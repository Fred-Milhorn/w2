//! # tacky
//!
//! Generate Tacky (TAC) from the AST created by parser.

use crate::parse::{
    Ast, BinaryOperator, Block, BlockItem, Const, Declaration, Expression, ForInit,
    FunctionDeclaration, Identifier, Parameters, Statement, Type, UnaryOperator,
    VariableDeclaration
};
use crate::utils::{mklabel, temp_name};
use crate::validate::{
    IdentAttrs, InitialValue, SYMBOLS, StaticInit, Symbol, add_symbol, get_symbol
};

use anyhow::{Result, bail};

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Constant(Const),
    Var(Identifier)
}
pub type Arguments = Vec<Val>;

pub const ZERO: Val = Val::Constant(Const::ConstInt(0));
pub const ONE: Val = Val::Constant(Const::ConstInt(1));

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    SignExtend(Val, Val),
    Truncate(Val, Val),
    Return(Val),
    Unary(UnaryOperator, Val, Val),
    Binary(BinaryOperator, Val, Val, Val),
    Copy(Val, Val),
    Jump(Identifier),
    JumpIfZero(Val, Identifier),
    JumpIfNotZero(Val, Identifier),
    Label(Identifier),
    FunCall(Identifier, Option<Arguments>, Val)
}
pub type Instructions = Vec<Instruction>;

#[derive(Debug, Clone, PartialEq)]
pub struct Function(pub Identifier, pub bool, pub Option<Parameters>, pub Option<Instructions>);

#[derive(Debug, Clone, PartialEq)]
pub struct StaticVariable(pub Identifier, pub bool, pub Type, pub StaticInit);

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    FunDef(Function),
    VarDef(StaticVariable)
}

type Definitions = Vec<Definition>;

#[derive(Debug, Clone, PartialEq)]
pub enum Tacky {
    Program(Definitions)
}

pub fn generate(ast: &Ast) -> Result<Tacky> {
    let Ast::Program(declarations) = ast;
    let mut definitions: Definitions = Vec::new();

    for declaration in declarations {
        if let Declaration::FunDecl(function_declaration) = declaration {
            definitions.push(Definition::FunDef(gen_function(function_declaration)?));
        }
    }

    let mut static_vars = convert_symbols_to_tacky();
    definitions.append(&mut static_vars);

    Ok(Tacky::Program(definitions))
}

pub fn convert_symbols_to_tacky() -> Definitions {
    let mut definitions: Definitions = Vec::new();

    SYMBOLS.with_borrow(|symbol_table| {
        for (name, entry) in symbol_table {
            if let IdentAttrs::Static(init, global) = &entry.attrs {
                match init {
                    InitialValue::Initial(initializer) => {
                        definitions.push(Definition::VarDef(StaticVariable(
                            name.to_string(),
                            *global,
                            entry.symbol_type.clone(),
                            initializer.clone()
                        )));
                    },
                    InitialValue::Tentative => {
                        let initializer = match entry.symbol_type {
                            Type::Int => StaticInit::IntInit(0),
                            Type::Long => StaticInit::LongInit(0),
                            _ => todo!()
                        };
                        definitions.push(Definition::VarDef(StaticVariable(
                            name.to_string(),
                            *global,
                            entry.symbol_type.clone(),
                            initializer
                        )));
                    },
                    InitialValue::NoInitializer => ()
                }
            }
        }
    });

    definitions
}

fn gen_function(declaration: &FunctionDeclaration) -> Result<Function> {
    let FunctionDeclaration(name, params, opt_body, _type, _storage_class) = declaration;

    let instructions = match opt_body {
        Some(block) => {
            let mut instructions: Instructions = Vec::new();
            emit_block(block, &mut instructions)?;

            // Patch functions without return and/or body
            if instructions.is_empty()
                || !matches!(instructions.last(), Some(Instruction::Return(_)))
            {
                instructions.push(Instruction::Return(ZERO));
            }
            Some(instructions)
        },
        None => None
    };

    let global = match get_symbol(name) {
        Some(entry) => {
            if let IdentAttrs::Function(_, global) = entry.attrs {
                global
            } else {
                bail!("gen_function: function has unexpected attributes in symbol table: {name:?}");
            }
        },
        _ => bail!("gen_function: function missing from symbol table: {name:?}")
    };

    Ok(Function(name.to_string(), global, params.clone(), instructions))
}

fn emit_block(block: &Block, instructions: &mut Instructions) -> Result<()> {
    for item in block {
        match item {
            BlockItem::S(statement) => {
                emit_statement(statement, instructions)?;
            },
            BlockItem::D(declaration) => {
                if let Declaration::VarDecl(VariableDeclaration(
                    identifier,
                    Some(expression),
                    _,
                    None
                )) = declaration
                {
                    let value = emit_tacky(expression, instructions)?;
                    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
                }
            }
        }
    }

    Ok(())
}

fn case_constant(expression: &Expression) -> Result<Const> {
    match expression {
        Expression::Constant(constant, _) => Ok(constant.clone()),
        Expression::Unary(UnaryOperator::Negate, inner, _) => match case_constant(inner)? {
            Const::ConstInt(value) => Ok(Const::ConstInt(-value)),
            Const::ConstLong(value) => Ok(Const::ConstLong(-value))
        },
        _ => bail!("switch case value is not a constant expression: {expression:?}")
    }
}

fn collect_switch_targets(
    statement: &Statement, cases: &mut Vec<(Const, Identifier)>, default: &mut Option<Identifier>
) -> Result<()> {
    match statement {
        Statement::Switch(_, _, _) => (),
        Statement::Case(expression, body, label) => {
            cases.push((case_constant(expression)?, label.clone()));
            collect_switch_targets(body, cases, default)?;
        },
        Statement::Default(body, label) => {
            *default = Some(label.clone());
            collect_switch_targets(body, cases, default)?;
        },
        Statement::If(_, then_branch, else_branch) => {
            collect_switch_targets(then_branch, cases, default)?;
            if let Some(else_statement) = else_branch {
                collect_switch_targets(else_statement, cases, default)?;
            }
        },
        Statement::Compound(block) => {
            for item in block {
                if let BlockItem::S(statement) = item {
                    collect_switch_targets(statement, cases, default)?;
                }
            }
        },
        Statement::Labeled(_, statement) => collect_switch_targets(statement, cases, default)?,
        Statement::While(_, statement, _) => collect_switch_targets(statement, cases, default)?,
        Statement::DoWhile(statement, _, _) => collect_switch_targets(statement, cases, default)?,
        Statement::For(_, _, _, statement, _) => collect_switch_targets(statement, cases, default)?,
        _ => ()
    }

    Ok(())
}

fn emit_statement(statement: &Statement, instructions: &mut Instructions) -> Result<()> {
    match statement {
        Statement::Return(expression) => {
            let value = emit_tacky(expression, instructions)?;
            instructions.push(Instruction::Return(value));
        },
        Statement::Expression(expression) => {
            let _ = emit_tacky(expression, instructions)?;
        },
        Statement::If(condition, then_branch, None) => {
            let result = emit_tacky(condition, instructions)?;
            let end_if = temp_name("end_if");
            instructions.push(Instruction::JumpIfZero(result, end_if.clone()));
            emit_statement(then_branch, instructions)?;
            instructions.push(Instruction::Label(end_if));
        },
        Statement::If(condition, then_branch, Some(else_branch)) => {
            let result = emit_tacky(condition, instructions)?;
            let else_label = temp_name("else_label");
            let end_if = temp_name("end_if");
            instructions.push(Instruction::JumpIfZero(result, else_label.clone()));
            emit_statement(then_branch, instructions)?;
            instructions.push(Instruction::Jump(end_if.clone()));
            instructions.push(Instruction::Label(else_label));
            emit_statement(else_branch, instructions)?;
            instructions.push(Instruction::Label(end_if));
        },
        Statement::Switch(condition, body, label) => {
            let condition_value = emit_tacky(condition, instructions)?;
            let break_label = mklabel("break", label);
            let mut cases: Vec<(Const, Identifier)> = Vec::new();
            let mut default_label: Option<Identifier> = None;
            collect_switch_targets(body, &mut cases, &mut default_label)?;

            for (case_constant, case_label) in cases {
                let result = make_tacky_variable("switch_case", &Type::Int);
                instructions.push(Instruction::Binary(
                    BinaryOperator::Equal,
                    condition_value.clone(),
                    Val::Constant(case_constant),
                    result.clone()
                ));
                instructions.push(Instruction::JumpIfNotZero(result, case_label));
            }

            match default_label {
                Some(default_target) => instructions.push(Instruction::Jump(default_target)),
                None => instructions.push(Instruction::Jump(break_label.clone()))
            }

            emit_statement(body, instructions)?;
            instructions.push(Instruction::Label(break_label));
        },
        Statement::Case(_, body, label) => {
            instructions.push(Instruction::Label(label.clone()));
            emit_statement(body, instructions)?;
        },
        Statement::Default(body, label) => {
            instructions.push(Instruction::Label(label.clone()));
            emit_statement(body, instructions)?;
        },
        Statement::Compound(block) => {
            emit_block(block, instructions)?;
        },
        Statement::Goto(target) => {
            instructions.push(Instruction::Jump(target.clone()));
        },
        Statement::Labeled(label, statement) => {
            instructions.push(Instruction::Label(label.clone()));
            emit_statement(statement, instructions)?;
        },
        Statement::Break(label) => {
            instructions.push(Instruction::Jump(mklabel("break", label)));
        },
        Statement::Continue(label) => {
            instructions.push(Instruction::Jump(mklabel("continue", label)));
        },
        Statement::DoWhile(body, condition, label) => {
            let continue_label = mklabel("continue", label);
            let break_label = mklabel("break", label);
            instructions.push(Instruction::Label(label.clone()));
            emit_statement(body, instructions)?;
            instructions.push(Instruction::Label(continue_label));
            let cond_val = emit_tacky(condition, instructions)?;
            instructions.push(Instruction::JumpIfNotZero(cond_val, label.clone()));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::While(condition, body, label) => {
            let continue_label = mklabel("continue", label);
            let break_label = mklabel("break", label);
            instructions.push(Instruction::Label(continue_label.clone()));
            let cond_val = emit_tacky(condition, instructions)?;
            instructions.push(Instruction::JumpIfZero(cond_val, break_label.clone()));
            emit_statement(body, instructions)?;
            instructions.push(Instruction::Jump(continue_label));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::For(for_init, condition, post, body, label) => {
            let continue_label = mklabel("continue", label);
            let break_label = mklabel("break", label);
            match for_init {
                ForInit::InitDecl(VariableDeclaration(identifier, Some(expression), _, _)) => {
                    let value = emit_tacky(expression, instructions)?;
                    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
                },
                ForInit::InitExp(Some(expression)) => {
                    let _ = emit_tacky(expression, instructions)?;
                },
                _ => ()
            }
            instructions.push(Instruction::Label(label.clone()));
            if let Some(for_condition) = condition {
                let cond_val = emit_tacky(for_condition, instructions)?;
                instructions.push(Instruction::JumpIfZero(cond_val, break_label.clone()));
            }
            emit_statement(body, instructions)?;
            instructions.push(Instruction::Label(continue_label.clone()));
            if let Some(for_post) = post {
                let _ = emit_tacky(for_post, instructions)?;
            }
            instructions.push(Instruction::Jump(label.clone()));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::None => ()
    }

    Ok(())
}

fn make_tacky_variable(prefix: &str, var_type: &Type) -> Val {
    let var_name = temp_name(prefix);
    add_symbol(&var_name, Symbol { symbol_type: var_type.clone(), attrs: IdentAttrs::Local });
    Val::Var(var_name)
}

fn one_for_type(var_type: &Type) -> Result<Val> {
    let one = match var_type {
        Type::Int => Val::Constant(Const::ConstInt(1)),
        Type::Long => Val::Constant(Const::ConstLong(1)),
        _ => bail!("Unsupported type for increment/decrement: {var_type:?}")
    };

    Ok(one)
}

fn emit_tacky(expression: &Expression, instructions: &mut Instructions) -> Result<Val> {
    let value = match expression {
        Expression::Cast(target_type, expression, _exp_type) => {
            let result = emit_tacky(expression, instructions)?;
            if *target_type == expression.get_type() {
                result
            } else {
                let dst = make_tacky_variable("cast", target_type);
                if *target_type == Type::Long {
                    instructions.push(Instruction::SignExtend(result, dst.clone()));
                } else {
                    instructions.push(Instruction::Truncate(result, dst.clone()));
                }
                dst
            }
        },
        Expression::FunctionCall(identifier, args, return_type) => {
            let args_exps = match args {
                Some(arguments) => {
                    let mut values = Vec::new();

                    for argument in arguments {
                        let exp_type = argument.get_type();
                        let res = emit_tacky(argument, instructions)?;
                        let val = make_tacky_variable("arg", &exp_type);
                        instructions.push(Instruction::Copy(res, val.clone()));
                        values.push(val);
                    }
                    Some(values)
                },
                None => None
            };
            let result = make_tacky_variable("result", return_type);
            instructions.push(Instruction::FunCall(
                identifier.to_string(),
                args_exps,
                result.clone()
            ));
            result
        },
        Expression::Conditional(condition, then_branch, else_branch, cond_type) => {
            let cond_val = emit_tacky(condition, instructions)?;
            let else_label = temp_name("else_label");
            let end_if = temp_name("end_if");
            let result = make_tacky_variable("cond_result", cond_type);
            instructions.push(Instruction::JumpIfZero(cond_val, else_label.clone()));
            let then_val = emit_tacky(then_branch, instructions)?;
            instructions.push(Instruction::Copy(then_val, result.clone()));
            instructions.push(Instruction::Jump(end_if.clone()));
            instructions.push(Instruction::Label(else_label));
            let else_val = emit_tacky(else_branch, instructions)?;
            instructions.push(Instruction::Copy(else_val, result.clone()));
            instructions.push(Instruction::Label(end_if));
            result
        },
        Expression::Constant(number, _type) => Val::Constant(number.clone()),
        Expression::Var(identifier, _type) => Val::Var(identifier.clone()),
        Expression::Unary(op, inner, unary_type) => {
            let src = emit_tacky(inner, instructions)?;
            let dst = make_tacky_variable("unary_op", unary_type);
            instructions.push(Instruction::Unary(op.clone(), src, dst.clone()));
            dst
        },
        Expression::PrefixIncrement(inner, inc_type) => {
            let lvalue = emit_tacky(inner, instructions)?;
            let one = one_for_type(inc_type)?;
            let result = make_tacky_variable("pre_incr", inc_type);
            instructions.push(Instruction::Binary(
                BinaryOperator::Plus,
                lvalue.clone(),
                one,
                result.clone()
            ));
            instructions.push(Instruction::Copy(result.clone(), lvalue));
            result
        },
        Expression::PrefixDecrement(inner, dec_type) => {
            let lvalue = emit_tacky(inner, instructions)?;
            let one = one_for_type(dec_type)?;
            let result = make_tacky_variable("pre_decr", dec_type);
            instructions.push(Instruction::Binary(
                BinaryOperator::Minus,
                lvalue.clone(),
                one,
                result.clone()
            ));
            instructions.push(Instruction::Copy(result.clone(), lvalue));
            result
        },
        Expression::PostfixIncrement(inner, inc_type) => {
            let lvalue = emit_tacky(inner, instructions)?;
            let old_value = make_tacky_variable("post_incr_old", inc_type);
            instructions.push(Instruction::Copy(lvalue.clone(), old_value.clone()));
            let one = one_for_type(inc_type)?;
            let result = make_tacky_variable("post_incr_new", inc_type);
            instructions.push(Instruction::Binary(
                BinaryOperator::Plus,
                lvalue.clone(),
                one,
                result.clone()
            ));
            instructions.push(Instruction::Copy(result, lvalue));
            old_value
        },
        Expression::PostfixDecrement(inner, dec_type) => {
            let lvalue = emit_tacky(inner, instructions)?;
            let old_value = make_tacky_variable("post_decr_old", dec_type);
            instructions.push(Instruction::Copy(lvalue.clone(), old_value.clone()));
            let one = one_for_type(dec_type)?;
            let result = make_tacky_variable("post_decr_new", dec_type);
            instructions.push(Instruction::Binary(
                BinaryOperator::Minus,
                lvalue.clone(),
                one,
                result.clone()
            ));
            instructions.push(Instruction::Copy(result, lvalue));
            old_value
        },
        Expression::Binary(BinaryOperator::And, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions)?;
            let false_label = temp_name("and_false");
            let end_label = temp_name("and_end");
            let result = make_tacky_variable("and_result", bin_type);
            instructions.push(Instruction::JumpIfZero(val1, false_label.clone()));
            let val2 = emit_tacky(dst, instructions)?;
            instructions.push(Instruction::JumpIfZero(val2, false_label.clone()));
            instructions.push(Instruction::Copy(ONE, result.clone()));
            instructions.push(Instruction::Jump(end_label.clone()));
            instructions.push(Instruction::Label(false_label.clone()));
            instructions.push(Instruction::Copy(ZERO, result.clone()));
            instructions.push(Instruction::Label(end_label.clone()));
            result
        },
        Expression::Binary(BinaryOperator::Or, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions)?;
            let true_label = temp_name("or_true");
            let end_label = temp_name("or_end");
            let result = make_tacky_variable("or_result", bin_type);
            instructions.push(Instruction::JumpIfNotZero(val1, true_label.clone()));
            let val2 = emit_tacky(dst, instructions)?;
            instructions.push(Instruction::JumpIfNotZero(val2, true_label.clone()));
            instructions.push(Instruction::Copy(ZERO, result.clone()));
            instructions.push(Instruction::Jump(end_label.clone()));
            instructions.push(Instruction::Label(true_label.clone()));
            instructions.push(Instruction::Copy(ONE, result.clone()));
            instructions.push(Instruction::Label(end_label.clone()));
            result
        },
        Expression::Binary(op, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions)?;
            let val2 = emit_tacky(dst, instructions)?;
            let dst = make_tacky_variable("bin", bin_type);
            instructions.push(Instruction::Binary(op.clone(), val1, val2, dst.clone()));
            dst
        },
        Expression::Assignment(lhs, rhs, _type) => {
            let lvalue = emit_tacky(lhs, instructions)?;
            let result = emit_tacky(rhs, instructions)?;
            instructions.push(Instruction::Copy(result, lvalue.clone()));
            lvalue
        },
        Expression::CompoundAssignment(operator, lhs, rhs, comp_type) => {
            let lvalue = emit_tacky(lhs, instructions)?;
            let result = emit_tacky(
                &Expression::Binary(operator.clone(), lhs.clone(), rhs.clone(), comp_type.clone()),
                instructions
            )?;
            instructions.push(Instruction::Copy(result, lvalue.clone()));
            lvalue
        }
    };

    Ok(value)
}
