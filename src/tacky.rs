//! # tacky
//!
//! Generate Tacky (TAC) from the AST created by parser.

use crate::parse::{
    Ast, BinaryOperator, Block, BlockItem, Const, Declaration, Expression, ForInit,
    FunctionDeclaration, Identifier, Parameters, Statement, Type, UnaryOperator,
    VariableDeclaration
};
use crate::utils::{mklabel, temp_name};
use crate::validate::{IdentAttrs, InitialValue, StaticInit, Symbol, SymbolTable};

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

pub fn generate(ast: &Ast, symbol_table: &mut SymbolTable) -> Result<Tacky> {
    let Ast::Program(declarations) = ast;
    let mut definitions: Definitions = Vec::new();

    for declaration in declarations {
        if let Declaration::FunDecl(function_declaration) = declaration {
            definitions.push(Definition::FunDef(gen_function(function_declaration, symbol_table)?));
        }
    }

    let mut static_vars = convert_symbols_to_tacky(symbol_table);
    definitions.append(&mut static_vars);

    Ok(Tacky::Program(definitions))
}

pub fn convert_symbols_to_tacky(symbol_table: &SymbolTable) -> Definitions {
    let mut definitions: Definitions = Vec::new();

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

    definitions
}

fn gen_function(
    declaration: &FunctionDeclaration, symbol_table: &mut SymbolTable
) -> Result<Function> {
    let FunctionDeclaration(name, params, opt_body, _type, _storage_class) = declaration;

    let instructions = match opt_body {
        Some(block) => {
            let mut instructions: Instructions = Vec::new();
            emit_block(block, &mut instructions, symbol_table)?;

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

    let global = match symbol_table.get(name) {
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

fn emit_block(
    block: &Block, instructions: &mut Instructions, symbol_table: &mut SymbolTable
) -> Result<()> {
    for item in block {
        match item {
            BlockItem::S(statement) => {
                emit_statement(statement, instructions, symbol_table)?;
            },
            BlockItem::D(declaration) => {
                if let Declaration::VarDecl(VariableDeclaration(
                    identifier,
                    Some(expression),
                    _,
                    None
                )) = declaration
                {
                    let value = emit_tacky(expression, instructions, symbol_table)?;
                    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
                }
            }
        }
    }

    Ok(())
}

fn emit_statement(
    statement: &Statement, instructions: &mut Instructions, symbol_table: &mut SymbolTable
) -> Result<()> {
    match statement {
        Statement::Return(expression) => {
            let value = emit_tacky(expression, instructions, symbol_table)?;
            instructions.push(Instruction::Return(value));
        },
        Statement::Expression(expression) => {
            let _ = emit_tacky(expression, instructions, symbol_table)?;
        },
        Statement::If(condition, then_branch, None) => {
            let result = emit_tacky(condition, instructions, symbol_table)?;
            let end_if = temp_name("end_if");
            instructions.push(Instruction::JumpIfZero(result, end_if.clone()));
            emit_statement(then_branch, instructions, symbol_table)?;
            instructions.push(Instruction::Label(end_if));
        },
        Statement::If(condition, then_branch, Some(else_branch)) => {
            let result = emit_tacky(condition, instructions, symbol_table)?;
            let else_label = temp_name("else_label");
            let end_if = temp_name("end_if");
            instructions.push(Instruction::JumpIfZero(result, else_label.clone()));
            emit_statement(then_branch, instructions, symbol_table)?;
            instructions.push(Instruction::Jump(end_if.clone()));
            instructions.push(Instruction::Label(else_label));
            emit_statement(else_branch, instructions, symbol_table)?;
            instructions.push(Instruction::Label(end_if));
        },
        Statement::Compound(block) => {
            emit_block(block, instructions, symbol_table)?;
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
            emit_statement(body, instructions, symbol_table)?;
            instructions.push(Instruction::Label(continue_label));
            let cond_val = emit_tacky(condition, instructions, symbol_table)?;
            instructions.push(Instruction::JumpIfNotZero(cond_val, label.clone()));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::While(condition, body, label) => {
            let continue_label = mklabel("continue", label);
            let break_label = mklabel("break", label);
            instructions.push(Instruction::Label(continue_label.clone()));
            let cond_val = emit_tacky(condition, instructions, symbol_table)?;
            instructions.push(Instruction::JumpIfZero(cond_val, break_label.clone()));
            emit_statement(body, instructions, symbol_table)?;
            instructions.push(Instruction::Jump(continue_label));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::For(for_init, condition, post, body, label) => {
            let continue_label = mklabel("continue", label);
            let break_label = mklabel("break", label);
            match for_init {
                ForInit::InitDecl(VariableDeclaration(identifier, Some(expression), _, _)) => {
                    let value = emit_tacky(expression, instructions, symbol_table)?;
                    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
                },
                ForInit::InitExp(Some(expression)) => {
                    let _ = emit_tacky(expression, instructions, symbol_table)?;
                },
                _ => ()
            }
            instructions.push(Instruction::Label(label.clone()));
            if let Some(for_condition) = condition {
                let cond_val = emit_tacky(for_condition, instructions, symbol_table)?;
                instructions.push(Instruction::JumpIfZero(cond_val, break_label.clone()));
            }
            emit_statement(body, instructions, symbol_table)?;
            instructions.push(Instruction::Label(continue_label.clone()));
            if let Some(for_post) = post {
                let _ = emit_tacky(for_post, instructions, symbol_table)?;
            }
            instructions.push(Instruction::Jump(label.clone()));
            instructions.push(Instruction::Label(break_label));
        },
        Statement::None => ()
    }

    Ok(())
}

fn make_tacky_variable(prefix: &str, var_type: &Type, symbol_table: &mut SymbolTable) -> Val {
    let var_name = temp_name(prefix);
    symbol_table
        .add(&var_name, Symbol { symbol_type: var_type.clone(), attrs: IdentAttrs::Local });
    Val::Var(var_name)
}

fn emit_tacky(
    expression: &Expression, instructions: &mut Instructions, symbol_table: &mut SymbolTable
) -> Result<Val> {
    let value = match expression {
        Expression::Cast(target_type, expression, _exp_type) => {
            let result = emit_tacky(expression, instructions, symbol_table)?;
            if *target_type == expression.get_type() {
                result
            } else {
                let dst = make_tacky_variable("cast", target_type, symbol_table);
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
                        let res = emit_tacky(argument, instructions, symbol_table)?;
                        let val = make_tacky_variable("arg", &exp_type, symbol_table);
                        instructions.push(Instruction::Copy(res, val.clone()));
                        values.push(val);
                    }
                    Some(values)
                },
                None => None
            };
            let result = make_tacky_variable("result", return_type, symbol_table);
            instructions.push(Instruction::FunCall(
                identifier.to_string(),
                args_exps,
                result.clone()
            ));
            result
        },
        Expression::Conditional(condition, then_branch, else_branch, cond_type) => {
            let cond_val = emit_tacky(condition, instructions, symbol_table)?;
            let else_label = temp_name("else_label");
            let end_if = temp_name("end_if");
            let result = make_tacky_variable("cond_result", cond_type, symbol_table);
            instructions.push(Instruction::JumpIfZero(cond_val, else_label.clone()));
            let then_val = emit_tacky(then_branch, instructions, symbol_table)?;
            instructions.push(Instruction::Copy(then_val, result.clone()));
            instructions.push(Instruction::Jump(end_if.clone()));
            instructions.push(Instruction::Label(else_label));
            let else_val = emit_tacky(else_branch, instructions, symbol_table)?;
            instructions.push(Instruction::Copy(else_val, result.clone()));
            instructions.push(Instruction::Label(end_if));
            result
        },
        Expression::Constant(number, _type) => Val::Constant(number.clone()),
        Expression::Var(identifier, _type) => Val::Var(identifier.clone()),
        Expression::Unary(op, inner, unary_type) => {
            let src = emit_tacky(inner, instructions, symbol_table)?;
            let dst = make_tacky_variable("unary_op", unary_type, symbol_table);
            instructions.push(Instruction::Unary(op.clone(), src, dst.clone()));
            dst
        },
        Expression::Binary(BinaryOperator::And, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions, symbol_table)?;
            let false_label = temp_name("and_false");
            let end_label = temp_name("and_end");
            let result = make_tacky_variable("and_result", bin_type, symbol_table);
            instructions.push(Instruction::JumpIfZero(val1, false_label.clone()));
            let val2 = emit_tacky(dst, instructions, symbol_table)?;
            instructions.push(Instruction::JumpIfZero(val2, false_label.clone()));
            instructions.push(Instruction::Copy(ONE, result.clone()));
            instructions.push(Instruction::Jump(end_label.clone()));
            instructions.push(Instruction::Label(false_label.clone()));
            instructions.push(Instruction::Copy(ZERO, result.clone()));
            instructions.push(Instruction::Label(end_label.clone()));
            result
        },
        Expression::Binary(BinaryOperator::Or, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions, symbol_table)?;
            let true_label = temp_name("or_true");
            let end_label = temp_name("or_end");
            let result = make_tacky_variable("or_result", bin_type, symbol_table);
            instructions.push(Instruction::JumpIfNotZero(val1, true_label.clone()));
            let val2 = emit_tacky(dst, instructions, symbol_table)?;
            instructions.push(Instruction::JumpIfNotZero(val2, true_label.clone()));
            instructions.push(Instruction::Copy(ZERO, result.clone()));
            instructions.push(Instruction::Jump(end_label.clone()));
            instructions.push(Instruction::Label(true_label.clone()));
            instructions.push(Instruction::Copy(ONE, result.clone()));
            instructions.push(Instruction::Label(end_label.clone()));
            result
        },
        Expression::Binary(op, src, dst, bin_type) => {
            let val1 = emit_tacky(src, instructions, symbol_table)?;
            let val2 = emit_tacky(dst, instructions, symbol_table)?;
            let dst = make_tacky_variable("bin", bin_type, symbol_table);
            instructions.push(Instruction::Binary(op.clone(), val1, val2, dst.clone()));
            dst
        },
        Expression::Assignment(lhs, rhs, _type) => {
            let lvalue = emit_tacky(lhs, instructions, symbol_table)?;
            let result = emit_tacky(rhs, instructions, symbol_table)?;
            instructions.push(Instruction::Copy(result, lvalue.clone()));
            lvalue
        },
        Expression::CompoundAssignment(operator, lhs, rhs, comp_type) => {
            let lvalue = emit_tacky(lhs, instructions, symbol_table)?;
            let result = emit_tacky(
                &Expression::Binary(operator.clone(), lhs.clone(), rhs.clone(), comp_type.clone()),
                instructions,
                symbol_table
            )?;
            instructions.push(Instruction::Copy(result, lvalue.clone()));
            lvalue
        }
    };

    Ok(value)
}
