//! # tacky
//!
//! Generate Tacky (TAC) from the AST created by parser.

use crate::parse;
use crate::utils::{temp_name, mklabel};

use anyhow::Result;

pub type Identifier = String;
pub type Instructions = Vec<Instruction>;

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Constant(i32),
    Var(Identifier),
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    Not,
    Negate,
    Complement,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Leftshift,
    Rightshift,
    BitAnd,
    BitXor,
    BitOr,
    Equal,
    NotEqual,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Return(Val),
    Unary(UnaryOperator, Val, Val),
    Binary(BinaryOperator, Val, Val, Val),
    Copy(Val, Val),
    Jump(Identifier),
    JumpIfZero(Val, Identifier),
    JumpIfNotZero(Val, Identifier),
    Label(Identifier),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function(pub Identifier, pub Instructions);

#[derive(Debug, Clone, PartialEq)]
pub enum Tacky {
    Program(Function),
}

pub fn generate(ast: parse::Ast) -> Result<Tacky> {
    let tacky = match ast {
	parse::Ast::Program(function_definition) => Tacky::Program(gen_function(&function_definition)?),
    };

    Ok(tacky)
}

fn gen_function(function: &parse::Function) -> Result<Function> {
    let parse::Function(name, body) = function;
    let mut instructions = gen_statement(body)?;

    // Patch functions without return
    instructions.push(Instruction::Return(Val::Constant(0)));
    
    Ok(Function(name.to_string(), instructions))
}

fn gen_statement(body: &parse::Block) -> Result<Instructions> {
    let mut instructions: Instructions = Vec::new();

    emit_block(body, &mut instructions)?;
    
    Ok(instructions)
}

fn emit_block(block: &parse::Block, instructions: &mut Instructions) -> Result<()> {
    for item in block.iter() {
	match item {
	    parse::BlockItem::S(statement) => {
		emit_statement(statement, instructions)?;
	    },
	    parse::BlockItem::D(declaration) => {
		if let parse::Declaration(identifier, Some(expression)) = declaration {
		    let value = emit_tacky(expression, instructions)?;
		    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
		}
	    },
	}
    }

    Ok(())
}

fn emit_statement(statement: &parse::Statement, instructions: &mut Instructions) -> Result<()> {
    match statement {
	parse::Statement::Return(expression) => {
	    let value = emit_tacky(expression, instructions)?;
	    instructions.push(Instruction::Return(value));
	},
	parse::Statement::Expression(expression) => {
	    let _ = emit_tacky(expression, instructions)?;
	},
	parse::Statement::If(condition, then_branch, None) => {
	    let result = emit_tacky(condition, instructions)?;
	    let end_if = temp_name("end_if");
	    instructions.push(Instruction::JumpIfZero(result, end_if.clone()));
	    emit_statement(then_branch, instructions)?;
	    instructions.push(Instruction::Label(end_if));
	},
	parse::Statement::If(condition, then_branch, Some(else_branch)) => {
	    let result = emit_tacky(condition, instructions)?;
	    let else_label = temp_name("else_label");
	    let end_if     = temp_name("end_if");
	    instructions.push(Instruction::JumpIfZero(result, else_label.clone()));
	    emit_statement(then_branch, instructions)?;
	    instructions.push(Instruction::Jump(end_if.clone()));
	    instructions.push(Instruction::Label(else_label));
	    emit_statement(else_branch, instructions)?;
	    instructions.push(Instruction::Label(end_if));
	},
	parse::Statement::Compound(block) => {
	    emit_block(block, instructions)?;
	},
	parse::Statement::Break(label) => {
	    instructions.push(Instruction::Jump(mklabel("break", label)));
	},
	parse::Statement::Continue(label) => {
	    instructions.push(Instruction::Jump(mklabel("continue", label)));
	},
	parse::Statement::DoWhile(body, condition, label) => {
	    let continue_label = mklabel("continue", label);
	    let break_label    = mklabel("break", label);
	    instructions.push(Instruction::Label(label.clone()));
	    emit_statement(body, instructions)?;
	    instructions.push(Instruction::Label(continue_label));
	    let cond_val = emit_tacky(condition, instructions)?;
	    instructions.push(Instruction::JumpIfNotZero(cond_val, label.clone()));
	    instructions.push(Instruction::Label(break_label));
	},
	parse::Statement::While(condition, body, label) => {
	    let continue_label = mklabel("continue", label);
	    let break_label    = mklabel("break", label);
	    instructions.push(Instruction::Label(continue_label.clone()));
	    let cond_val = emit_tacky(condition, instructions)?;
	    instructions.push(Instruction::JumpIfZero(cond_val, break_label.clone()));
	    emit_statement(body, instructions)?;
	    instructions.push(Instruction::Jump(continue_label));
	    instructions.push(Instruction::Label(break_label));
	},
	parse::Statement::For(for_init, condition, post, body, label) => {
	    let continue_label = mklabel("continue", label);
	    let break_label    = mklabel("break", label);
	    match for_init {
		parse::ForInit::InitDecl(parse::Declaration(identifier, Some(expression))) => {
		    let value = emit_tacky(expression, instructions)?;
		    instructions.push(Instruction::Copy(value, Val::Var(identifier.clone())));
		},
		parse::ForInit::InitExp(Some(expression)) => {
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
	parse::Statement::Null => (),
    }

    Ok(())
}

fn emit_tacky(expression: &parse::Expression, instructions: &mut Instructions) -> Result<Val> {
    let value = match expression {
	parse::Expression::Conditional(condition, then_branch, else_branch) => {
	    let cond_val = emit_tacky(condition, instructions)?;
	    let else_label = temp_name("else_label");
	    let end_if     = temp_name("end_if");
	    let result     = Val::Var(temp_name("cond_result"));
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
	parse::Expression::Constant(number) => Val::Constant(*number),
	parse::Expression::Var(identifier)  => Val::Var(identifier.clone()),
	parse::Expression::Unary(parse::UnaryOperator::PreIncrement, rhs) => {
	    emit_tacky(&parse::Expression::CompoundAssignment(parse::BinaryOperator::Plus,
							      rhs.clone(),
							      Box::new(parse::Expression::Constant(1))),
		       instructions)?
	},
	parse::Expression::Unary(parse::UnaryOperator::PreDecrement, rhs) => {
	    emit_tacky(&parse::Expression::CompoundAssignment(parse::BinaryOperator::Minus,
							      rhs.clone(),
							      Box::new(parse::Expression::Constant(1))),
		       instructions)?
	},
	parse::Expression::Unary(parse::UnaryOperator::PostIncrement, lhs) => {
	    let val = emit_tacky(lhs, instructions)?;
	    let result = Val::Var(temp_name("tmp"));
	    instructions.push(Instruction::Copy(val, result.clone()));
	    emit_tacky(&parse::Expression::CompoundAssignment(parse::BinaryOperator::Plus,
							      lhs.clone(),
							      Box::new(parse::Expression::Constant(1))),
		       instructions)?;
	    result
	},
	parse::Expression::Unary(parse::UnaryOperator::PostDecrement, lhs) => {
	    let val = emit_tacky(lhs, instructions)?;
	    let result = Val::Var(temp_name("tmp"));
	    instructions.push(Instruction::Copy(val, result.clone()));
	    emit_tacky(&parse::Expression::CompoundAssignment(parse::BinaryOperator::Minus,
							      lhs.clone(),
							      Box::new(parse::Expression::Constant(1))),
		       instructions)?;
	    result
	    
	},
	parse::Expression::Unary(op, inner) => {
	    let src = emit_tacky(inner, instructions)?;
	    let dst = Val::Var(temp_name("tmp"));
	    let tacky_op = match op {
		parse::UnaryOperator::Complement => UnaryOperator::Complement,
		parse::UnaryOperator::Negate     => UnaryOperator::Negate,
		parse::UnaryOperator::Not        => UnaryOperator::Not,
		_                                => todo!()
	    };
	    instructions.push(Instruction::Unary(tacky_op, src, dst.clone()));
	    dst
	},
	parse::Expression::Binary(parse::BinaryOperator::And, src, dst) => {
	    let val1        = emit_tacky(src, instructions)?;
	    let false_label = temp_name("and_false");
	    let end_label   = temp_name("and_end");
	    let result      = Val::Var(temp_name("and_result"));
	    instructions.push(Instruction::JumpIfZero(val1, false_label.clone()));
	    let val2        = emit_tacky(dst, instructions)?;
	    instructions.push(Instruction::JumpIfZero(val2, false_label.clone()));
	    instructions.push(Instruction::Copy(Val::Constant(1), result.clone()));
	    instructions.push(Instruction::Jump(end_label.clone()));
	    instructions.push(Instruction::Label(false_label.clone()));
	    instructions.push(Instruction::Copy(Val::Constant(0), result.clone()));
	    instructions.push(Instruction::Label(end_label.clone()));
	    result    
	},
	parse::Expression::Binary(parse::BinaryOperator::Or, src, dst) => {
	    let val1        = emit_tacky(src, instructions)?;
	    let true_label = temp_name("or_true");
	    let end_label   = temp_name("or_end");
	    let result      = Val::Var(temp_name("or_result"));
	    instructions.push(Instruction::JumpIfNotZero(val1, true_label.clone()));
	    let val2        = emit_tacky(dst, instructions)?;
	    instructions.push(Instruction::JumpIfNotZero(val2, true_label.clone()));
	    instructions.push(Instruction::Copy(Val::Constant(0), result.clone()));
	    instructions.push(Instruction::Jump(end_label.clone()));
	    instructions.push(Instruction::Label(true_label.clone()));
	    instructions.push(Instruction::Copy(Val::Constant(1), result.clone()));
	    instructions.push(Instruction::Label(end_label.clone()));
	    result    
	},
	parse::Expression::Binary(op, src, dst) => {
	    let val1 = emit_tacky(src, instructions)?;
	    let val2 = emit_tacky(dst, instructions)?;
	    let dst  = Val::Var(temp_name("tmp"));
	    let tacky_op = match op {
		parse::BinaryOperator::Plus           => BinaryOperator::Add,
		parse::BinaryOperator::Minus          => BinaryOperator::Subtract,
		parse::BinaryOperator::Multiply       => BinaryOperator::Multiply,
		parse::BinaryOperator::Divide         => BinaryOperator::Divide,
		parse::BinaryOperator::Remainder      => BinaryOperator::Remainder,
		parse::BinaryOperator::Leftshift      => BinaryOperator::Leftshift,
		parse::BinaryOperator::Rightshift     => BinaryOperator::Rightshift,
		parse::BinaryOperator::BitAnd         => BinaryOperator::BitAnd,
		parse::BinaryOperator::BitXor         => BinaryOperator::BitXor,
		parse::BinaryOperator::BitOr          => BinaryOperator::BitOr,
		parse::BinaryOperator::Equal          => BinaryOperator::Equal,
		parse::BinaryOperator::NotEqual       => BinaryOperator::NotEqual,
		parse::BinaryOperator::LessThan       => BinaryOperator::LessThan,
		parse::BinaryOperator::LessOrEqual    => BinaryOperator::LessOrEqual,
		parse::BinaryOperator::GreaterThan    => BinaryOperator::GreaterThan,
		parse::BinaryOperator::GreaterOrEqual => BinaryOperator::GreaterOrEqual,
		_ => todo!()
	    };
	    instructions.push(Instruction::Binary(tacky_op, val1, val2, dst.clone()));
	    dst
	},
	parse::Expression::Assignment(lhs, rhs) => {
	    let lvalue = emit_tacky(lhs, instructions)?;
	    let result = emit_tacky(rhs, instructions)?;
	    instructions.push(Instruction::Copy(result, lvalue.clone()));
	    lvalue
	},
	parse::Expression::CompoundAssignment(operator, lhs, rhs) => {
	    let lvalue = emit_tacky(lhs, instructions)?;
	    let result = emit_tacky(&parse::Expression::Binary(operator.clone(), lhs.clone(), rhs.clone()), instructions)?;
	    instructions.push(Instruction::Copy(result, lvalue.clone()));
	    lvalue
	},
    };

    Ok(value)
}
