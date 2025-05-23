//! # code
//!
//! Generate x86-64 assembly language from the AST created by parser.

use crate::tacky;
use anyhow::Result;
use std::collections::HashMap;
use std::fmt::Write as _;

pub type Identifier = String;
pub type Instructions = Vec<Instruction>;

#[derive(Debug, Clone, PartialEq)]
pub enum Register {
    AX,
    CL,
    DX,
    R10,
    R11,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Imm(i32),
    Reg(Register),
    Pseudo(Identifier),
    Stack(i32),
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOperator {
    Add,
    Sub,
    Mult,
    Leftshift,
    Rightshift,
    BitAnd,
    BitXor,
    BitOr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConditionCode {
    E,
    NE,
    G,
    GE,
    L,
    LE,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Mov(Operand, Operand),
    Unary(UnaryOperator, Operand),
    Binary(BinaryOperator, Operand, Operand),
    Cmp(Operand, Operand),
    Idiv(Operand),
    Cdq,
    Jmp(Identifier),
    JmpCC(ConditionCode, Identifier),
    SetCC(ConditionCode, Operand),
    Label(Identifier),
    AllocateStack(i32),
    Ret,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function(Identifier, Instructions);

#[derive(Debug, Clone, PartialEq)]
pub enum Assembly {
    Program(Function),
}

pub fn generate(ast: &tacky::Tacky) -> Assembly {
    let tacky::Tacky::Program(function_definition) = ast;
    let tacky::Function(name, instructions) = function_definition;

    // Turn Tacky instructions in to assembly instructions
    let mut assembly = gen_assembly(instructions);

    // Turn Pseudo(tmp.%d) place holders into Stack(offsets)
    // Add AllocateStack instruction as well.
    assembly = fixup_pseudo(assembly);

    // Fix up invalid instructions that have addresses in src and dst
    assembly = fixup_invalid(assembly);

    Assembly::Program(Function(name.to_string(), assembly))
}

impl tacky::UnaryOperator {
    fn convert(&self) -> UnaryOperator {
        match self {
            tacky::UnaryOperator::Complement => UnaryOperator::Not,
            tacky::UnaryOperator::Negate => UnaryOperator::Neg,
            tacky::UnaryOperator::Not => UnaryOperator::Not,
        }
    }
}

impl tacky::BinaryOperator {
    fn convert(&self) -> BinaryOperator {
        match self {
            tacky::BinaryOperator::Add => BinaryOperator::Add,
            tacky::BinaryOperator::Subtract => BinaryOperator::Sub,
            tacky::BinaryOperator::Multiply => BinaryOperator::Mult,
            tacky::BinaryOperator::Rightshift => BinaryOperator::Rightshift,
            tacky::BinaryOperator::Leftshift => BinaryOperator::Leftshift,
            tacky::BinaryOperator::BitAnd => BinaryOperator::BitAnd,
            tacky::BinaryOperator::BitXor => BinaryOperator::BitXor,
            tacky::BinaryOperator::BitOr => BinaryOperator::BitOr,
            _ => todo!(),
        }
    }
}

impl tacky::Val {
    fn convert(&self) -> Operand {
        match self {
            tacky::Val::Constant(number) => Operand::Imm(*number),
            tacky::Val::Var(identifier) => Operand::Pseudo(identifier.to_string()),
        }
    }
}

fn gen_assembly(body: &tacky::Instructions) -> Instructions {
    let mut instructions: Instructions = Vec::new();

    for instruction in body.iter() {
        match instruction {
            tacky::Instruction::Return(val) => {
                instructions.push(Instruction::Mov(val.convert(), Operand::Reg(Register::AX)));
                instructions.push(Instruction::Ret);
            }
            tacky::Instruction::Unary(tacky::UnaryOperator::Not, src, dst) => {
                instructions.push(Instruction::Cmp(Operand::Imm(0), src.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::E, dst.convert()));
            }
            tacky::Instruction::Unary(operator, src, dst) => {
                instructions.push(Instruction::Mov(src.convert(), dst.convert()));
                instructions.push(Instruction::Unary(operator.convert(), dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::Divide, src1, src2, dst) => {
                instructions.push(Instruction::Mov(src1.convert(), Operand::Reg(Register::AX)));
                instructions.push(Instruction::Cdq);
                instructions.push(Instruction::Idiv(src2.convert()));
                instructions.push(Instruction::Mov(Operand::Reg(Register::AX), dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::Remainder, src1, src2, dst) => {
                instructions.push(Instruction::Mov(src1.convert(), Operand::Reg(Register::AX)));
                instructions.push(Instruction::Cdq);
                instructions.push(Instruction::Idiv(src2.convert()));
                instructions.push(Instruction::Mov(Operand::Reg(Register::DX), dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::Equal, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::E, dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::NotEqual, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::NE, dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::LessThan, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::L, dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::LessOrEqual, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::LE, dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::GreaterThan, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::G, dst.convert()));
            }
            tacky::Instruction::Binary(tacky::BinaryOperator::GreaterOrEqual, src1, src2, dst) => {
                instructions.push(Instruction::Cmp(src2.convert(), src1.convert()));
                instructions.push(Instruction::Mov(Operand::Imm(0), dst.convert()));
                instructions.push(Instruction::SetCC(ConditionCode::GE, dst.convert()));
            }
            tacky::Instruction::Binary(operator, src1, src2, dst) => {
                instructions.push(Instruction::Mov(src1.convert(), dst.convert()));
                instructions.push(Instruction::Binary(
                    operator.convert(),
                    src2.convert(),
                    dst.convert(),
                ));
            }
            tacky::Instruction::Jump(target) => {
                instructions.push(Instruction::Jmp(target.to_string()));
            }
            tacky::Instruction::JumpIfZero(val, target) => {
                instructions.push(Instruction::Cmp(Operand::Imm(0), val.convert()));
                instructions.push(Instruction::JmpCC(ConditionCode::E, target.to_string()));
            }
            tacky::Instruction::JumpIfNotZero(val, target) => {
                instructions.push(Instruction::Cmp(Operand::Imm(0), val.convert()));
                instructions.push(Instruction::JmpCC(ConditionCode::NE, target.to_string()));
            }
            tacky::Instruction::Copy(src, dst) => {
                instructions.push(Instruction::Mov(src.convert(), dst.convert()));
            }
            tacky::Instruction::Label(target) => {
                instructions.push(Instruction::Label(target.to_string()));
            }
        }
    }

    instructions
}

fn fixup_pseudo(body: Instructions) -> Instructions {
    let mut instructions: Instructions = Vec::new();
    let mut pseudo_map: HashMap<String, i32> = HashMap::new();
    let mut stack_depth: i32 = 0;
    let depth: &mut i32 = &mut stack_depth;

    let mut fixup = |operand: Operand| -> Operand {
        const TMPSIZE: i32 = 4;

        if let Operand::Pseudo(tmp) = operand {
            match pseudo_map.get(&tmp) {
                Some(offset) => Operand::Stack(*offset),
                None => {
                    *depth -= TMPSIZE;
                    pseudo_map.insert(tmp, *depth);
                    Operand::Stack(*depth)
                }
            }
        } else {
            operand
        }
    };

    for instruction in body.into_iter() {
        match instruction {
            Instruction::Mov(src, dst) => {
                instructions.push(Instruction::Mov(fixup(src), fixup(dst)));
            }
            Instruction::Unary(op, dst) => {
                instructions.push(Instruction::Unary(op, fixup(dst)));
            }
            Instruction::Binary(op, src, dst) => {
                instructions.push(Instruction::Binary(op, fixup(src), fixup(dst)));
            }
            Instruction::Idiv(src) => {
                instructions.push(Instruction::Idiv(fixup(src)));
            }
            Instruction::Cmp(src1, src2) => {
                instructions.push(Instruction::Cmp(fixup(src1), fixup(src2)));
            }
            Instruction::SetCC(op, dst) => {
                instructions.push(Instruction::SetCC(op, fixup(dst)));
            }
            _ => instructions.push(instruction),
        }
    }

    // Now we know that stack depth. insert the stack allocation instruction.
    instructions.insert(0, Instruction::AllocateStack(stack_depth.abs()));

    instructions
}

fn fixup_invalid(body: Instructions) -> Instructions {
    let mut instructions: Instructions = Vec::new();

    for instruction in body.into_iter() {
        match instruction {
            Instruction::Cmp(src1, Operand::Imm(number)) => {
                instructions.push(Instruction::Mov(
                    Operand::Imm(number),
                    Operand::Reg(Register::R11),
                ));
                instructions.push(Instruction::Cmp(src1, Operand::Reg(Register::R11)));
            }
            Instruction::Cmp(Operand::Stack(src1_offset), Operand::Stack(src2_offset)) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src1_offset),
                    Operand::Reg(Register::R10),
                ));
                instructions.push(Instruction::Cmp(
                    Operand::Reg(Register::R10),
                    Operand::Stack(src2_offset),
                ));
            }
            Instruction::Mov(Operand::Stack(src_offset), Operand::Stack(dst_offset)) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::R10),
                ));
                instructions.push(Instruction::Mov(
                    Operand::Reg(Register::R10),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Idiv(Operand::Imm(number)) => {
                instructions.push(Instruction::Mov(
                    Operand::Imm(number),
                    Operand::Reg(Register::R10),
                ));
                instructions.push(Instruction::Idiv(Operand::Reg(Register::R10)));
            }
            Instruction::Binary(BinaryOperator::Mult, src, Operand::Stack(dst_offset)) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(dst_offset),
                    Operand::Reg(Register::R11),
                ));
                instructions.push(Instruction::Binary(
                    BinaryOperator::Mult,
                    src,
                    Operand::Reg(Register::R11),
                ));
                instructions.push(Instruction::Mov(
                    Operand::Reg(Register::R11),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Binary(
                BinaryOperator::Leftshift,
                Operand::Stack(src_offset),
                Operand::Stack(dst_offset),
            ) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::CL),
                ));
                instructions.push(Instruction::Binary(
                    BinaryOperator::Leftshift,
                    Operand::Reg(Register::CL),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Binary(
                BinaryOperator::Rightshift,
                Operand::Stack(src_offset),
                Operand::Stack(dst_offset),
            ) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::CL),
                ));
                instructions.push(Instruction::Binary(
                    BinaryOperator::Rightshift,
                    Operand::Reg(Register::CL),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Binary(
                operator,
                Operand::Stack(src_offset),
                Operand::Stack(dst_offset),
            ) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::R10),
                ));
                instructions.push(Instruction::Binary(
                    operator,
                    Operand::Reg(Register::R10),
                    Operand::Stack(dst_offset),
                ));
            }
            _ => instructions.push(instruction),
        }
    }

    instructions
}

pub fn emit(assembly: &Assembly) -> Result<String> {
    let mut code = String::new();
    let Assembly::Program(Function(name, instructions)) = assembly;
    let preamble = "\t.section\t__TEXT,__text,regular,pure_instructions\n\t.build_version macos, 15, 0\tsdk_version 15, 2\n";

    write!(&mut code, "{preamble}")?;
    emit_function(&mut code, name, instructions)?;

    Ok(code)
}

impl Operand {
    fn fixup(&self) -> String {
        match self {
            Operand::Reg(Register::AX) => "%eax".to_string(),
            Operand::Reg(Register::CL) => "%cl".to_string(),
            Operand::Reg(Register::DX) => "%edx".to_string(),
            Operand::Reg(Register::R10) => "%r10d".to_string(),
            Operand::Reg(Register::R11) => "%r11d".to_string(),
            Operand::Stack(number) => format!("{number}(%rbp)"),
            Operand::Imm(number) => format!("${number}"),
            Operand::Pseudo(_) => panic!(),
        }
    }

    fn fixup_1byte(&self) -> String {
        match self {
            Operand::Reg(Register::AX) => "%al".to_string(),
            Operand::Reg(Register::CL) => "%cl".to_string(),
            Operand::Reg(Register::DX) => "%dl".to_string(),
            Operand::Reg(Register::R10) => "%r10b".to_string(),
            Operand::Reg(Register::R11) => "%r11b".to_string(),
            Operand::Stack(number) => format!("{number}(%rbp)"),
            Operand::Imm(number) => format!("${number}"),
            Operand::Pseudo(_) => panic!(),
        }
    }
}

impl ConditionCode {
    fn name(&self) -> &str {
        match self {
            ConditionCode::E => "e",
            ConditionCode::NE => "ne",
            ConditionCode::G => "g",
            ConditionCode::GE => "ge",
            ConditionCode::L => "l",
            ConditionCode::LE => "le",
        }
    }
}

fn emit_function(code: &mut String, name: &str, instructions: &Instructions) -> Result<()> {
    // Function prologue. Yes, this is ugly.
    writeln!(
        code,
        "\t.global\t_{name}\n_{name}:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp"
    )?;

    for instruction in instructions.iter() {
        match instruction {
            Instruction::Cmp(src, dst) => {
                writeln!(code, "\tcmpl\t{}, {}", src.fixup(), dst.fixup())?
            }
            Instruction::Jmp(label) => writeln!(code, "\tjmp\tL{}", label)?,
            Instruction::Label(label) => writeln!(code, "L{}:", label)?,
            Instruction::JmpCC(cc, label) => writeln!(code, "\tj{}\tL{}", cc.name(), label)?,
            Instruction::SetCC(cc, dst) => {
                writeln!(code, "\tset{}\t{}", cc.name(), dst.fixup_1byte())?
            }
            Instruction::Mov(src, Operand::Reg(Register::CL)) => {
                writeln!(code, "\tmovb\t{}, %cl", src.fixup())?
            }
            Instruction::Mov(src, dst) => {
                writeln!(code, "\tmovl\t{}, {}", src.fixup(), dst.fixup())?
            }
            Instruction::Unary(operator, dst) => {
                let instruction = match operator {
                    UnaryOperator::Neg => "negl",
                    UnaryOperator::Not => "notl",
                };
                writeln!(code, "\t{}\t{}", instruction, dst.fixup())?;
            }
            Instruction::AllocateStack(number) => writeln!(code, "\tsubq\t${number}, %rsp")?,
            Instruction::Ret => writeln!(code, "\tmovq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret")?,
            Instruction::Cdq => {
                writeln!(code, "\tcdq")?;
            }
            Instruction::Idiv(dst) => {
                writeln!(code, "\tidivl\t{}", dst.fixup())?;
            }
            Instruction::Binary(operator, src, dst) => {
                let instruction = match operator {
                    BinaryOperator::Add => "addl",
                    BinaryOperator::Sub => "subl",
                    BinaryOperator::Mult => "imull",
                    BinaryOperator::Leftshift => "sall",
                    BinaryOperator::Rightshift => "sarl",
                    BinaryOperator::BitAnd => "andl",
                    BinaryOperator::BitXor => "xorl",
                    BinaryOperator::BitOr => "orl",
                };
                writeln!(code, "\t{}\t{}, {}", instruction, src.fixup(), dst.fixup())?;
            }
        }
    }

    Ok(())
}
