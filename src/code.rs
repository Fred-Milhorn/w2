//! # code
//!
//! Generate x86-64 assembly language from the AST created by parser.

use crate::tacky;
use anyhow::Result;
use std::collections::HashMap;
use std::fmt::Write as _;

pub type Identifier = String;
pub type Instructions = Vec<Instruction>;
pub type FunctionDefinitions = Vec<Function>;
pub type StackSize = i32;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Register {
    AX = 0,
    CX,
    DX,
    DI,
    SI,
    R8,
    R9,
    R10,
    R11,
}

const STACK_COUNT: usize = 6;            // First 6 arguments go into registers
static ARG_REGISTERS: [Register; STACK_COUNT] = [
    Register::DI, Register::SI, Register::DX,
    Register::CX, Register::R8, Register::R9,
];

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ByteSize {
    B1 = 0, // 1 byte 
    B4,     // 4 bytes
    B8      // 8 bytes
}

const REG_SIZES: usize = 3;
const REG_COUNT: usize = 9;
const REGNAME: [[&str; REG_SIZES]; REG_COUNT] = [
    // B1       B4       B8
    ["%al",   "%eax",  "%rax"],
    ["%dl",   "%edx",  "%rdx"],
    ["%cl",   "%ecx",  "%rcx"],
    ["%dil",  "%edi",  "%rdi"],
    ["%sil",  "%esi",  "%rsi"],
    ["%r8b",  "%r8d",  "%r8" ],
    ["%r9b",  "%r9d",  "%r9" ],
    ["%r10b", "%r10d", "%r10" ],
    ["%r11b", "%r11d", "%r11" ],
];

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
    DeallocateStack(i32),
    Push(Operand),
    Call(Identifier),
    Ret,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function(Identifier, StackSize, Instructions);

#[derive(Debug, Clone, PartialEq)]
pub enum Assembly {
    Program(FunctionDefinitions),
}

impl tacky::UnaryOperator {
    fn convert(&self) -> UnaryOperator {
        match self {
            tacky::UnaryOperator::Complement => UnaryOperator::Not,
            tacky::UnaryOperator::Negate     => UnaryOperator::Neg,
            tacky::UnaryOperator::Not        => UnaryOperator::Not,
        }
    }
}

impl tacky::BinaryOperator {
    fn convert(&self) -> BinaryOperator {
        match self {
            tacky::BinaryOperator::Add        => BinaryOperator::Add,
            tacky::BinaryOperator::Subtract   => BinaryOperator::Sub,
            tacky::BinaryOperator::Multiply   => BinaryOperator::Mult,
            tacky::BinaryOperator::Rightshift => BinaryOperator::Rightshift,
            tacky::BinaryOperator::Leftshift  => BinaryOperator::Leftshift,
            tacky::BinaryOperator::BitAnd     => BinaryOperator::BitAnd,
            tacky::BinaryOperator::BitXor     => BinaryOperator::BitXor,
            tacky::BinaryOperator::BitOr      => BinaryOperator::BitOr,
            _ => todo!(),
        }
    }
}

impl tacky::Val {
    fn convert(&self) -> Operand {
        match self {
            tacky::Val::Constant(number) => Operand::Imm(*number),
            tacky::Val::Var(identifier)  => Operand::Pseudo(identifier.to_string()),
        }
    }
}

pub fn generate(ast: &tacky::Tacky) -> Assembly {
    let tacky::Tacky::Program(definitions) = ast;
    let mut functions: FunctionDefinitions = Vec::new();

    for definition in definitions.into_iter() {
	let mut function = gen_assembly(definition);
	function = fixup_pseudo(function);
	function = fixup_invalid(function);

	functions.push(function);
    }

    Assembly::Program(functions)
}

fn convert_function_call(name: &String, arguments: &Option<tacky::Args>, dst: &tacky::Val, instructions: &mut Instructions) {
    let mut stack_padding: i32 = 0;  // in bytes

    if let Some(args) = arguments {
	if (args.len() % 2) == 1 {
	    stack_padding = 8;
	    instructions.push(Instruction::AllocateStack(stack_padding));
	}

	let at_ix = args.len().min(STACK_COUNT);
	let register_args = &args[0..at_ix];
	let stack_args = &args[at_ix..];

	for (index, tacky_arg) in register_args.iter().enumerate() {
	    let register = ARG_REGISTERS[index];
	    let assembly_arg = tacky_arg.convert();
	    instructions.push(Instruction::Mov(assembly_arg, Operand::Reg(register)));
	}

	for tacky_arg in stack_args.iter().rev() {
	    let assembly_arg = tacky_arg.convert();
	    match assembly_arg {
		Operand::Imm(_) |
		Operand::Reg(_) => {
		    instructions.push(Instruction::Push(assembly_arg));
		},
		_ => {
		    instructions.push(Instruction::Mov(assembly_arg, Operand::Reg(Register::AX)));
		    instructions.push(Instruction::Push(Operand::Reg(Register::AX)));
		}
	    }
	}
	instructions.push(Instruction::Call(name.to_string()));

	let bytes_to_remove: i32 = 8 * (stack_args.len() as i32) + stack_padding;
	if bytes_to_remove > 0 {
	    instructions.push(Instruction::DeallocateStack(bytes_to_remove));
	}
	
    } else {
	instructions.push(Instruction::Call(name.to_string()));
    }

    instructions.push(Instruction::Mov(Operand::Reg(Register::AX), dst.convert()));
}

fn gen_assembly(function: &tacky::FunctionDefinition) -> Function {
    let tacky::FunctionDefinition(name, parameters, body) = function;
    let mut instructions: Instructions = Vec::new();

    if let Some(params) = parameters {
	let mut ix = 0;
	while ix < params.len() && ix < STACK_COUNT {
	    instructions.push(Instruction::Mov(Operand::Reg(ARG_REGISTERS[ix]),
					       Operand::Pseudo(params[ix].to_string())));
	    ix += 1;
	}

	let mut stack_depth = 16;
	while ix < params.len() {
	    instructions.push(Instruction::Mov(Operand::Stack(stack_depth),
					       Operand::Pseudo(params[ix].to_string())));
	    ix += 1;
	    stack_depth += 8;
	}
    }

    for instruction in body {
        match instruction {
            tacky::Instruction::FunCall(name, args, dst) => {
                convert_function_call(name, args, dst, &mut instructions);
            }
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

    Function(name.clone(), 0, instructions)
}

fn fixup_pseudo(function: Function) -> Function {
    let Function(name, _, body) = function;
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

    for instruction in body {
        match instruction {
            Instruction::Mov(src, dst) => {
                instructions.push(Instruction::Mov(fixup(src), fixup(dst)));
            },
            Instruction::Unary(op, dst) => {
                instructions.push(Instruction::Unary(op, fixup(dst)));
            },
            Instruction::Binary(op, src, dst) => {
                instructions.push(Instruction::Binary(op, fixup(src), fixup(dst)));
            },
            Instruction::Idiv(src) => {
                instructions.push(Instruction::Idiv(fixup(src)));
            },
            Instruction::Cmp(src1, src2) => {
                instructions.push(Instruction::Cmp(fixup(src1), fixup(src2)));
            },
            Instruction::SetCC(op, dst) => {
                instructions.push(Instruction::SetCC(op, fixup(dst)));
            },
	    Instruction::Push(src) => {
		instructions.push(Instruction::Push(fixup(src)));
	    },
            _ => instructions.push(instruction),
        }
    }

    // Now we know that stack depth. insert the stack allocation instruction.
    instructions.insert(0, Instruction::AllocateStack(stack_depth.abs()));

    Function(name.clone(), stack_depth.abs(), instructions)
}

fn fixup_invalid(function: Function) -> Function {
    let Function(name, stack_size, body) = function;
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
            Instruction::Binary(BinaryOperator::Leftshift,
				Operand::Stack(src_offset), Operand::Stack(dst_offset)) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::CX),
                ));
                instructions.push(Instruction::Binary(
                    BinaryOperator::Leftshift,
                    Operand::Reg(Register::CX),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Binary(BinaryOperator::Rightshift,
				Operand::Stack(src_offset), Operand::Stack(dst_offset)) => {
                instructions.push(Instruction::Mov(
                    Operand::Stack(src_offset),
                    Operand::Reg(Register::CX),
                ));
                instructions.push(Instruction::Binary(
                    BinaryOperator::Rightshift,
                    Operand::Reg(Register::CX),
                    Operand::Stack(dst_offset),
                ));
            }
            Instruction::Binary(operator,
				Operand::Stack(src_offset), Operand::Stack(dst_offset)) => {
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

    Function(name.clone(), stack_size, instructions)
}

pub fn emit(assembly: &Assembly) -> Result<String> {
    let mut code = String::new();
    let preamble = "\t.section\t__TEXT,__text,regular,pure_instructions\n\t.build_version macos, 15, 0\tsdk_version 15, 2\n";

    writeln!(&mut code, "{preamble}")?;

    let Assembly::Program(functions) = assembly;
    for function in functions {
	emit_function(&mut code, function)?;
    }

    Ok(code)
}

impl Operand {
    fn fixup(&self, size: ByteSize) -> String {
        match self {
            Operand::Reg(register) => {
		REGNAME[*register as usize][size as usize].to_string()
	    },
            Operand::Stack(number) => format!("{number}(%rbp)"),
            Operand::Imm(number)   => format!("${number}"),
            Operand::Pseudo(_)     => panic!(),
        }
    }

    fn r1b(&self) -> String {
	self.fixup(ByteSize::B1)
    }

    fn r4b(&self) -> String {
	self.fixup(ByteSize::B4)
    }

    #[allow(dead_code)]
    fn r8b(&self) -> String {
	self.fixup(ByteSize::B8)
    }
}

impl ConditionCode {
    fn name(&self) -> &str {
        match self {
            ConditionCode::E  => "e",
            ConditionCode::NE => "ne",
            ConditionCode::G  => "g",
            ConditionCode::GE => "ge",
            ConditionCode::L  => "l",
            ConditionCode::LE => "le",
        }
    }
}

impl UnaryOperator {
    fn name(&self) -> &str {
        match self {
            UnaryOperator::Neg => "negl",
            UnaryOperator::Not => "notl",
        }
    }
}

impl BinaryOperator {
    fn name(&self) -> &str {
        match self {
            BinaryOperator::Add        => "addl",
            BinaryOperator::Sub        => "subl",
            BinaryOperator::Mult       => "imull",
            BinaryOperator::Leftshift  => "sall",
            BinaryOperator::Rightshift => "sarl",
            BinaryOperator::BitAnd     => "andl",
            BinaryOperator::BitXor     => "xorl",
            BinaryOperator::BitOr      => "orl",
        }
    }
}

fn emit_instruction(code: &mut String, instruction: &Instruction) -> Result<()> {
    match instruction {
    	Instruction::DeallocateStack(number)    => writeln!(code, "\taddq\t{number}, %rsp")?,
    	Instruction::Push(src)                  => writeln!(code, "\tpush\t{}", src.r4b())?,
    	Instruction::Call(name)                 => writeln!(code, "\tcall\t_{name}")?,
        Instruction::Cmp(src, dst)              => writeln!(code, "\tcmpl\t{}, {}", src.r4b(), dst.r4b())?,
        Instruction::Jmp(label)                 => writeln!(code, "\tjmp\tL{}", label)?,
        Instruction::Label(label)               => writeln!(code, "L{}:", label)?,
        Instruction::JmpCC(cc, label)           => writeln!(code, "\tj{}\tL{}", cc.name(), label)?,
        Instruction::SetCC(cc, dst)             => writeln!(code, "\tset{}\t{}", cc.name(), dst.r1b())?,
        Instruction::Mov(src, dst)              => writeln!(code, "\tmovl\t{}, {}", src.r4b(), dst.r4b())?,
        Instruction::Unary(operator, dst)       => writeln!(code, "\t{}\t{}", operator.name(), dst.r4b())?,
        Instruction::AllocateStack(number)      => writeln!(code, "\tsubq\t${number}, %rsp")?,
        Instruction::Ret                        => writeln!(code, "\tmovq\t%rbp, %rsp\n\tpopq\t%rbp\n\tret")?,
        Instruction::Cdq                        => writeln!(code, "\tcdq")?,
        Instruction::Idiv(dst)                  => writeln!(code, "\tidivl\t{}", dst.r4b())?,
        Instruction::Binary(operator, src, dst) => writeln!(code, "\t{}\t{}, {}", operator.name(), src.r4b(), dst.r4b())?,
    }

    Ok(())
}

fn emit_function(code: &mut String, function: &Function) -> Result<()> {
    let Function(name, _stack_size, instructions) = function;

    writeln!(code, "\t.global\t_{name}\n_{name}:\n\tpushq\t%rbp\n\tmovq\t%rsp, %rbp")?;

    for instruction in instructions {
	emit_instruction(code, instruction)?;
    }

    Ok(())
}
