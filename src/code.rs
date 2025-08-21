//! # code
//!
//! Generate x86-64 assembly language from the AST created by parser.

use crate::convert::val_type;
use crate::parse;
use crate::parse::Identifier;
use crate::tacky;
use crate::validate::{IdentAttrs, StaticInit, SYMBOLS, BACKEND, BackendSymbol, Symbol, get_symbol};

use anyhow::Result;
use std::collections::HashMap;
use std::convert::Into;
use std::fmt::Write as _;

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
    SP
}

const STACK_COUNT: usize = 6; // First 6 arguments go into registers
static ARG_REGISTERS: [Register; STACK_COUNT] =
    [Register::DI, Register::SI, Register::DX, Register::CX, Register::R8, Register::R9];

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ByteSize {
    B1 = 0, // 1 byte
    B4,     // 4 bytes
    B8      // 8 bytes
}

const REG_SIZES: usize = 3;
const REG_COUNT: usize = 10;

#[rustfmt::skip]
const REGNAME: [[&str; REG_SIZES]; REG_COUNT] = [
    // B1       B4       B8
    ["%al",   "%eax",  "%rax"],
    ["%cl",   "%ecx",  "%rcx"],
    ["%dl",   "%edx",  "%rdx"],
    ["%dil",  "%edi",  "%rdi"],
    ["%sil",  "%esi",  "%rsi"],
    ["%r8b",  "%r8d",  "%r8" ],
    ["%r9b",  "%r9d",  "%r9" ],
    ["%r10b", "%r10d", "%r10"],
    ["%r11b", "%r11d", "%r11"],
    ["%spl",  "%esp",  "%rsp"],
];

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Imm(i64),
    Reg(Register),
    Pseudo(Identifier),
    Stack(i32),
    Data(Identifier)
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
    BitOr
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    Neg,
    Not
}

#[derive(Debug, Clone, PartialEq)]
pub enum ConditionCode {
    E,
    NE,
    G,
    GE,
    L,
    LE
}

#[derive(Debug, Clone, PartialEq)]
pub enum AssemblyType {
    Longword,
    Quadword
}

type Alignment = usize;

impl AssemblyType {
    fn alignment(&self) -> Alignment {
        match self {
            AssemblyType::Longword => 4,
            AssemblyType::Quadword => 8
        }
    }
}

impl From<parse::Type> for AssemblyType {
    fn from(parse_type: parse::Type) -> Self {
        match parse_type {
            parse::Type::Int => AssemblyType::Longword,
            parse::Type::Long => AssemblyType::Quadword,
            _ => todo!()
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Mov(AssemblyType, Operand, Operand),
    Movsx(Operand, Operand),
    Unary(UnaryOperator, AssemblyType, Operand),
    Binary(BinaryOperator, AssemblyType, Operand, Operand),
    Cmp(AssemblyType, Operand, Operand),
    Idiv(AssemblyType, Operand),
    Cdq(AssemblyType),
    Jmp(Identifier),
    JmpCC(ConditionCode, Identifier),
    SetCC(ConditionCode, Operand),
    Label(Identifier),
    Push(Operand),
    Call(Identifier),
    Ret
}

pub type Instructions = Vec<Instruction>;

#[derive(Debug, Clone, PartialEq)]
pub struct Function(Identifier, bool, StackSize, Option<Instructions>);

#[derive(Debug, Clone, PartialEq)]
pub struct StaticVariable(Identifier, bool, Alignment, StaticInit);

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    FunDef(Function),
    VarDef(StaticVariable)
}

type TopLevel = Vec<Definition>;
type Definitions = Vec<Definition>;

#[derive(Debug, Clone, PartialEq)]
pub enum Assembly {
    Program(TopLevel)
}

#[rustfmt::skip]
impl From<parse::UnaryOperator> for UnaryOperator {
    fn from(operator: parse::UnaryOperator) -> Self {
        match operator {
            parse::UnaryOperator::Complement => UnaryOperator::Not,
            parse::UnaryOperator::Negate     => UnaryOperator::Neg,
            parse::UnaryOperator::Not        => UnaryOperator::Not,
        }
    }
}
#[rustfmt::skip]
impl From<&parse::UnaryOperator> for UnaryOperator {
    fn from(operator: &parse::UnaryOperator) -> Self {
        match operator {
            parse::UnaryOperator::Complement => UnaryOperator::Not,
            parse::UnaryOperator::Negate     => UnaryOperator::Neg,
            parse::UnaryOperator::Not        => UnaryOperator::Not,
        }
    }
}

#[rustfmt::skip]
impl From<parse::BinaryOperator> for BinaryOperator {
    fn from(operator: parse::BinaryOperator) -> Self {
        match operator {
            parse::BinaryOperator::Plus       => BinaryOperator::Add,
            parse::BinaryOperator::Minus      => BinaryOperator::Sub,
            parse::BinaryOperator::Multiply   => BinaryOperator::Mult,
            parse::BinaryOperator::Rightshift => BinaryOperator::Rightshift,
            parse::BinaryOperator::Leftshift  => BinaryOperator::Leftshift,
            parse::BinaryOperator::BitAnd     => BinaryOperator::BitAnd,
            parse::BinaryOperator::BitXor     => BinaryOperator::BitXor,
            parse::BinaryOperator::BitOr      => BinaryOperator::BitOr,
            _ => todo!(),
        }
    }
}

#[rustfmt::skip]
impl From<&parse::BinaryOperator> for BinaryOperator {
    fn from(operator: &parse::BinaryOperator) -> Self {
        match operator {
            parse::BinaryOperator::Plus       => BinaryOperator::Add,
            parse::BinaryOperator::Minus      => BinaryOperator::Sub,
            parse::BinaryOperator::Multiply   => BinaryOperator::Mult,
            parse::BinaryOperator::Rightshift => BinaryOperator::Rightshift,
            parse::BinaryOperator::Leftshift  => BinaryOperator::Leftshift,
            parse::BinaryOperator::BitAnd     => BinaryOperator::BitAnd,
            parse::BinaryOperator::BitXor     => BinaryOperator::BitXor,
            parse::BinaryOperator::BitOr      => BinaryOperator::BitOr,
            _ => todo!(),
        }
    }
}

impl From<tacky::Val> for Operand {
    fn from(item: tacky::Val) -> Self {
        match item {
            tacky::Val::Constant(number) => match number {
                parse::Const::ConstInt(number) => Operand::Imm(number),
                parse::Const::ConstLong(number) => Operand::Imm(number)
            },
            tacky::Val::Var(identifier) => Operand::Pseudo(identifier)
        }
    }
}

impl From<&tacky::Val> for Operand {
    fn from(item: &tacky::Val) -> Self {
        match item {
            tacky::Val::Constant(numeric) => match numeric {
                parse::Const::ConstInt(number) => Operand::Imm(*number),
                parse::Const::ConstLong(number) => Operand::Imm(*number)
            },
            tacky::Val::Var(identifier) => Operand::Pseudo(identifier.to_string())
        }
    }
}

pub fn generate(ast: &tacky::Tacky) -> Result<Assembly> {
    let tacky::Tacky::Program(declarations) = ast;
    let mut definitions: Definitions = Vec::new();

    for declaration in declarations {
        match declaration {
            tacky::Definition::FunDef(function_declaration) => {
                let function = gen_assembly(function_declaration)?;
                definitions.push(Definition::FunDef(function));
            },
            tacky::Definition::VarDef(tacky::StaticVariable(name, global, var_type, init)) => {
                let asm_type: AssemblyType = var_type.clone().into();
                let alignment = asm_type.alignment();
                definitions.push(Definition::VarDef(StaticVariable(
                    name.to_string(),
                    *global,
                    alignment,
                    init.clone()
                )));
            }
        }
    }

    // Populate the backend symbol table
    SYMBOLS.with_borrow(|symbol_table| {
        BACKEND.with_borrow_mut(|backend_table| {
            for (name, symbol) in symbol_table {
                match symbol.attrs {
                    IdentAttrs::Static(_, _) => {
                        let asm_type: AssemblyType = symbol.symbol_type.clone().into();
                        backend_table.add(name, BackendSymbol::ObjEntry(asm_type, true));
                    },
                    IdentAttrs::Function(is_defined, _) => {
                        backend_table.add(name, BackendSymbol::FunEntry(is_defined));
                    },
                    IdentAttrs::Local => {
                        let asm_type: AssemblyType = symbol.symbol_type.clone().into();
                        backend_table.add(name, BackendSymbol::ObjEntry(asm_type, false));
                    }
                };
            }   
        });
    });

    for definition in definitions.iter_mut() {
        match definition {
            Definition::FunDef(function) => {
                *function = fixup_pseudo(function);
                *function = fixup_invalid(function);
                *function = allocate_stack(function);
            },
            _ => ()
        }
    }

    Ok(Assembly::Program(definitions))
}

fn convert_function_call(
    name: &String, arguments: &Option<tacky::Arguments>, dst: &tacky::Val,
    instructions: &mut Instructions
) -> Result<()> {
    let mut stack_padding = 0; // in bytes

    if let Some(args) = arguments {
        if (args.len() % 2) == 1 {
            stack_padding = 8;
            instructions.push(Instruction::Binary(
                BinaryOperator::Sub,
                AssemblyType::Quadword,
                Operand::Imm(stack_padding),
                Operand::Reg(Register::SP)
            ));
        }

        let at_ix = args.len().min(STACK_COUNT);
        let register_args = &args[0..at_ix];
        let stack_args = &args[at_ix..];

        for (index, tacky_arg) in register_args.iter().enumerate() {
            let register = ARG_REGISTERS[index];
            let atype = val_type(tacky_arg)?;
            instructions.push(Instruction::Mov(atype, tacky_arg.into(), Operand::Reg(register)));
        }

        for tacky_arg in stack_args.iter().rev() {
            let assembly_arg = tacky_arg.into();
            let atype = val_type(tacky_arg)?;
            if matches!(assembly_arg, Operand::Imm(_) | Operand::Reg(_))
                || matches!(atype, AssemblyType::Quadword)
            {
                instructions.push(Instruction::Push(assembly_arg));
            } else {
                instructions.push(Instruction::Mov(
                    AssemblyType::Longword,
                    assembly_arg,
                    Operand::Reg(Register::AX)
                ));
                instructions.push(Instruction::Push(Operand::Reg(Register::AX)));
            }
        }
        instructions.push(Instruction::Call(name.to_string()));

        let bytes_to_remove = 8 * (stack_args.len() as i64) + stack_padding;
        if bytes_to_remove > 0 {
            instructions.push(Instruction::Binary(
                BinaryOperator::Add,
                AssemblyType::Quadword,
                Operand::Imm(bytes_to_remove),
                Operand::Reg(Register::SP)
            ));
        }
    } else {
        instructions.push(Instruction::Call(name.to_string()));
    }

    instructions.push(Instruction::Mov(val_type(dst)?, Operand::Reg(Register::AX), dst.into()));

    Ok(())
}

fn tacky_to_assembly(instruction: &tacky::Instruction) -> Result<Instructions> {
    let mut instructions: Instructions = Vec::new();

    match instruction {
        tacky::Instruction::FunCall(name, args, dst) => {
            convert_function_call(name, args, dst, &mut instructions)?;
        },
        tacky::Instruction::Return(val) => {
            instructions.push(Instruction::Mov(
                val_type(val)?,
                val.into(),
                Operand::Reg(Register::AX)
            ));
            instructions.push(Instruction::Ret);
        },
        tacky::Instruction::Unary(parse::UnaryOperator::Not, src, dst) => {
            let dst_type = val_type(dst)?;
            let src_type = val_type(src)?;

            instructions.push(Instruction::Cmp(src_type, Operand::Imm(0), src.into()));
            instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::E, dst.into()));
        },
        tacky::Instruction::Unary(operator, src, dst) => {
            let src_type = val_type(src)?;

            instructions.push(Instruction::Mov(src_type.clone(), src.into(), dst.into()));
            instructions.push(Instruction::Unary(operator.into(), src_type.clone(), dst.into()));
        },
        tacky::Instruction::Binary(operator, src1, src2, dst) => {
            let dst_type = val_type(dst)?;
            let src1_type = val_type(src1)?;

            match operator {
                parse::BinaryOperator::Divide => {
                    instructions.push(Instruction::Mov(
                        src1_type.clone(),
                        src1.into(),
                        Operand::Reg(Register::AX)
                    ));
                    instructions.push(Instruction::Cdq(src1_type.clone()));
                    instructions.push(Instruction::Idiv(src1_type.clone(), src2.into()));
                    instructions.push(Instruction::Mov(
                        src1_type.clone(),
                        Operand::Reg(Register::AX),
                        dst.into()
                    ));
                },
                parse::BinaryOperator::Remainder => {
                    instructions.push(Instruction::Mov(
                        src1_type.clone(),
                        src1.into(),
                        Operand::Reg(Register::AX)
                    ));
                    instructions.push(Instruction::Cdq(src1_type.clone()));
                    instructions.push(Instruction::Idiv(src1_type.clone(), src2.into()));
                    instructions.push(Instruction::Mov(
                        src1_type.clone(),
                        Operand::Reg(Register::DX),
                        dst.into()
                    ));
                },
                parse::BinaryOperator::Equal => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::E, dst.into()));
                },
                parse::BinaryOperator::NotEqual => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::NE, dst.into()));
                },
                parse::BinaryOperator::LessThan => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::L, dst.into()));
                },
                parse::BinaryOperator::LessOrEqual => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::LE, dst.into()));
                },
                parse::BinaryOperator::GreaterThan => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::G, dst.into()));
                },
                parse::BinaryOperator::GreaterOrEqual => {
                    instructions.push(Instruction::Cmp(src1_type, src2.into(), src1.into()));
                    instructions.push(Instruction::Mov(dst_type, Operand::Imm(0), dst.into()));
                    instructions.push(Instruction::SetCC(ConditionCode::GE, dst.into()));
                },
                _ => {
                    instructions.push(Instruction::Mov(src1_type.clone(), src1.into(), dst.into()));
                    instructions.push(Instruction::Binary(
                        operator.into(),
                        src1_type,
                        src2.into(),
                        dst.into()
                    ));
                }
            }
        },
        tacky::Instruction::Jump(target) => {
            instructions.push(Instruction::Jmp(target.to_string()));
        },
        tacky::Instruction::JumpIfZero(val, target) => {
            instructions.push(Instruction::Cmp(
                AssemblyType::Longword,
                Operand::Imm(0),
                val.into()
            ));
            instructions.push(Instruction::JmpCC(ConditionCode::E, target.to_string()));
        },
        tacky::Instruction::JumpIfNotZero(val, target) => {
            instructions.push(Instruction::Cmp(
                AssemblyType::Longword,
                Operand::Imm(0),
                val.into()
            ));
            instructions.push(Instruction::JmpCC(ConditionCode::NE, target.to_string()));
        },
        tacky::Instruction::Copy(src, dst) => {
            let src_type = val_type(src)?;
            instructions.push(Instruction::Mov(src_type, src.into(), dst.into()));
        },
        tacky::Instruction::Label(target) => {
            instructions.push(Instruction::Label(target.to_string()));
        },
        tacky::Instruction::SignExtend(src, dst) => {
            instructions.push(Instruction::Movsx(src.into(), dst.into()));
        },
        tacky::Instruction::Truncate(src, dst) => {
            instructions.push(Instruction::Mov(AssemblyType::Longword, src.into(), dst.into()));
        }
    }

    Ok(instructions)
}

fn gen_assembly(function: &tacky::Function) -> Result<Function> {
    let tacky::Function(name, global, parameters, body) = function;
    let instructions = {
        let mut assembly: Instructions = Vec::new();

        if let Some(params) = parameters {
            let mut ix = 0;
            while ix < params.len() && ix < STACK_COUNT {
                let param = params[ix].clone();
                assembly.push(Instruction::Mov(
                    param.type_of.into(),
                    Operand::Reg(ARG_REGISTERS[ix]),
                    Operand::Pseudo(param.name)
                ));
                ix += 1;
            }

            let mut stack_depth = 16;
            while ix < params.len() {
                let param = params[ix].clone();
                assembly.push(Instruction::Mov(
                    param.type_of.into(),
                    Operand::Stack(stack_depth),
                    Operand::Pseudo(param.name)
                ));
                ix += 1;
                stack_depth += 8;
            }
        }

        if let Some(instructions) = body {
            for instruction in instructions {
                let mut code = tacky_to_assembly(instruction)?;
                assembly.append(&mut code);
            }
        }
        if assembly.is_empty() { None } else { Some(assembly) }
    };

    Ok(Function(name.clone(), *global, 0, instructions))
}

fn allocate_stack(function: &Function) -> Function {
    let mut new_function = function.clone();
    match new_function {
        Function(_, _, stack_size, Some(ref mut instructions)) if stack_size > 0 => {
            instructions.insert(
                0,
                Instruction::Binary(
                    BinaryOperator::Sub,
                    AssemblyType::Quadword,
                    Operand::Imm(stack_size.into()),
                    Operand::Reg(Register::SP)
                )
            );
        },
        _ => ()
    };
    new_function
}

fn fixup_pseudo(function: &Function) -> Function {
    let Function(name, global, _, body) = function;
    let mut pseudo_map: HashMap<String, i32> = HashMap::new();
    let mut stack_depth: i32 = 0;
    let depth: &mut i32 = &mut stack_depth;

    let mut fixup = |operand: &Operand| -> Operand {
        const TMPSIZE: i32 = 4;
        if let Operand::Pseudo(identifier) = operand {
            match get_symbol(identifier) {
                Some(Symbol { attrs: IdentAttrs::Static(_, _), .. }) => {
                    Operand::Data(identifier.to_string())
                },
                _ => match pseudo_map.get(identifier) {
                    Some(offset) => Operand::Stack(*offset),
                    None => {
                        *depth -= TMPSIZE;
                        pseudo_map.insert(identifier.to_string(), *depth);
                        Operand::Stack(*depth)
                    }
                }
            }
        } else {
            operand.clone()
        }
    };

    let instructions = body.as_ref().map(|block: &Instructions| -> Instructions {
        let mut assembly = Instructions::new();

        block.iter().for_each(|instruction: &Instruction| {
            assembly.push(match instruction {
                Instruction::Mov(atype, src, dst) => {
                    Instruction::Mov(atype.clone(), fixup(src), fixup(dst))
                },
                Instruction::Unary(op, atype, dst) => {
                    Instruction::Unary(op.clone(), atype.clone(), fixup(dst))
                },
                Instruction::Binary(op, atype, src, dst) => {
                    Instruction::Binary(op.clone(), atype.clone(), fixup(src), fixup(dst))
                },
                Instruction::Idiv(atype, src) => Instruction::Idiv(atype.clone(), fixup(src)),
                Instruction::Cmp(atype, src1, src2) => {
                    Instruction::Cmp(atype.clone(), fixup(src1), fixup(src2))
                },
                Instruction::SetCC(op, dst) => Instruction::SetCC(op.clone(), fixup(dst)),
                Instruction::Push(src) => Instruction::Push(fixup(src)),
                _ => instruction.clone()
            })
        });
        assembly
    });
    let mut stack_size = 0;
    if stack_depth < 0 {
        stack_size = (stack_depth.abs() / 16) * 16 + 16
    }

    Function(name.clone(), *global, stack_size, instructions)
}

fn fixup_invalid(function: &Function) -> Function {
    let Function(name, global, stack_size, body) = function;

    let instructions = body.as_ref().map(|block| -> Instructions {
        macro_rules! invalid {
            ($src:expr, $dst:expr) => {
                matches!($src, Operand::Stack(_) | Operand::Data(_))
                    && matches!($dst, Operand::Stack(_) | Operand::Data(_))
            };
        }
        let mut instructions = Instructions::new();

        for instruction in block {
            match instruction {
                Instruction::Cmp(atype, src, Operand::Imm(number)) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        Operand::Imm(*number),
                        Operand::Reg(Register::R11)
                    ));
                    instructions.push(Instruction::Cmp(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::R11)
                    ));
                },
                Instruction::Cmp(atype, src, dst) if invalid!(src, dst) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        dst.clone(),
                        Operand::Reg(Register::R11)
                    ));
                    instructions.push(Instruction::Cmp(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::R11)
                    ));
                },
                Instruction::Mov(atype, src, dst) if invalid!(src, dst) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::R10)
                    ));
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        Operand::Reg(Register::R10),
                        dst.clone()
                    ));
                },
                Instruction::Idiv(atype, Operand::Imm(number)) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        Operand::Imm(*number),
                        Operand::Reg(Register::R10)
                    ));
                    instructions
                        .push(Instruction::Idiv(atype.clone(), Operand::Reg(Register::R10)));
                },
                Instruction::Binary(BinaryOperator::Mult, atype, src, dst) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        dst.clone(),
                        Operand::Reg(Register::R11)
                    ));
                    instructions.push(Instruction::Binary(
                        BinaryOperator::Mult,
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::R11)
                    ));
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        Operand::Reg(Register::R11),
                        dst.clone()
                    ));
                },
                Instruction::Binary(BinaryOperator::Leftshift, atype, src, dst)
                    if invalid!(src, dst) =>
                {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::CX)
                    ));
                    instructions.push(Instruction::Binary(
                        BinaryOperator::Leftshift,
                        atype.clone(),
                        Operand::Reg(Register::CX),
                        dst.clone()
                    ));
                },
                Instruction::Binary(BinaryOperator::Rightshift, atype, src, dst)
                    if invalid!(src, dst) =>
                {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::CX)
                    ));
                    instructions.push(Instruction::Binary(
                        BinaryOperator::Rightshift,
                        atype.clone(),
                        Operand::Reg(Register::CX),
                        dst.clone()
                    ));
                },
                Instruction::Binary(operator, atype, src, dst) if invalid!(src, dst) => {
                    instructions.push(Instruction::Mov(
                        atype.clone(),
                        src.clone(),
                        Operand::Reg(Register::R10)
                    ));
                    instructions.push(Instruction::Binary(
                        operator.clone(),
                        atype.clone(),
                        Operand::Reg(Register::R10),
                        dst.clone()
                    ));
                },
                _ => instructions.push(instruction.clone())
            }
        }

        instructions
    });

    Function(name.clone(), *global, *stack_size, instructions)
}

pub fn emit(assembly: &Assembly) -> Result<String> {
    let mut code = String::new();

    writeln!(
        &mut code,
        r#"    .section __TEXT,__text,regular,pure_instructions
    .build_version macos, 12, 0  sdk_version 12, 2
    "#
    )?;

    let Assembly::Program(definitions) = assembly;
    for definition in definitions {
        match definition {
            Definition::FunDef(function) => emit_function(&mut code, function)?,
            Definition::VarDef(variable) => emit_static_variable(&mut code, variable)?
        }
    }

    Ok(code)
}

#[rustfmt::skip]
impl Operand {
    fn fixup(&self, size: ByteSize) -> String {
        match self {
            Operand::Reg(register) => REGNAME[*register as usize][size as usize].to_string(),
            Operand::Stack(number) => format!("{number}(%rbp)"),
            Operand::Imm(number)   => format!("${number}"),
            Operand::Data(name) => format!("_{name}(%rip)"),
            Operand::Pseudo(_)           => panic!(),
        }
    }

    fn r1b(&self) -> String {
        self.fixup(ByteSize::B1)
    }

    fn r4b(&self) -> String {
        self.fixup(ByteSize::B4)
    }

    fn r8b(&self) -> String {
        self.fixup(ByteSize::B8)
    }
}

#[rustfmt::skip]
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
            UnaryOperator::Not => "notl"
        }
    }
}

#[rustfmt::skip]
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
        Instruction::Push(src) => writeln!(code, "    push    {}", src.r8b())?,
        Instruction::Call(name) => writeln!(code, "    call    _{name}")?,
        Instruction::Cmp(_atype, src, dst) => {
            writeln!(code, "    cmpl    {}, {}", src.r4b(), dst.r4b())?
        },
        Instruction::Jmp(label) => writeln!(code, "    jmp     L{}", label)?,
        Instruction::Label(label) => writeln!(code, "L{}:", label)?,
        Instruction::JmpCC(cc, label) => writeln!(code, "    j{}     L{}", cc.name(), label)?,
        Instruction::SetCC(cc, dst) => writeln!(code, "    set{}   {}", cc.name(), dst.r1b())?,
        Instruction::Mov(_atype, src, dst) => {
            writeln!(code, "    movl    {}, {}", src.r4b(), dst.r4b())?
        },
        Instruction::Unary(operator, _atype, dst) => {
            writeln!(code, "    {}    {}", operator.name(), dst.r4b())?
        },
        Instruction::Ret => writeln!(code, "    movq    %rbp, %rsp\n    popq    %rbp\n    ret")?,
        Instruction::Cdq(_atype) => writeln!(code, "    cdq")?,
        Instruction::Idiv(_atype, dst) => writeln!(code, "    idivl   {}", dst.r4b())?,
        Instruction::Binary(operator, _atype, src, dst) => {
            let src_name = match operator {
                BinaryOperator::Leftshift | BinaryOperator::Rightshift => src.r1b(),
                _ => src.r4b()
            };
            writeln!(code, "    {}  {}, {}", operator.name(), src_name, dst.r4b())?;
        },
        Instruction::Movsx(_, _) => todo!()
    }

    Ok(())
}

fn emit_static_variable(code: &mut String, variable: &StaticVariable) -> Result<()> {
    let StaticVariable(name, global, alignment, init) = variable;

    if *global {
        writeln!(code, "    .globl   _{name}")?;
    }
    match init {
        StaticInit::IntInit(init_value) => {
            if *init_value == 0 {
                writeln!(code, "    .bss")?;
                writeln!(code, "    .balign {alignment}")?;
                writeln!(code, "_{name}:")?;
                writeln!(code, "    .zero {alignment}")?;
            } else {
                writeln!(code, "    .data")?;
                writeln!(code, "    .balign {alignment}")?;
                writeln!(code, "_{name}:")?;
                writeln!(code, "    .long {init_value}")?;
            }
        },
        StaticInit::LongInit(init_value) => {
            if *init_value == 0 {
                writeln!(code, "    .bss")?;
                writeln!(code, "    .balign {alignment}")?;
                writeln!(code, "_{name}:")?;
                writeln!(code, "    .zero {alignment}")?;
            } else {
                writeln!(code, "    .data")?;
                writeln!(code, "    .balign {alignment}")?;
                writeln!(code, "_{name}:")?;
                writeln!(code, "    .quad {init_value}")?;
            }
        },
    }

    Ok(())
}

fn emit_function(code: &mut String, function: &Function) -> Result<()> {
    let Function(name, global, _stack_size, body) = function;

    if let Some(instructions) = body {
        if *global {
            writeln!(code, "\n    .globl   _{name}")?;
        }

        writeln!(
            code,
            r#"    .text
_{name}:
    pushq   %rbp
    movq    %rsp, %rbp"#
        )?;

        for instruction in instructions {
            emit_instruction(code, instruction)?;
        }
    }

    Ok(())
}
