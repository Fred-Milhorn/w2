//! # code
//!
//! Generate x86-64 assembly language from the AST created by parser.

use crate::parse;
use crate::parse::Identifier;
use crate::tacky;
use crate::validate::{IdentAttrs, StaticInit, Symbol, SymbolTable};

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
    R11
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
const REG_COUNT: usize = 9;

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
    ["%r11b", "%r11d", "%r11"]
];

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Imm(i32),
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

impl Into<AssemblyType> for parse::Type {
    fn into(self) -> AssemblyType {
        match self {
            parse::Type::Int => AssemblyType::Longword,
            parse::Type::Long => AssemblyType::Quadword,
            _ => todo!()
        }
    }
}

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
    AllocateStack(i32),
    DeallocateStack(i32),
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
impl Into<UnaryOperator> for parse::UnaryOperator {
    fn into(self) -> UnaryOperator {
        match self {
            parse::UnaryOperator::Complement => UnaryOperator::Not,
            parse::UnaryOperator::Negate     => UnaryOperator::Neg,
            parse::UnaryOperator::Not        => UnaryOperator::Not,
        }
    }
}

#[rustfmt::skip]
impl Into<BinaryOperator> for parse::BinaryOperator {
    fn into(self) -> BinaryOperator {
        match self {
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

impl Into<Operand> for tacky::Val {
    fn into(self) -> Operand {
        match self {
            tacky::Val::Constant(number) => match number {
                parse::Const::ConstInt(number) => Operand::Imm(number),
                parse::Const::ConstLong(_number) => todo!()
            },
            tacky::Val::Var(identifier) => Operand::Pseudo(identifier)
        }
    }
}

pub fn generate(ast: &tacky::Tacky, symbol_table: &SymbolTable) -> Assembly {
    let tacky::Tacky::Program(declarations) = ast;
    let mut definitions: Definitions = Vec::new();

    for declaration in declarations {
        match declaration {
            tacky::Definition::FunDef(function_declaration) => {
                let mut function = gen_assembly(function_declaration);
                function = fixup_pseudo(function, symbol_table);
                function = fixup_invalid(function);
                function = allocate_stack(function);
                definitions.push(Definition::FunDef(function));
            },
            tacky::Definition::VarDef(tacky::StaticVariable(name, global, var_type, init)) => {
                let asm_type: AssemblyType = (var_type.clone()).into();
                let alignment = asm_type.alignment();
                definitions.push(Definition::VarDef(StaticVariable(name.to_string(),
                                                                   *global,
                                                                   alignment,
                                                                   init.clone())));
            }
        }
    }

    Assembly::Program(definitions)
}

fn convert_function_call(name: &String, arguments: &Option<tacky::Arguments>, dst: &tacky::Val,
                         instructions: &mut Instructions) {
    let mut stack_padding: i32 = 0; // in bytes

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
            let assembly_arg = tacky_arg.into();
            instructions.push(Instruction::Mov(assembly_arg, Operand::Reg(register)));
        }

        for tacky_arg in stack_args.iter().rev() {
            let assembly_arg = tacky_arg.into();
            match assembly_arg {
                Operand::Imm(_) | Operand::Reg(_) => {
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

    instructions.push(Instruction::Mov(Operand::Reg(Register::AX), dst.into()));
}

fn tacky_to_assembly(instruction: &tacky::Instruction) -> Instructions {
    let mut instructions: Instructions = Vec::new();

    match instruction {
        tacky::Instruction::FunCall(name, args, dst) => {
            convert_function_call(name, args, dst, &mut instructions);
        },
        tacky::Instruction::Return(val) => {
            instructions.push(Instruction::Mov(val.into(), Operand::Reg(Register::AX)));
            instructions.push(Instruction::Ret);
        },
        tacky::Instruction::Unary(tacky::UnaryOperator::Not, src, dst) => {
            instructions.push(Instruction::Cmp(Operand::Imm(0), src.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::E, dst.into()));
        },
        tacky::Instruction::Unary(operator, src, dst) => {
            instructions.push(Instruction::Mov(src.into(), dst.into()));
            instructions.push(Instruction::Unary(operator.into(), dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::Divide, src1, src2, dst) => {
            instructions.push(Instruction::Mov(src1.into(), Operand::Reg(Register::AX)));
            instructions.push(Instruction::Cdq);
            instructions.push(Instruction::Idiv(src2.into()));
            instructions.push(Instruction::Mov(Operand::Reg(Register::AX), dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::Remainder, src1, src2, dst) => {
            instructions.push(Instruction::Mov(src1.into(), Operand::Reg(Register::AX)));
            instructions.push(Instruction::Cdq);
            instructions.push(Instruction::Idiv(src2.into()));
            instructions.push(Instruction::Mov(Operand::Reg(Register::DX), dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::Equal, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::E, dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::NotEqual, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::NE, dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::LessThan, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::L, dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::LessOrEqual, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::LE, dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::GreaterThan, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::G, dst.into()));
        },
        tacky::Instruction::Binary(tacky::BinaryOperator::GreaterOrEqual, src1, src2, dst) => {
            instructions.push(Instruction::Cmp(src2.into(), src1.into()));
            instructions.push(Instruction::Mov(Operand::Imm(0), dst.into()));
            instructions.push(Instruction::SetCC(ConditionCode::GE, dst.into()));
        },
        tacky::Instruction::Binary(operator, src1, src2, dst) => {
            instructions.push(Instruction::Mov(src1.into(), dst.into()));
            instructions.push(Instruction::Binary(operator.into(), src2.into(), dst.into()));
        },
        tacky::Instruction::Jump(target) => {
            instructions.push(Instruction::Jmp(target.to_string()));
        },
        tacky::Instruction::JumpIfZero(val, target) => {
            instructions.push(Instruction::Cmp(Operand::Imm(0), val.into()));
            instructions.push(Instruction::JmpCC(ConditionCode::E, target.to_string()));
        },
        tacky::Instruction::JumpIfNotZero(val, target) => {
            instructions.push(Instruction::Cmp(Operand::Imm(0), val.into()));
            instructions.push(Instruction::JmpCC(ConditionCode::NE, target.to_string()));
        },
        tacky::Instruction::Copy(src, dst) => {
            instructions.push(Instruction::Mov(src.into(), dst.into()));
        },
        tacky::Instruction::Label(target) => {
            instructions.push(Instruction::Label(target.to_string()));
        }
    }

    instructions
}

fn gen_assembly(function: &tacky::Function) -> Function {
    let tacky::Function(name, global, parameters, body) = function;
    let instructions = body.as_ref().map(|instructions: &tacky::Instructions| -> Instructions {
                                        let mut assembly: Instructions = Vec::new();

                                        if let Some(params) = parameters {
                                            let mut ix = 0;
                                            while ix < params.len() && ix < STACK_COUNT {
                                                assembly.push(Instruction::Mov(Operand::Reg(ARG_REGISTERS[ix]),
                                                                Operand::Pseudo(params[ix].to_string())));
                                                ix += 1;
                                            }

                                            let mut stack_depth = 16;
                                            while ix < params.len() {
                                                assembly.push(Instruction::Mov(Operand::Stack(stack_depth),
                                                                Operand::Pseudo(params[ix].to_string())));
                                                ix += 1;
                                                stack_depth += 8;
                                            }
                                        }

                                        instructions.iter().for_each(|instruction| {
                                                               assembly.append(&mut tacky_to_assembly(instruction))
                                                           });

                                        assembly
                                    });

    Function(name.clone(), *global, 0, instructions)
}

fn allocate_stack(function: Function) -> Function {
    match function {
        Function(name, global, stack_size, Some(mut instructions)) if stack_size > 0 => {
            instructions.insert(0, Instruction::AllocateStack(stack_size));
            Function(name, global, stack_size, Some(instructions))
        },
        _ => function
    }
}

fn fixup_pseudo(function: Function, symbol_table: &SymbolTable) -> Function {
    let Function(name, global, _, body) = function;
    let mut pseudo_map: HashMap<String, i32> = HashMap::new();
    let mut stack_depth: i32 = 0;
    let depth: &mut i32 = &mut stack_depth;

    let mut fixup = |operand: &Operand| -> Operand {
        const TMPSIZE: i32 = 4;
        if let Operand::Pseudo(identifier) = operand {
            match symbol_table.get(identifier) {
                Some(Symbol { attrs: IdentAttrs::Static(_, _), .. }) => Operand::Data(identifier.to_string()),
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

    let instructions =
        body.as_ref().map(|block: &Instructions| -> Instructions {
                         let mut assembly = Instructions::new();

                         block.iter().for_each(|instruction: &Instruction| {
                                         assembly.push(match instruction {
                                                     Instruction::Mov(atype, src, dst) => {
                                                         Instruction::Mov(atype, fixup(src), fixup(dst))
                                                     },
                                                     Instruction::Unary(op, atype, dst) => {
                                                         Instruction::Unary(op.clone(), atype, fixup(dst))
                                                     },
                                                     Instruction::Binary(op, atype, src, dst) => {
                                                         Instruction::Binary(op.clone(), atype, fixup(src), fixup(dst))
                                                     },
                                                     Instruction::Idiv(atype, src) => {
                                                         Instruction::Idiv(atype, fixup(src))
                                                     },
                                                     Instruction::Cmp(atype, src1, src2) => {
                                                         Instruction::Cmp(atype, fixup(src1), fixup(src2))
                                                     },
                                                     Instruction::SetCC(op, dst) => {
                                                         Instruction::SetCC(op.clone(), fixup(dst))
                                                     },
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

    Function(name.clone(), global, stack_size, instructions)
}

fn fixup_invalid(function: Function) -> Function {
    let Function(name, global, stack_size, body) = function;

    let instructions =
        body.as_ref().map(|block| -> Instructions {
                         macro_rules! invalid {
                             ($src:expr, $dst:expr) => {
                                 matches!($src, Operand::Stack(_) | Operand::Data(_))
                                 && matches!($dst, Operand::Stack(_) | Operand::Data(_))
                             };
                         }
                         let mut instructions = Instructions::new();

                         for instruction in block {
                             match instruction {
                                 Instruction::Cmp(src, Operand::Imm(number)) => {
                                     instructions.push(Instruction::Mov(Operand::Imm(*number),
                                                                        Operand::Reg(Register::R11)));
                                     instructions.push(Instruction::Cmp(src.clone(), Operand::Reg(Register::R11)));
                                 },
                                 Instruction::Cmp(src, dst) if invalid!(src, dst) => {
                                     instructions.push(Instruction::Mov(dst.clone(), Operand::Reg(Register::R11)));
                                     instructions.push(Instruction::Cmp(src.clone(), Operand::Reg(Register::R11)));
                                 },
                                 Instruction::Mov(src, dst) if invalid!(src, dst) => {
                                     instructions.push(Instruction::Mov(src.clone(), Operand::Reg(Register::R10)));
                                     instructions.push(Instruction::Mov(Operand::Reg(Register::R10), dst.clone()));
                                 },
                                 Instruction::Idiv(Operand::Imm(number)) => {
                                     instructions.push(Instruction::Mov(Operand::Imm(*number),
                                                                        Operand::Reg(Register::R10)));
                                     instructions.push(Instruction::Idiv(Operand::Reg(Register::R10)));
                                 },
                                 Instruction::Binary(BinaryOperator::Mult, src, dst) => {
                                     instructions.push(Instruction::Mov(dst.clone(), Operand::Reg(Register::R11)));
                                     instructions.push(Instruction::Binary(BinaryOperator::Mult,
                                                                           src.clone(),
                                                                           Operand::Reg(Register::R11)));
                                     instructions.push(Instruction::Mov(Operand::Reg(Register::R11), dst.clone()));
                                 },
                                 Instruction::Binary(BinaryOperator::Leftshift, src, dst) if invalid!(src, dst) => {
                                     instructions.push(Instruction::Mov(src.clone(), Operand::Reg(Register::CX)));
                                     instructions.push(Instruction::Binary(BinaryOperator::Leftshift,
                                                                           Operand::Reg(Register::CX),
                                                                           dst.clone()));
                                 },
                                 Instruction::Binary(BinaryOperator::Rightshift, src, dst) if invalid!(src, dst) => {
                                     instructions.push(Instruction::Mov(src.clone(), Operand::Reg(Register::CX)));
                                     instructions.push(Instruction::Binary(BinaryOperator::Rightshift,
                                                                           Operand::Reg(Register::CX),
                                                                           dst.clone()));
                                 },
                                 Instruction::Binary(operator, src, dst) if invalid!(src, dst) => {
                                     instructions.push(Instruction::Mov(src.clone(), Operand::Reg(Register::R10)));
                                     instructions.push(Instruction::Binary(operator.clone(),
                                                                           Operand::Reg(Register::R10),
                                                                           dst.clone()));
                                 },
                                 _ => instructions.push(instruction.clone())
                             }
                         }

                         instructions
                     });

    Function(name.clone(), global, stack_size, instructions)
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
            Operand::Data(name)    => format!("_{name}(%rip)"),
            Operand::Pseudo(_)     => panic!(),
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

#[rustfmt::skip]
fn emit_instruction(code: &mut String, instruction: &Instruction) -> Result<()> {
    match instruction {
        Instruction::DeallocateStack(number) => writeln!(code, "    addq    ${number}, %rsp")?,
        Instruction::Push(src)               => writeln!(code, "    push    {}", src.r8b())?,
        Instruction::Call(name)              => writeln!(code, "    call    _{name}")?,
        Instruction::Cmp(src, dst)           => writeln!(code, "    cmpl    {}, {}", src.r4b(), dst.r4b())?,
        Instruction::Jmp(label)              => writeln!(code, "    jmp     L{}", label)?,
        Instruction::Label(label)            => writeln!(code, "L{}:", label)?,
        Instruction::JmpCC(cc, label)        => writeln!(code, "    j{}     L{}", cc.name(), label)?,
        Instruction::SetCC(cc, dst)          => writeln!(code, "    set{}   {}", cc.name(), dst.r1b())?,
        Instruction::Mov(src, dst)           => writeln!(code, "    movl    {}, {}", src.r4b(), dst.r4b())?,
        Instruction::Unary(operator, dst)    => writeln!(code, "    {}    {}", operator.name(), dst.r4b())?,
        Instruction::AllocateStack(number)   => writeln!(code, "    subq    ${number}, %rsp")?,
        Instruction::Ret                     => writeln!(code, "    movq    %rbp, %rsp\n    popq    %rbp\n    ret")?,
        Instruction::Cdq                     => writeln!(code, "    cdq")?,
        Instruction::Idiv(dst)               => writeln!(code, "    idivl   {}", dst.r4b())?,
        Instruction::Binary(operator, src, dst) => {
            let src_name = match operator {
                BinaryOperator::Leftshift | BinaryOperator::Rightshift => src.r1b(),
                _ => src.r4b(),
            };
            writeln!(code, "    {}  {}, {}", operator.name(), src_name, dst.r4b())?;
        }
    }

    Ok(())
}

fn emit_static_variable(code: &mut String, variable: &StaticVariable) -> Result<()> {
    let StaticVariable(name, global, init) = variable;

    if *global {
        writeln!(code, "    .globl   _{name}")?;
    }
    if *init == 0 {
        writeln!(code, "    .bss")?;
        writeln!(code, "    .balign 4")?;
        writeln!(code, "_{name}:")?;
        writeln!(code, "    .zero 4")?;
    } else {
        writeln!(code, "    .data")?;
        writeln!(code, "    .balign 4")?;
        writeln!(code, "_{name}:")?;
        writeln!(code, "    .long {init}")?;
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
