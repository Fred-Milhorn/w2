//! arm64.rs
//!
//! Generate macOS arm64 assembly from Tacky IR.

use crate::code::AssemblyType;
use crate::convert::val_type;
use crate::parse;
use crate::parse::Identifier;
use crate::tacky;
use crate::validate::{BACKEND, BackendSymbol, IdentAttrs, SYMBOLS, StaticInit, get_backend};

use anyhow::{Result, bail};
use std::collections::HashMap;
use std::fmt::Write as _;

const TMP0: u8 = 9;
const TMP1: u8 = 10;
const TMP2: u8 = 11;
const TMP3: u8 = 12;
const ADDR: u8 = 15;

#[derive(Debug, Clone, PartialEq)]
enum Storage {
    Stack(i32),
    Data(Identifier)
}

#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    name:         Identifier,
    global:       bool,
    stack_size:   i32,
    return_label: Identifier,
    body:         Option<Vec<String>>
}

#[derive(Debug, Clone, PartialEq)]
pub struct StaticVariable(Identifier, bool, usize, StaticInit);

#[derive(Debug, Clone, PartialEq)]
pub enum Definition {
    FunDef(Function),
    VarDef(StaticVariable)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Assembly {
    Program(Vec<Definition>)
}

fn align_to(value: i32, alignment: i32) -> i32 {
    if value == 0 { 0 } else { ((value + alignment - 1) / alignment) * alignment }
}

fn add_sub_large(lines: &mut Vec<String>, op: &str, dst: &str, src: &str, mut amount: i32) {
    if amount == 0 {
        return;
    }

    let mut first = true;
    while amount > 0 {
        let chunk = amount.min(4095);
        let current_src = if first { src.to_string() } else { dst.to_string() };
        lines.push(format!("    {op} {dst}, {current_src}, #{chunk}"));
        amount -= chunk;
        first = false;
    }
}

fn address_from_base(lines: &mut Vec<String>, base: &str, offset: i32) {
    let addr = format!("x{ADDR}");
    lines.push(format!("    mov {addr}, {base}"));
    if offset > 0 {
        add_sub_large(lines, "add", &addr, &addr, offset);
    } else if offset < 0 {
        add_sub_large(lines, "sub", &addr, &addr, -offset);
    }
}

fn width_suffix(atype: &AssemblyType) -> &'static str {
    match atype {
        AssemblyType::Longword => "w",
        AssemblyType::Quadword => "x"
    }
}

fn reg(index: u8, atype: &AssemblyType) -> String {
    format!("{}{index}", width_suffix(atype))
}

fn emit_load_imm(lines: &mut Vec<String>, index: u8, atype: &AssemblyType, value: i64) {
    match atype {
        AssemblyType::Longword => {
            let value = value as i32 as u32;
            let r = format!("w{index}");
            let low = value & 0xFFFF;
            let hi = (value >> 16) & 0xFFFF;
            lines.push(format!("    movz {r}, #{low}"));
            if hi != 0 {
                lines.push(format!("    movk {r}, #{hi}, lsl #16"));
            }
        },
        AssemblyType::Quadword => {
            let value = value as u64;
            let r = format!("x{index}");
            let p0 = value & 0xFFFF;
            let p1 = (value >> 16) & 0xFFFF;
            let p2 = (value >> 32) & 0xFFFF;
            let p3 = (value >> 48) & 0xFFFF;
            lines.push(format!("    movz {r}, #{p0}"));
            if p1 != 0 {
                lines.push(format!("    movk {r}, #{p1}, lsl #16"));
            }
            if p2 != 0 {
                lines.push(format!("    movk {r}, #{p2}, lsl #32"));
            }
            if p3 != 0 {
                lines.push(format!("    movk {r}, #{p3}, lsl #48"));
            }
        }
    }
}

fn load_from_data(lines: &mut Vec<String>, dst: u8, atype: &AssemblyType, name: &str) {
    let addr = format!("x{ADDR}");
    let dst = reg(dst, atype);
    lines.push(format!("    adrp {addr}, _{name}@PAGE"));
    lines.push(format!("    ldr {dst}, [{addr}, _{name}@PAGEOFF]"));
}

fn store_to_data(lines: &mut Vec<String>, src: u8, atype: &AssemblyType, name: &str) {
    let addr = format!("x{ADDR}");
    let src = reg(src, atype);
    lines.push(format!("    adrp {addr}, _{name}@PAGE"));
    lines.push(format!("    str {src}, [{addr}, _{name}@PAGEOFF]"));
}

fn load_from_stack(lines: &mut Vec<String>, dst: u8, atype: &AssemblyType, offset: i32) {
    let dst = reg(dst, atype);
    address_from_base(lines, "x29", offset);
    lines.push(format!("    ldr {dst}, [x{ADDR}]"));
}

fn store_to_stack(lines: &mut Vec<String>, src: u8, atype: &AssemblyType, offset: i32) {
    let src = reg(src, atype);
    address_from_base(lines, "x29", offset);
    lines.push(format!("    str {src}, [x{ADDR}]"));
}

fn load_from_storage(lines: &mut Vec<String>, dst: u8, atype: &AssemblyType, storage: &Storage) {
    match storage {
        Storage::Data(name) => load_from_data(lines, dst, atype, name),
        Storage::Stack(offset) => load_from_stack(lines, dst, atype, *offset)
    }
}

fn store_to_storage(lines: &mut Vec<String>, src: u8, atype: &AssemblyType, storage: &Storage) {
    match storage {
        Storage::Data(name) => store_to_data(lines, src, atype, name),
        Storage::Stack(offset) => store_to_stack(lines, src, atype, *offset)
    }
}

fn load_from_value(
    lines: &mut Vec<String>, value: &tacky::Val, dst: u8, slots: &HashMap<String, i32>
) -> Result<AssemblyType> {
    let atype = val_type(value)?;
    match value {
        tacky::Val::Constant(number) => match number {
            parse::Const::ConstInt(value) | parse::Const::ConstLong(value) => {
                emit_load_imm(lines, dst, &atype, *value);
            }
        },
        tacky::Val::Var(name) => {
            let storage = resolve_storage(name, slots)?;
            load_from_storage(lines, dst, &atype, &storage);
        }
    }
    Ok(atype)
}

fn store_to_value(
    lines: &mut Vec<String>, src: u8, atype: &AssemblyType, value: &tacky::Val,
    slots: &HashMap<String, i32>
) -> Result<()> {
    if let tacky::Val::Var(name) = value {
        let storage = resolve_storage(name, slots)?;
        store_to_storage(lines, src, atype, &storage);
        Ok(())
    } else {
        bail!("Expected destination variable, got {value:?}")
    }
}

fn resolve_storage(name: &str, slots: &HashMap<String, i32>) -> Result<Storage> {
    match get_backend(name) {
        Some(BackendSymbol::ObjEntry(_, true)) => Ok(Storage::Data(name.to_string())),
        _ => match slots.get(name) {
            Some(offset) => Ok(Storage::Stack(*offset)),
            None => bail!("No stack slot for variable {name:?}")
        }
    }
}

fn is_data_symbol(name: &str) -> bool {
    matches!(get_backend(name), Some(BackendSymbol::ObjEntry(_, true)))
}

fn add_local_if_needed(name: &str, locals: &mut Vec<String>) {
    if !is_data_symbol(name) && !locals.iter().any(|entry| entry == name) {
        locals.push(name.to_string());
    }
}

fn collect_locals(function: &tacky::Function) -> Vec<String> {
    let tacky::Function(_, _, params, body) = function;
    let mut locals: Vec<String> = Vec::new();

    if let Some(params) = params {
        for param in params {
            add_local_if_needed(&param.name, &mut locals);
        }
    }

    if let Some(body) = body {
        for instruction in body {
            match instruction {
                tacky::Instruction::SignExtend(src, dst)
                | tacky::Instruction::Truncate(src, dst)
                | tacky::Instruction::Copy(src, dst) => {
                    if let tacky::Val::Var(name) = src {
                        add_local_if_needed(name, &mut locals);
                    }
                    if let tacky::Val::Var(name) = dst {
                        add_local_if_needed(name, &mut locals);
                    }
                },
                tacky::Instruction::Return(value)
                | tacky::Instruction::JumpIfZero(value, _)
                | tacky::Instruction::JumpIfNotZero(value, _) => {
                    if let tacky::Val::Var(name) = value {
                        add_local_if_needed(name, &mut locals);
                    }
                },
                tacky::Instruction::Unary(_, src, dst) => {
                    if let tacky::Val::Var(name) = src {
                        add_local_if_needed(name, &mut locals);
                    }
                    if let tacky::Val::Var(name) = dst {
                        add_local_if_needed(name, &mut locals);
                    }
                },
                tacky::Instruction::Binary(_, src1, src2, dst) => {
                    if let tacky::Val::Var(name) = src1 {
                        add_local_if_needed(name, &mut locals);
                    }
                    if let tacky::Val::Var(name) = src2 {
                        add_local_if_needed(name, &mut locals);
                    }
                    if let tacky::Val::Var(name) = dst {
                        add_local_if_needed(name, &mut locals);
                    }
                },
                tacky::Instruction::FunCall(_, args, dst) => {
                    if let Some(args) = args {
                        for arg in args {
                            if let tacky::Val::Var(name) = arg {
                                add_local_if_needed(name, &mut locals);
                            }
                        }
                    }
                    if let tacky::Val::Var(name) = dst {
                        add_local_if_needed(name, &mut locals);
                    }
                },
                tacky::Instruction::Jump(_) | tacky::Instruction::Label(_) => ()
            }
        }
    }

    locals
}

fn assign_slots(locals: &[String]) -> HashMap<String, i32> {
    let mut slots: HashMap<String, i32> = HashMap::new();
    let mut offset = -8;
    for name in locals {
        slots.insert(name.clone(), offset);
        offset -= 8;
    }
    slots
}

fn emit_cmp_set(
    lines: &mut Vec<String>, cond: &str, src1: &tacky::Val, src2: &tacky::Val, dst: &tacky::Val,
    slots: &HashMap<String, i32>
) -> Result<()> {
    let lhs_type = load_from_value(lines, src1, TMP0, slots)?;
    let _ = load_from_value(lines, src2, TMP1, slots)?;
    lines.push(format!("    cmp {}, {}", reg(TMP0, &lhs_type), reg(TMP1, &lhs_type)));
    lines.push(format!("    cset w{TMP2}, {cond}"));

    let dst_type = val_type(dst)?;
    if matches!(dst_type, AssemblyType::Quadword) {
        lines.push(format!("    sxtw x{TMP2}, w{TMP2}"));
    }
    store_to_value(lines, TMP2, &dst_type, dst, slots)
}

fn emit_binary(
    lines: &mut Vec<String>, operator: &parse::BinaryOperator, src1: &tacky::Val,
    src2: &tacky::Val, dst: &tacky::Val, slots: &HashMap<String, i32>
) -> Result<()> {
    match operator {
        parse::BinaryOperator::Equal => return emit_cmp_set(lines, "eq", src1, src2, dst, slots),
        parse::BinaryOperator::NotEqual => {
            return emit_cmp_set(lines, "ne", src1, src2, dst, slots);
        },
        parse::BinaryOperator::LessThan => {
            return emit_cmp_set(lines, "lt", src1, src2, dst, slots);
        },
        parse::BinaryOperator::LessOrEqual => {
            return emit_cmp_set(lines, "le", src1, src2, dst, slots);
        },
        parse::BinaryOperator::GreaterThan => {
            return emit_cmp_set(lines, "gt", src1, src2, dst, slots);
        },
        parse::BinaryOperator::GreaterOrEqual => {
            return emit_cmp_set(lines, "ge", src1, src2, dst, slots);
        },
        parse::BinaryOperator::And | parse::BinaryOperator::Or => {
            bail!("Unexpected short-circuit operator in binary instruction: {operator:?}");
        },
        _ => ()
    }

    let atype = load_from_value(lines, src1, TMP0, slots)?;
    let _ = load_from_value(lines, src2, TMP1, slots)?;

    let r0 = reg(TMP0, &atype);
    let r1 = reg(TMP1, &atype);
    let rd = reg(TMP2, &atype);

    match operator {
        parse::BinaryOperator::Plus => lines.push(format!("    add {rd}, {r0}, {r1}")),
        parse::BinaryOperator::Minus => lines.push(format!("    sub {rd}, {r0}, {r1}")),
        parse::BinaryOperator::Multiply => lines.push(format!("    mul {rd}, {r0}, {r1}")),
        parse::BinaryOperator::Divide => lines.push(format!("    sdiv {rd}, {r0}, {r1}")),
        parse::BinaryOperator::Remainder => {
            let rq = reg(TMP3, &atype);
            lines.push(format!("    sdiv {rq}, {r0}, {r1}"));
            lines.push(format!("    msub {rd}, {rq}, {r1}, {r0}"));
        },
        parse::BinaryOperator::Leftshift => lines.push(format!("    lsl {rd}, {r0}, {r1}")),
        parse::BinaryOperator::Rightshift => lines.push(format!("    asr {rd}, {r0}, {r1}")),
        parse::BinaryOperator::BitAnd => lines.push(format!("    and {rd}, {r0}, {r1}")),
        parse::BinaryOperator::BitXor => lines.push(format!("    eor {rd}, {r0}, {r1}")),
        parse::BinaryOperator::BitOr => lines.push(format!("    orr {rd}, {r0}, {r1}")),
        _ => bail!("Unsupported binary operator: {operator:?}")
    }

    store_to_value(lines, TMP2, &atype, dst, slots)
}

fn emit_stack_store_for_call(
    lines: &mut Vec<String>, reg_index: u8, atype: &AssemblyType, offset: i32
) {
    let src = reg(reg_index, atype);
    if offset <= 4095 {
        lines.push(format!("    str {src}, [sp, #{offset}]"));
    } else {
        address_from_base(lines, "sp", offset);
        lines.push(format!("    str {src}, [x{ADDR}]"));
    }
}

fn emit_call(
    lines: &mut Vec<String>, name: &str, args: &Option<tacky::Arguments>, dst: &tacky::Val,
    slots: &HashMap<String, i32>
) -> Result<()> {
    if let Some(args) = args {
        for (index, arg) in args.iter().take(8).enumerate() {
            let _ = load_from_value(lines, arg, index as u8, slots)?;
        }

        let stack_arg_count = args.len().saturating_sub(8);
        let stack_bytes = align_to((stack_arg_count as i32) * 8, 16);
        if stack_bytes > 0 {
            add_sub_large(lines, "sub", "sp", "sp", stack_bytes);
            for (slot, arg) in args.iter().skip(8).enumerate() {
                let atype = load_from_value(lines, arg, TMP0, slots)?;
                emit_stack_store_for_call(lines, TMP0, &atype, (slot as i32) * 8);
            }
        }

        lines.push(format!("    bl _{name}"));

        if stack_bytes > 0 {
            add_sub_large(lines, "add", "sp", "sp", stack_bytes);
        }
    } else {
        lines.push(format!("    bl _{name}"));
    }

    let dst_type = val_type(dst)?;
    store_to_value(lines, 0, &dst_type, dst, slots)
}

fn emit_instruction(
    lines: &mut Vec<String>, instruction: &tacky::Instruction, slots: &HashMap<String, i32>,
    return_label: &str
) -> Result<()> {
    match instruction {
        tacky::Instruction::Return(value) => {
            let _ = load_from_value(lines, value, 0, slots)?;
            lines.push(format!("    b L{return_label}"));
        },
        tacky::Instruction::Unary(parse::UnaryOperator::Not, src, dst) => {
            let src_type = load_from_value(lines, src, TMP0, slots)?;
            lines.push(format!("    cmp {}, #0", reg(TMP0, &src_type)));
            lines.push(format!("    cset w{TMP1}, eq"));

            let dst_type = val_type(dst)?;
            if matches!(dst_type, AssemblyType::Quadword) {
                lines.push(format!("    sxtw x{TMP1}, w{TMP1}"));
            }
            store_to_value(lines, TMP1, &dst_type, dst, slots)?;
        },
        tacky::Instruction::Unary(operator, src, dst) => {
            let atype = load_from_value(lines, src, TMP0, slots)?;
            let src = reg(TMP0, &atype);
            let dst_reg = reg(TMP1, &atype);
            match operator {
                parse::UnaryOperator::Negate => lines.push(format!("    neg {dst_reg}, {src}")),
                parse::UnaryOperator::Complement => lines.push(format!("    mvn {dst_reg}, {src}")),
                parse::UnaryOperator::Not => unreachable!()
            }
            store_to_value(lines, TMP1, &atype, dst, slots)?;
        },
        tacky::Instruction::Binary(operator, src1, src2, dst) => {
            emit_binary(lines, operator, src1, src2, dst, slots)?;
        },
        tacky::Instruction::Copy(src, dst) => {
            let atype = load_from_value(lines, src, TMP0, slots)?;
            store_to_value(lines, TMP0, &atype, dst, slots)?;
        },
        tacky::Instruction::Jump(label) => lines.push(format!("    b L{label}")),
        tacky::Instruction::JumpIfZero(value, label) => {
            let atype = load_from_value(lines, value, TMP0, slots)?;
            lines.push(format!("    cmp {}, #0", reg(TMP0, &atype)));
            lines.push(format!("    b.eq L{label}"));
        },
        tacky::Instruction::JumpIfNotZero(value, label) => {
            let atype = load_from_value(lines, value, TMP0, slots)?;
            lines.push(format!("    cmp {}, #0", reg(TMP0, &atype)));
            lines.push(format!("    b.ne L{label}"));
        },
        tacky::Instruction::Label(label) => lines.push(format!("L{label}:")),
        tacky::Instruction::FunCall(name, args, dst) => emit_call(lines, name, args, dst, slots)?,
        tacky::Instruction::SignExtend(src, dst) => {
            let _ = load_from_value(lines, src, TMP0, slots)?;
            lines.push(format!("    sxtw x{TMP1}, w{TMP0}"));
            store_to_value(lines, TMP1, &AssemblyType::Quadword, dst, slots)?;
        },
        tacky::Instruction::Truncate(src, dst) => {
            let _ = load_from_value(lines, src, TMP0, slots)?;
            lines.push(format!("    mov w{TMP1}, w{TMP0}"));
            store_to_value(lines, TMP1, &AssemblyType::Longword, dst, slots)?;
        }
    }
    Ok(())
}

fn emit_param_moves(
    lines: &mut Vec<String>, params: &Option<parse::Parameters>, slots: &HashMap<String, i32>
) -> Result<()> {
    if let Some(params) = params {
        for (index, param) in params.iter().enumerate() {
            let atype: AssemblyType = param.type_of.clone().into();
            let storage = resolve_storage(&param.name, slots)?;
            if index < 8 {
                store_to_storage(lines, index as u8, &atype, &storage);
            } else {
                let caller_offset = 16 + ((index - 8) as i32 * 8);
                let tmp = reg(TMP0, &atype);
                address_from_base(lines, "x29", caller_offset);
                lines.push(format!("    ldr {tmp}, [x{ADDR}]"));
                store_to_storage(lines, TMP0, &atype, &storage);
            }
        }
    }
    Ok(())
}

fn emit_function(function: &tacky::Function) -> Result<Function> {
    let tacky::Function(name, global, params, body) = function;
    if body.is_none() {
        return Ok(Function {
            name:         name.clone(),
            global:       *global,
            stack_size:   0,
            return_label: format!("ret_{name}"),
            body:         None
        });
    }

    let locals = collect_locals(function);
    let slots = assign_slots(&locals);
    let stack_size = align_to((locals.len() as i32) * 8, 16);
    let return_label = format!("ret_{name}");
    let mut lines: Vec<String> = Vec::new();

    emit_param_moves(&mut lines, params, &slots)?;

    if let Some(body) = body {
        for instruction in body {
            emit_instruction(&mut lines, instruction, &slots, &return_label)?;
        }
    }

    Ok(Function {
        name: name.clone(),
        global: *global,
        stack_size,
        return_label,
        body: Some(lines)
    })
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

fn emit_function_definition(code: &mut String, function: &Function) -> Result<()> {
    if function.body.is_none() {
        return Ok(());
    }

    if function.global {
        writeln!(code, "\n    .globl   _{}", function.name)?;
    }
    writeln!(code, "    .text")?;
    writeln!(code, "_{}:", function.name)?;
    writeln!(code, "    stp x29, x30, [sp, #-16]!")?;
    writeln!(code, "    mov x29, sp")?;

    let mut adjust_lines = Vec::new();
    add_sub_large(&mut adjust_lines, "sub", "sp", "sp", function.stack_size);
    for line in adjust_lines {
        writeln!(code, "{line}")?;
    }

    if let Some(body) = &function.body {
        for line in body {
            writeln!(code, "{line}")?;
        }
    }

    writeln!(code, "L{}:", function.return_label)?;

    let mut restore_lines = Vec::new();
    add_sub_large(&mut restore_lines, "add", "sp", "sp", function.stack_size);
    for line in restore_lines {
        writeln!(code, "{line}")?;
    }

    writeln!(code, "    ldp x29, x30, [sp], #16")?;
    writeln!(code, "    ret")?;

    Ok(())
}

fn populate_backend_table() {
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
}

pub fn generate(tacky: &tacky::Tacky) -> Result<Assembly> {
    populate_backend_table();

    let tacky::Tacky::Program(declarations) = tacky;
    let mut definitions: Vec<Definition> = Vec::new();

    for declaration in declarations {
        match declaration {
            tacky::Definition::FunDef(function) => {
                definitions.push(Definition::FunDef(emit_function(function)?));
            },
            tacky::Definition::VarDef(tacky::StaticVariable(name, global, var_type, init)) => {
                let alignment = match AssemblyType::from(var_type.clone()) {
                    AssemblyType::Longword => 4,
                    AssemblyType::Quadword => 8
                };
                definitions.push(Definition::VarDef(StaticVariable(
                    name.to_string(),
                    *global,
                    alignment,
                    init.clone()
                )));
            }
        }
    }

    Ok(Assembly::Program(definitions))
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
            Definition::FunDef(function) => emit_function_definition(&mut code, function)?,
            Definition::VarDef(variable) => emit_static_variable(&mut code, variable)?
        }
    }

    Ok(code)
}
