//! convert.rs
//!
//! Type conversion functions.

use crate::code::AssemblyType;
use crate::parse::{Const, Expression, Type};
use crate::tacky::Val;
use crate::validate::{InitialValue, StaticInit, get_symbol};

use anyhow::{Result, bail};

pub fn get_common_type(type1: Type, type2: Type) -> Type {
    if type1 == type2 {
        return type1;
    }
    Type::Long
}

pub fn convert_to(expression: Expression, exp_type: Type) -> Expression {
    if expression.get_type() == exp_type {
        return expression;
    }
    Expression::Cast(exp_type.clone(), Box::new(expression), exp_type.clone())
}

pub fn convert_static_init(
    name: &str, var_type: &Type, init: &Option<Expression>
) -> Result<InitialValue> {
    let initial_value = match init {
        Some(Expression::Constant(numeric, _)) => match numeric {
            Const::ConstInt(number) => InitialValue::Initial(StaticInit::IntInit(*number)),
            Const::ConstLong(number) => match var_type {
                Type::Int => InitialValue::Initial(StaticInit::IntInit(*number)),
                Type::Long => InitialValue::Initial(StaticInit::LongInit(*number)),
                _ => {
                    bail!(
                        "convert_static_init: unexpected type {var_type:?} for variable {name:?}"
                    );
                }
            }
        },
        None => match var_type {
            Type::Int => InitialValue::Initial(StaticInit::IntInit(0)),
            Type::Long => InitialValue::Initial(StaticInit::LongInit(0)),
            _ => {
                bail!("convert_static_init: unexpected type {var_type:?} for variable {name:?}");
            }
        },
        _ => {
            bail!(
                "typecheck_local_variable: Non-constant initializer on local static variable: {name:?}"
            );
        }
    };

    Ok(initial_value)
}

pub fn val_type(value: &Val) -> Result<AssemblyType> {
    let atype = match value {
        Val::Constant(Const::ConstInt(_)) => AssemblyType::Longword,
        Val::Constant(Const::ConstLong(_)) => AssemblyType::Quadword,
        Val::Var(identifier) => match get_symbol(identifier) {
            Some(entry) => match entry.symbol_type {
                Type::Int => AssemblyType::Longword,
                Type::Long => AssemblyType::Quadword,
                _ => bail!("val_type: Unexpected type for symbol: {identifier:?} {entry:?}")
            },
            None => bail!("val_type: symbol {identifier:?} not found")
        }
    };

    Ok(atype)
}
