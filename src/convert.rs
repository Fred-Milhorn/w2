//! convert.rs
//!
//! Type conversion functions.

use crate::parse::{Const, Expression, Type};
use crate::validate::{InitialValue, StaticInit};
use anyhow::{Result, anyhow};

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

pub fn convert_static_init(name: &str, var_type: &Type, init: &Option<Expression>) -> Result<InitialValue> {
    let initial_value = match init {
        Some(Expression::Constant(numeric, _)) => match numeric {
            Const::ConstInt(number) => InitialValue::Initial(StaticInit::IntInit(*number)),
            Const::ConstLong(number) => {
                let initializer = match var_type {
                    Type::Int => InitialValue::Initial(StaticInit::IntInit(*number as i32)),
                    Type::Long => InitialValue::Initial(StaticInit::LongInit(*number)),
                    _ => {
                        return Err(anyhow!(
                            "convert_static_init: unexpected type {var_type:?} for variable {name:?}"
                        ));
                    }
                };
                initializer
            }
        },
        None => match var_type {
            Type::Int => InitialValue::Initial(StaticInit::IntInit(0)),
            Type::Long => InitialValue::Initial(StaticInit::LongInit(0)),
            _ => {
                return Err(anyhow!(
                    "convert_static_init: unexpected type {var_type:?} for variable {name:?}"
                ));
            }
        },
        _ => {
            return Err(anyhow!(
                "typecheck_local_variable: Non-constant initializer on local static variable: {name:?}"
            ));
        }
    };

    Ok(initial_value)
}
