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

#[cfg(test)]
mod tests {
    use super::{convert_static_init, convert_to, get_common_type};
    use crate::parse::{Const, Expression, Type};
    use crate::validate::{InitialValue, StaticInit};

    #[test]
    fn common_type_prefers_long_when_types_differ() {
        assert_eq!(get_common_type(Type::Int, Type::Int), Type::Int);
        assert_eq!(get_common_type(Type::Int, Type::Long), Type::Long);
    }

    #[test]
    fn convert_to_is_noop_for_matching_type() {
        let expression = Expression::Constant(Const::ConstInt(7), Type::Int);
        let converted = convert_to(expression.clone(), Type::Int);
        assert_eq!(converted, expression);
    }

    #[test]
    fn convert_to_wraps_expression_when_type_changes() {
        let expression = Expression::Constant(Const::ConstInt(1), Type::Int);
        let converted = convert_to(expression.clone(), Type::Long);

        match converted {
            Expression::Cast(Type::Long, inner, Type::Long) => assert_eq!(*inner, expression),
            _ => panic!("expected cast to long"),
        }
    }

    #[test]
    fn convert_static_init_defaults_to_zero() {
        let initial = convert_static_init("x", &Type::Long, &None).expect("expected success");
        assert_eq!(initial, InitialValue::Initial(StaticInit::LongInit(0)));
    }

    #[test]
    fn convert_static_init_rejects_non_constant_initializer() {
        let init = Some(Expression::Var("x".to_string(), Type::Int));
        let err = convert_static_init("x", &Type::Int, &init).expect_err("expected failure");
        assert!(err.to_string().contains("Non-constant initializer"));
    }
}
