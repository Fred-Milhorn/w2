//! validate.rs
//!
//! Validate AST for symantic errors.

use anyhow::{Result, anyhow};
use std::collections::HashMap;

use crate::parse::{
    Ast, Block, BlockItem, Const, Declaration, Expression, ForInit, FunctionDeclaration, Identifier, Label, Parameter, Statement,
    StorageClass, Type, UnaryOperator, VariableDeclaration,
};
use crate::utils::temp_name;

#[derive(Debug, Clone, PartialEq)]
pub enum InitialValue {
    Tentative,
    ConstInt(i32),
    ConstLong(i64),
    NoInitializer,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IdentAttrs {
    Function(bool, bool),
    Static(InitialValue, bool),
    Local,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    pub symbol_type: Type,
    pub attrs: IdentAttrs,
}

#[derive(Debug, Clone, PartialEq)]
pub struct SymbolTable(HashMap<Identifier, Symbol>);

impl SymbolTable {
    fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get(&self, name: &String) -> Option<Symbol> {
        self.0.get(name).cloned()
    }

    fn add(&mut self, name: &str, symbol: Symbol) -> Option<Symbol> {
        self.0.insert(name.to_string(), symbol)
    }
}

impl<'a> IntoIterator for &'a SymbolTable {
    type Item = (&'a Identifier, &'a Symbol); // The item type yielded by the iterator
    type IntoIter = std::collections::hash_map::Iter<'a, Identifier, Symbol>; // The iterator type

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter() // Delegate to the HashMap's iter() method
    }
}

#[derive(Debug, Clone, PartialEq)]
struct MapEntry {
    new_name: Identifier,
    has_type: Type,
    from_current_scope: bool,
    has_linkage: bool,
}

impl MapEntry {
    fn new(name: &str, ident_type: &Type, current: bool, linkage: bool) -> Self {
        Self {
            has_type: ident_type.clone(),
            new_name: name.to_string(),
            from_current_scope: current,
            has_linkage: linkage,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct IdentMap(HashMap<String, MapEntry>);

impl IdentMap {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn get(&self, name: &String) -> Option<MapEntry> {
        self.0.get(name).cloned()
    }

    fn add(
        &mut self, name: &str, new_name: &str, ident_type: &Type, from_current_scope: bool, has_linkage: bool,
    ) -> Option<MapEntry> {
        self.0.insert(
            name.to_string(),
            MapEntry::new(new_name, ident_type, from_current_scope, has_linkage),
        )
    }

    fn duplicate(&self) -> IdentMap {
        let mut new_map = IdentMap::new();

        for (name, entry) in self.0.iter() {
            new_map.add(name, &entry.new_name, &entry.has_type, false, false);
        }

        new_map
    }
}

pub fn validate(mut ast: Ast) -> Result<(Ast, SymbolTable)> {
    let Ast::Program(ref mut declarations) = ast;
    let mut ident_map = IdentMap::new();
    let mut symbol_table = SymbolTable::new();

    // Resolve all the variable names in each function
    for declaration in declarations.iter_mut() {
        match declaration {
            Declaration::FunDecl(function_declaration) => {
                *declaration = Declaration::FunDecl(resolve_function(function_declaration, &mut ident_map)?);
            }
            Declaration::VarDecl(variable_declaration) => {
                resolve_file_scope_variables(variable_declaration, &mut ident_map);
            }
        }
    }

    // Label all the loops, breaks, continues
    for declaration in declarations.iter_mut() {
        if let Declaration::FunDecl(function_declaration) = declaration {
            *declaration = Declaration::FunDecl(label_loops(function_declaration, &None)?);
        }
    }

    // Typecheck all declarations, definitions, and variables
    for declaration in declarations.iter_mut() {
        *declaration = match declaration {
            Declaration::FunDecl(function_declaration) => {
                Declaration::FunDecl(typecheck_function(function_declaration, &mut symbol_table)?)
            }
            Declaration::VarDecl(variable_declaration) => {
                Declaration::VarDecl(typecheck_file_scope_variable(variable_declaration, &mut symbol_table)?)
            }
        }
    }

    Ok((ast, symbol_table))
}

fn resolve_file_scope_variables(declaration: &VariableDeclaration, ident_map: &mut IdentMap) {
    let VariableDeclaration(name, _, var_type, _) = declaration;

    ident_map.add(name, name, var_type, true, true);
}

fn resolve_parameter(parameter: &Parameter, ident_map: &mut IdentMap) -> Result<Parameter> {
    if let Some(entry) = ident_map.get(&parameter.name) {
        if entry.from_current_scope {
            return Err(anyhow!(
                "resolve_declaration: duplicate declaration of variable '{parameter:?}'"
            ));
        }
    }

    let unique_name = temp_name(&parameter.name);
    ident_map.add(&parameter.name, &unique_name, &parameter.type_of, true, false);

    Ok(Parameter {
        name: unique_name,
        type_of: parameter.type_of.clone(),
    })
}

fn resolve_function(declaration: &FunctionDeclaration, ident_map: &mut IdentMap) -> Result<FunctionDeclaration> {
    let FunctionDeclaration(name, opt_params, opt_body, fn_type, opt_storage_class) = declaration;

    if let Some(entry) = ident_map.get(name) {
        if entry.from_current_scope && !entry.has_linkage {
            return Err(anyhow!("resolve_function: duplicate function declaration: '{name}'"));
        }
    }
    ident_map.add(name, name, fn_type, true, true);

    let mut inner_map = ident_map.duplicate();
    let new_params = opt_params
        .as_ref()
        .map(|parameters| {
            parameters
                .iter()
                .map(|parameter| resolve_parameter(parameter, &mut inner_map))
                .collect::<Result<Vec<_>>>()
        })
        .transpose()?;
    let new_body = opt_body
        .as_ref()
        .map(|body| resolve_block(body, &mut inner_map))
        .transpose()?;

    Ok(FunctionDeclaration(
        name.clone(),
        new_params,
        new_body,
        fn_type.clone(),
        opt_storage_class.clone(),
    ))
}

fn resolve_block(block: &Block, ident_map: &mut IdentMap) -> Result<Block> {
    let mut new_block = Vec::<BlockItem>::new();

    for item in block {
        let new_item = match item {
            BlockItem::D(declaration) => BlockItem::D(match declaration {
                Declaration::FunDecl(fundecl) => match fundecl {
                    FunctionDeclaration(name, _, Some(_), _, _) => {
                        return Err(anyhow!("resolve_block: nested function definitions not allowed: {name:?}"));
                    }
                    FunctionDeclaration(name, _, _, _, Some(StorageClass::Static)) => {
                        return Err(anyhow!("resolve_block: function declarations cannot be static: {name:?}"));
                    }
                    _ => Declaration::FunDecl(resolve_function(fundecl, ident_map)?),
                },
                Declaration::VarDecl(vardecl) => Declaration::VarDecl(resolve_local_variable(vardecl, ident_map)?),
            }),
            BlockItem::S(statement) => BlockItem::S(resolve_statement(statement, ident_map)?),
        };
        new_block.push(new_item);
    }

    Ok(new_block)
}

fn resolve_local_variable(declaration: &VariableDeclaration, ident_map: &mut IdentMap) -> Result<VariableDeclaration> {
    let VariableDeclaration(name, init, var_type, opt_storage_class) = declaration;

    if let Some(entry) = ident_map.get(name) {
        if entry.from_current_scope && !(entry.has_linkage && matches!(opt_storage_class, Some(StorageClass::Extern))) {
            return Err(anyhow!(
                "resolve_local_variable: conflicting local declarations of variable '{name}'"
            ));
        }
    }

    match opt_storage_class {
        Some(StorageClass::Extern) => {
            ident_map.add(name, name, var_type, true, true);
            Ok(declaration.clone())
        }
        _ => {
            let unique_name = temp_name(name);
            ident_map.add(name, &unique_name, var_type, true, false);

            let resolved_init = match init {
                Some(initializer) => Some(resolve_expression(initializer, ident_map)?),
                None => None,
            };

            Ok(VariableDeclaration(
                unique_name,
                resolved_init,
                var_type.clone(),
                opt_storage_class.clone(),
            ))
        }
    }
}

fn resolve_statement(statement: &Statement, ident_map: &IdentMap) -> Result<Statement> {
    let new_statement = match statement {
        Statement::Return(expression) => Statement::Return(resolve_expression(expression, ident_map)?),
        Statement::Expression(expression) => Statement::Expression(resolve_expression(expression, ident_map)?),
        Statement::If(condition, then_part, else_part) => {
            let resolved_condition = resolve_expression(condition, ident_map)?;
            let resolved_then = Box::new(resolve_statement(then_part, ident_map)?);
            let resolved_else = match else_part {
                Some(statement) => Some(Box::new(resolve_statement(statement, ident_map)?)),
                None => None,
            };
            Statement::If(resolved_condition, resolved_then, resolved_else)
        }
        Statement::Compound(block) => {
            let mut new_ident_map = ident_map.duplicate();
            Statement::Compound(resolve_block(block, &mut new_ident_map)?)
        }
        Statement::Break(_) => statement.clone(),
        Statement::Continue(_) => statement.clone(),
        Statement::While(condition, body, label) => {
            let resolved_condition = resolve_expression(condition, ident_map)?;
            let resolved_body = resolve_statement(body, ident_map)?;
            Statement::While(resolved_condition, Box::new(resolved_body), label.clone())
        }
        Statement::DoWhile(body, condition, label) => {
            let resolved_body = resolve_statement(body, ident_map)?;
            let resolved_condition = resolve_expression(condition, ident_map)?;
            Statement::DoWhile(Box::new(resolved_body), resolved_condition, label.clone())
        }
        Statement::For(for_init, condition, post, body, label) => {
            let mut new_ident_map = ident_map.duplicate();
            let resolved_init = resolve_for_init(for_init, &mut new_ident_map)?;
            let resolved_condition = resolve_optional_expression(condition, &new_ident_map)?;
            let resolved_post = resolve_optional_expression(post, &new_ident_map)?;
            let resolved_body = resolve_statement(body, &new_ident_map)?;
            Statement::For(
                resolved_init,
                resolved_condition,
                resolved_post,
                Box::new(resolved_body),
                label.clone(),
            )
        }
        Statement::None => Statement::None,
    };

    Ok(new_statement)
}

fn resolve_optional_expression(optional_expression: &Option<Expression>, ident_map: &IdentMap) -> Result<Option<Expression>> {
    optional_expression
        .as_ref()
        .map(|expression| resolve_expression(expression, ident_map))
        .transpose()
}

fn resolve_for_init(for_init: &ForInit, ident_map: &mut IdentMap) -> Result<ForInit> {
    let resolved_for_init = match for_init {
        ForInit::InitDecl(declaration) => ForInit::InitDecl(resolve_local_variable(declaration, ident_map)?),
        ForInit::InitExp(expression) => ForInit::InitExp(resolve_optional_expression(expression, ident_map)?),
    };

    Ok(resolved_for_init)
}

fn resolve_expression(expression: &Expression, ident_map: &IdentMap) -> Result<Expression> {
    let new_expression = match expression {
        Expression::Cast(target_type, expression, exp_type) => Expression::Cast(
            target_type.clone(),
            Box::new(resolve_expression(expression, ident_map)?),
            exp_type.clone(),
        ),
        Expression::Conditional(condition, then_part, else_part, cond_type) => Expression::Conditional(
            Box::new(resolve_expression(condition, ident_map)?),
            Box::new(resolve_expression(then_part, ident_map)?),
            Box::new(resolve_expression(else_part, ident_map)?),
            cond_type.clone(),
        ),
        Expression::Assignment(left, right, assign_type) => match &**left {
            Expression::Var(_, _) => Expression::Assignment(
                Box::new(resolve_expression(left, ident_map)?),
                Box::new(resolve_expression(right, ident_map)?),
                assign_type.clone(),
            ),
            _ => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
        },
        Expression::CompoundAssignment(operator, left, right, comp_type) => match &**left {
            Expression::Var(_, _) => Expression::CompoundAssignment(
                operator.clone(),
                Box::new(resolve_expression(left, ident_map)?),
                Box::new(resolve_expression(right, ident_map)?),
                comp_type.clone(),
            ),
            _ => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
        },
        Expression::Var(name, _) => match ident_map.get(name) {
            Some(entry) => Expression::Var(entry.new_name, entry.has_type),
            None => return Err(anyhow!("resolve_expression: Undeclared variable: '{name}'")),
        },
        Expression::Unary(operator, dst, unary_type) => {
            let resolved = resolve_expression(dst, ident_map)?;
            if matches!(
                operator,
                UnaryOperator::PreIncrement
                    | UnaryOperator::PreDecrement
                    | UnaryOperator::PostIncrement
                    | UnaryOperator::PostDecrement
            ) && !matches!(resolved, Expression::Var(_, _))
            {
                return Err(anyhow!("resolve_expression: Illegal lvalue: '{dst:?}'"));
            }

            Expression::Unary(operator.clone(), Box::new(resolved), unary_type.clone())
        }
        Expression::Binary(operator, left, right, exp_type) => Expression::Binary(
            operator.clone(),
            Box::new(resolve_expression(left, ident_map)?),
            Box::new(resolve_expression(right, ident_map)?),
            exp_type.clone(),
        ),
        Expression::FunctionCall(name, opt_args, fun_type) => match ident_map.get(name) {
            Some(entry) => {
                let new_name = entry.new_name.clone();
                let new_args = match opt_args {
                    Some(args) => {
                        let mut resolved_args = Vec::<Expression>::new();
                        for arg in args {
                            let resolved_arg = resolve_expression(arg, ident_map)?;
                            resolved_args.push(resolved_arg);
                        }
                        Some(resolved_args)
                    }
                    None => None,
                };

                Expression::FunctionCall(new_name, new_args, fun_type.clone())
            }
            None => return Err(anyhow!("resolve_expression: undeclarated function '{name}'")),
        },
        _ => expression.clone(),
    };

    Ok(new_expression)
}

fn label_statement(statement: &Statement, label: &Option<Label>) -> Result<Statement> {
    let labeled_statement = match statement {
        Statement::If(condition, then_part, else_part) => {
            let labeled_then = Box::new(label_statement(then_part, label)?);
            let labeled_else = match else_part {
                Some(else_branch) => Some(Box::new(label_statement(else_branch, label)?)),
                None => None,
            };
            Statement::If(condition.clone(), labeled_then, labeled_else)
        }
        Statement::Compound(block) => Statement::Compound(label_block(block, label)?),
        Statement::Break(_) => match label {
            Some(name) => Statement::Break(name.clone()),
            None => return Err(anyhow!("break statement outside of loop")),
        },
        Statement::Continue(_) => match label {
            Some(name) => Statement::Continue(name.clone()),
            None => return Err(anyhow!("continue statement outside of loop")),
        },
        Statement::While(condition, body, _) => {
            let while_label = temp_name("while");
            let labeled_body = label_statement(body, &Some(while_label.clone()))?;
            Statement::While(condition.clone(), Box::new(labeled_body), while_label)
        }
        Statement::DoWhile(body, condition, _) => {
            let do_while_label = temp_name("dowhile");
            let labeled_body = label_statement(body, &Some(do_while_label.clone()))?;
            Statement::DoWhile(Box::new(labeled_body), condition.clone(), do_while_label)
        }
        Statement::For(for_init, condition, post, body, _) => {
            let for_label = temp_name("for");
            let labeled_body = label_statement(body, &Some(for_label.clone()))?;
            Statement::For(
                for_init.clone(),
                condition.clone(),
                post.clone(),
                Box::new(labeled_body),
                for_label,
            )
        }
        statement => statement.clone(),
    };

    Ok(labeled_statement)
}

fn label_block(block: &Block, label: &Option<Label>) -> Result<Block> {
    let mut new_block = Vec::<BlockItem>::new();

    for item in block {
        match item {
            BlockItem::D(_) => {
                new_block.push(item.clone());
            }
            BlockItem::S(statement) => {
                let labeled_statement = label_statement(statement, label)?;
                new_block.push(BlockItem::S(labeled_statement));
            }
        }
    }

    Ok(new_block)
}

fn label_loops(declaration: &FunctionDeclaration, label: &Option<Label>) -> Result<FunctionDeclaration> {
    if let FunctionDeclaration(name, opt_params, Some(body), fun_type, opt_storage_class) = declaration {
        let new_body = label_block(body, label)?;
        return Ok(FunctionDeclaration(
            name.clone(),
            opt_params.clone(),
            Some(new_body),
            fun_type.clone(),
            opt_storage_class.clone(),
        ));
    }

    Ok(declaration.clone())
}

fn typecheck_for_init(for_init: &ForInit, symbol_table: &mut SymbolTable) -> Result<ForInit> {
    let new_for_init = match for_init {
        ForInit::InitDecl(declaration) => {
            if let VariableDeclaration(name, _, _, Some(_)) = declaration {
                return Err(anyhow!("typecheck_for_init: Storage class on for-init not allowed: {name:?}"));
            }
            ForInit::InitDecl(typecheck_local_variable(declaration, symbol_table)?)
        }
        ForInit::InitExp(Some(expression)) => ForInit::InitExp(Some(typecheck_expression(expression, symbol_table)?)),
        _ => for_init.clone(),
    };

    Ok(new_for_init)
}

fn typecheck_statement(statement: &Statement, symbol_table: &mut SymbolTable) -> Result<Statement> {
    let new_statement = match statement {
        Statement::Return(expression) => Statement::Return(typecheck_expression(expression, symbol_table)?),
        Statement::Expression(expression) => Statement::Expression(typecheck_expression(expression, symbol_table)?),
        Statement::If(expression, then_branch, else_branch) => {
            let new_condition = typecheck_expression(expression, symbol_table)?;
            let new_then_branch = typecheck_statement(then_branch, symbol_table)?;
            let new_else_branch = match else_branch {
                Some(branch) => Some(Box::new(typecheck_statement(branch, symbol_table)?)),
                None => None,
            };
            Statement::If(new_condition, Box::new(new_then_branch), new_else_branch)
        }
        Statement::Compound(block) => Statement::Compound(typecheck_block(block, symbol_table)?),
        Statement::While(condition, statement, label) => {
            let new_condition = typecheck_expression(condition, symbol_table)?;
            let new_statement = typecheck_statement(statement, symbol_table)?;
            Statement::While(new_condition, Box::new(new_statement), label.clone())
        }
        Statement::DoWhile(statement, condition, label) => {
            let new_statement = typecheck_statement(statement, symbol_table)?;
            let new_condition = typecheck_expression(condition, symbol_table)?;
            Statement::DoWhile(Box::new(new_statement), new_condition, label.clone())
        }
        Statement::For(for_init, opt_condition, opt_post, body, label) => {
            let new_init = typecheck_for_init(for_init, symbol_table)?;
            let new_condition = match opt_condition {
                Some(condition) => Some(typecheck_expression(condition, symbol_table)?),
                None => None,
            };
            let new_post = match opt_post {
                Some(post) => Some(typecheck_expression(post, symbol_table)?),
                None => None,
            };
            let new_body = typecheck_statement(body, symbol_table)?;
            Statement::For(new_init, new_condition, new_post, Box::new(new_body), label.clone())
        }
        _ => statement.clone(),
    };

    Ok(new_statement)
}

fn typecheck_expression(expression: &Expression, symbol_table: &mut SymbolTable) -> Result<Expression> {
    let new_expression = match expression {
        Expression::FunctionCall(name, opt_args, _) => match symbol_table.get(name) {
            Some(entry) => match &entry.symbol_type {
                Type::FunType(param_types, _) => {
                    if let Some(args) = opt_args {
                        if args.len() != param_types.len() {
                            return Err(anyhow!("Function called with wrong number of arguments: {name:?}"));
                        }
                    }

                    let new_args = match opt_args {
                        Some(args) => args
                            .iter()
                            .map(|arg| typecheck_expression(arg, symbol_table))
                            .collect::<Result<Vec<_>>>()
                            .map(Some),
                        None => Ok(None),
                    }?;

                    Expression::FunctionCall(name.clone(), new_args, entry.symbol_type)
                }
                _ => return Err(anyhow!("Variable used as function name: {name:?}")),
            },
            None => return Err(anyhow!("Undefined function call: {name:?}")),
        },
        Expression::Var(name, _) => match symbol_table.get(name) {
            Some(entry) => {
                if let Type::FunType(_, _) = entry.symbol_type {
                    return Err(anyhow!("Function name used as variable: {name:?}"));
                }
                Expression::Var(name.clone(), entry.symbol_type)
            }
            None => return Err(anyhow!("Undeclared variable in expression: {name:?}")),
        },
        Expression::Assignment(lvalue, expression, assign_type) => Expression::Assignment(
            Box::new(typecheck_expression(lvalue, symbol_table)?),
            Box::new(typecheck_expression(expression, symbol_table)?),
            assign_type.clone(),
        ),
        Expression::Unary(operator, expression, unary_type) => Expression::Unary(
            operator.clone(),
            Box::new(typecheck_expression(expression, symbol_table)?),
            unary_type.clone(),
        ),
        Expression::Binary(operator, lhs, rhs, binary_type) => Expression::Binary(
            operator.clone(),
            Box::new(typecheck_expression(lhs, symbol_table)?),
            Box::new(typecheck_expression(rhs, symbol_table)?),
            binary_type.clone(),
        ),
        Expression::CompoundAssignment(operator, lvalue, rhs, comp_type) => Expression::CompoundAssignment(
            operator.clone(),
            Box::new(typecheck_expression(lvalue, symbol_table)?),
            Box::new(typecheck_expression(rhs, symbol_table)?),
            comp_type.clone(),
        ),
        Expression::Conditional(condition, then_branch, else_branch, cond_type) => Expression::Conditional(
            Box::new(typecheck_expression(condition, symbol_table)?),
            Box::new(typecheck_expression(then_branch, symbol_table)?),
            Box::new(typecheck_expression(else_branch, symbol_table)?),
            cond_type.clone(),
        ),
        Expression::Cast(target_type, cast_exp, _cast_type) => Expression::Cast(
            target_type.clone(),
            Box::new(typecheck_expression(cast_exp, symbol_table)?),
            target_type.clone(),
        ),
        Expression::Constant(const_value, _const_type) => {
            let new_type = match const_value {
                Const::ConstInt(_) => Type::Int,
                Const::ConstLong(_) => Type::Long,
            };
            Expression::Constant(const_value.clone(), new_type)
        }
    };

    Ok(new_expression)
}

fn typecheck_decl_stmt(item: &BlockItem, symbol_table: &mut SymbolTable) -> Result<BlockItem> {
    let new_item = match item {
        BlockItem::D(declaration) => match declaration {
            Declaration::VarDecl(vardecl) => BlockItem::D(Declaration::VarDecl(typecheck_local_variable(vardecl, symbol_table)?)),
            Declaration::FunDecl(fundecl) => BlockItem::D(Declaration::FunDecl(typecheck_function(fundecl, symbol_table)?)),
        },
        BlockItem::S(statement) => BlockItem::S(typecheck_statement(statement, symbol_table)?),
    };

    Ok(new_item)
}

fn typecheck_block(block: &Block, symbol_table: &mut SymbolTable) -> Result<Block> {
    let new_block = block
        .iter()
        .map(|item| typecheck_decl_stmt(item, symbol_table))
        .collect::<Result<Vec<_>>>()?;

    Ok(new_block)
}

fn typecheck_local_variable(declaration: &VariableDeclaration, symbol_table: &mut SymbolTable) -> Result<VariableDeclaration> {
    let VariableDeclaration(name, init, var_type, opt_storage_class) = declaration;

    let new_declaration = match opt_storage_class {
        Some(StorageClass::Extern) => {
            if init.is_some() {
                return Err(anyhow!(
                    "typecheck_local_variable: Initializer on local extern variable declaration: {name:?}"
                ));
            }
            match symbol_table.get(name) {
                Some(entry) => {
                    if entry.symbol_type != *var_type {
                        return Err(anyhow!(
                            "typecheck_local_variable: function redeclared as variable: {entry:?}"
                        ));
                    }
                }
                None => {
                    symbol_table.add(
                        name,
                        Symbol {
                            symbol_type: var_type.clone(),
                            attrs: IdentAttrs::Static(InitialValue::NoInitializer, true),
                        },
                    );
                }
            }
            declaration.clone()
        }
        Some(StorageClass::Static) => {
            let initial_value = match init {
                Some(Expression::Constant(numeric, _)) => match numeric {
                    Const::ConstInt(number) => InitialValue::ConstInt(*number),
                    Const::ConstLong(number) => InitialValue::ConstLong(*number),
                },
                None => match var_type {
                    Type::Int => InitialValue::ConstInt(0),
                    Type::Long => InitialValue::ConstLong(0),
                    _ => todo!(),
                },
                _ => {
                    return Err(anyhow!(
                        "typecheck_local_variable: Non-constant initializer on local static variable: {name:?}"
                    ));
                }
            };
            symbol_table.add(
                name,
                Symbol {
                    symbol_type: var_type.clone(),
                    attrs: IdentAttrs::Static(initial_value, false),
                },
            );
            declaration.clone()
        }
        _ => {
            symbol_table.add(
                name,
                Symbol {
                    symbol_type: var_type.clone(),
                    attrs: IdentAttrs::Local,
                },
            );
            let new_init = init
                .as_ref()
                .map(|expression| typecheck_expression(expression, symbol_table))
                .transpose()?;

            VariableDeclaration(name.clone(), new_init, var_type.clone(), opt_storage_class.clone())
        }
    };

    Ok(new_declaration)
}

fn typecheck_file_scope_variable(
    declaration: &VariableDeclaration, symbol_table: &mut SymbolTable,
) -> Result<VariableDeclaration> {
    let VariableDeclaration(name, init, var_type, opt_storage_class) = declaration;

    let mut initial_value = match init {
        Some(Expression::Constant(numeric, _)) => match numeric {
            Const::ConstInt(number) => InitialValue::ConstInt(*number),
            Const::ConstLong(number) => InitialValue::ConstLong(*number),
        },
        None => match opt_storage_class {
            Some(StorageClass::Extern) => InitialValue::NoInitializer,
            _ => InitialValue::Tentative,
        },
        _ => return Err(anyhow!("typecheck_file_scope_variable: non-constant initializer: {init:?}")),
    };
    let mut global = !matches!(opt_storage_class, Some(StorageClass::Static));

    if let Some(entry) = symbol_table.get(name) {
        if !matches!(entry.symbol_type, Type::Int | Type::Long) {
            return Err(anyhow!("Function redeclared as variable: '{entry:?}'"));
        }
        let mut entry_is_global = false;
        let mut entry_initial_value = InitialValue::NoInitializer;
        if let IdentAttrs::Static(ref entry_value, entry_scope) = entry.attrs {
            entry_is_global = entry_scope;
            entry_initial_value = entry_value.clone();
        }
        if matches!(opt_storage_class, Some(StorageClass::Extern)) {
            global = entry_is_global;
        } else if global != entry_is_global {
            return Err(anyhow!(
                "typecheck_file_scope_variable: conflicting variable linkage: {entry:?}"
            ));
        }
        if entry.symbol_type != *var_type {
            return Err(anyhow!(
                "typecheck_file_scope_variable: for variable {:?}, conflicting file scope variable types: {:?} vs. {:?}",
                name,
                entry.symbol_type,
                *var_type,
            ));
        }
        if matches!(entry_initial_value, InitialValue::ConstInt(_) | InitialValue::ConstLong(_)) {
            if matches!(initial_value, InitialValue::ConstInt(_) | InitialValue::ConstLong(_)) {
                return Err(anyhow!(
                    "typecheck_file_scope_variable: conflicting file scope variable definitions: {entry:?}"
                ));
            } else {
                initial_value = entry_initial_value;
            }
        } else if !matches!(initial_value, InitialValue::ConstInt(_) | InitialValue::ConstLong(_))
            && matches!(entry_initial_value, InitialValue::Tentative)
        {
            initial_value = InitialValue::Tentative;
        }
    }

    let new_symbol = Symbol {
        symbol_type: var_type.clone(),
        attrs: IdentAttrs::Static(initial_value, global),
    };
    symbol_table.add(name, new_symbol);

    Ok(declaration.clone())
}

pub fn equal_types(a: &Type, b: &Type) -> bool {
    match (a, b) {
        (Type::Int, Type::Int) => true,
        (Type::Long, Type::Long) => true,
        (Type::None, Type::None) => true,
        (Type::FunType(params_a, ret_a), Type::FunType(params_b, ret_b)) => {
            params_a.len() == params_b.len()
                && equal_types(ret_a, ret_b)
                && params_a.iter().zip(params_b.iter()).all(|(p, q)| equal_types(p, q))
        }
        _ => false,
    }
}

fn typecheck_function(declaration: &FunctionDeclaration, symbol_table: &mut SymbolTable) -> Result<FunctionDeclaration> {
    let FunctionDeclaration(name, parameters, body, function_type, opt_storage_class) = declaration;

    let mut global = !matches!(opt_storage_class, Some(StorageClass::Static));
    let mut already_defined = false;

    if let Some(entry) = symbol_table.get(name) {
        if !equal_types(&entry.symbol_type, function_type) {
            return Err(anyhow!("Incompatible function declarations: '{entry:?}'"));
        }
        let mut entry_is_global = false;
        if let IdentAttrs::Function(entry_defined, entry_scope) = entry.attrs {
            already_defined = entry_defined;
            entry_is_global = entry_scope;
        }
        if already_defined && body.is_some() {
            return Err(anyhow!("Function defined more than once: {entry:?}'"));
        }
        if matches!(opt_storage_class, Some(StorageClass::Static)) && entry_is_global {
            return Err(anyhow!("Static function declaration follows non-static: {entry:?}"));
        }
        global = entry_is_global;
    }

    symbol_table.add(
        name,
        Symbol {
            symbol_type: function_type.clone(),
            attrs: IdentAttrs::Function(already_defined || body.is_some(), global),
        },
    );

    let new_block = match body {
        Some(block) => {
            if let Some(params) = parameters {
                for param in params {
                    symbol_table.add(
                        &param.name,
                        Symbol {
                            symbol_type: param.type_of.clone(),
                            attrs: IdentAttrs::Local,
                        },
                    );
                }
            }
            Some(typecheck_block(block, symbol_table)?)
        }
        None => None,
    };
    let new_decl = FunctionDeclaration(
        name.clone(),
        parameters.clone(),
        new_block,
        function_type.clone(),
        opt_storage_class.clone(),
    );

    Ok(new_decl)
}
