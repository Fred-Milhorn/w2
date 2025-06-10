//! validate.rs
//!
//! Validate AST for symantic errors.

use anyhow::{anyhow, Result};
use std::collections::HashMap;

use crate::parse::{
    Ast, Block, BlockItem, Declaration, Expression, ForInit, FunctionDeclaration, Identifier, Label, Statement, StorageClass,
    UnaryOperator, VariableDeclaration,
};
use crate::utils::temp_name;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    FunType(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum InitialValue {
    Tentative,
    Initial(i32),
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
    from_current_scope: bool,
    has_linkage: bool,
}

impl MapEntry {
    fn new(name: &str, current: bool, linkage: bool) -> Self {
        Self {
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

    fn add(&mut self, name: &str, new_name: &str, from_current_scope: bool, has_linkage: bool) -> Option<MapEntry> {
        self.0
            .insert(name.to_string(), MapEntry::new(new_name, from_current_scope, has_linkage))
    }

    fn duplicate(&self) -> IdentMap {
        let mut new_map = IdentMap::new();

        for (name, entry) in self.0.iter() {
            new_map.add(name, &entry.new_name, false, false);
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
    for declaration in declarations {
        match declaration {
            Declaration::FunDecl(function_declaration) => {
                typecheck_function(function_declaration, &mut symbol_table)?;
            }
            Declaration::VarDecl(variable_declaration) => {
                typecheck_file_scope_variable(variable_declaration, &mut symbol_table)?;
            }
        }
    }

    Ok((ast, symbol_table))
}

fn resolve_file_scope_variables(declaration: &VariableDeclaration, ident_map: &mut IdentMap) {
    let VariableDeclaration(name, _, _) = declaration;

    ident_map.add(name, name, true, true);
}

fn resolve_parameter(parameter: &Identifier, ident_map: &mut IdentMap) -> Result<Identifier> {
    if let Some(entry) = ident_map.get(parameter) {
        if entry.from_current_scope {
            return Err(anyhow!(
                "resolve_declaration: duplicate declaration of variable '{parameter}'"
            ));
        }
    }

    let unique_name = temp_name(parameter);
    ident_map.add(parameter, &unique_name, true, false);

    Ok(unique_name)
}

fn resolve_function(declaration: &FunctionDeclaration, ident_map: &mut IdentMap) -> Result<FunctionDeclaration> {
    let FunctionDeclaration(name, opt_params, opt_body, opt_storage_class) = declaration;

    if let Some(entry) = ident_map.get(name) {
        if entry.from_current_scope && !entry.has_linkage {
            return Err(anyhow!("resolve_function: duplicate function declaration: '{name}'"));
        }
    }

    ident_map.add(name, name, true, true);

    let mut inner_map = ident_map.duplicate();
    let new_params = match opt_params {
        Some(params) => {
            let mut resolved_params = Vec::<Identifier>::new();
            for param in params {
                let resolved_param = resolve_parameter(param, &mut inner_map)?;
                resolved_params.push(resolved_param);
            }
            Some(resolved_params)
        }
        None => None,
    };
    let new_body = match opt_body {
        Some(body) => Some(resolve_block(body, &mut inner_map)?),
        None => None,
    };

    Ok(FunctionDeclaration(
        name.clone(),
        new_params,
        new_body,
        opt_storage_class.clone(),
    ))
}

fn resolve_block(block: &Block, ident_map: &mut IdentMap) -> Result<Block> {
    let mut new_block = Vec::<BlockItem>::new();

    for item in block {
        let new_item = match item {
            BlockItem::D(declaration) => BlockItem::D(match declaration {
                Declaration::FunDecl(fundecl) => match fundecl {
                    FunctionDeclaration(name, _, Some(_), _) => {
                        return Err(anyhow!("resolve_block: nested function definitions not allowed: {name:?}"));
                    }
                    FunctionDeclaration(name, _, _, Some(StorageClass::Static)) => {
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
    let VariableDeclaration(name, init, opt_storage_class) = declaration;

    if let Some(entry) = ident_map.get(name) {
        if entry.from_current_scope && !(entry.has_linkage && matches!(opt_storage_class, Some(StorageClass::Extern))) {
            return Err(anyhow!(
                "resolve_local_variable: conflicting local declarations of variable '{name}'"
            ));
        }
    }

    match opt_storage_class {
        Some(StorageClass::Extern) => {
            ident_map.add(name, name, true, true);
            Ok(declaration.clone())
        }
        _ => {
            let unique_name = temp_name(name);
            ident_map.add(name, &unique_name, true, false);

            let resolved_init = match init {
                Some(initializer) => Some(resolve_expression(initializer, ident_map)?),
                None => None,
            };

            Ok(VariableDeclaration(unique_name, resolved_init, opt_storage_class.clone()))
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
        Statement::Null => Statement::Null,
    };

    Ok(new_statement)
}

fn resolve_optional_expression(optional_expression: &Option<Expression>, ident_map: &IdentMap) -> Result<Option<Expression>> {
    let resolved_expression = match optional_expression {
        Some(expression) => Some(resolve_expression(expression, ident_map)?),
        None => None,
    };

    Ok(resolved_expression)
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
        Expression::Conditional(condition, then_part, else_part) => Expression::Conditional(
            Box::new(resolve_expression(condition, ident_map)?),
            Box::new(resolve_expression(then_part, ident_map)?),
            Box::new(resolve_expression(else_part, ident_map)?),
        ),
        Expression::Assignment(left, right) => {
            match **left {
                // Here be boxes, arrgh!
                Expression::Var(_) => Expression::Assignment(
                    Box::new(resolve_expression(left, ident_map)?),
                    Box::new(resolve_expression(right, ident_map)?),
                ),
                _ => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
            }
        }
        Expression::CompoundAssignment(operator, left, right) => {
            match **left {
                // Here be boxes, arrgh!
                Expression::Var(_) => Expression::CompoundAssignment(
                    operator.clone(),
                    Box::new(resolve_expression(left, ident_map)?),
                    Box::new(resolve_expression(right, ident_map)?),
                ),
                _ => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
            }
        }
        Expression::Var(name) => match ident_map.get(name) {
            Some(entry) => Expression::Var(entry.new_name),
            None => return Err(anyhow!("resolve_expression: Undeclared variable: '{name}'")),
        },
        Expression::Unary(operator, dst) => {
            let resolved = resolve_expression(dst, ident_map)?;
            if matches!(
                operator,
                UnaryOperator::PreIncrement
                    | UnaryOperator::PreDecrement
                    | UnaryOperator::PostIncrement
                    | UnaryOperator::PostDecrement
            ) && !matches!(resolved, Expression::Var(_))
            {
                return Err(anyhow!("resolve_expression: Illegal lvalue: '{dst:?}'"));
            }

            Expression::Unary(operator.clone(), Box::new(resolved))
        }
        Expression::Binary(operator, left, right) => Expression::Binary(
            operator.clone(),
            Box::new(resolve_expression(left, ident_map)?),
            Box::new(resolve_expression(right, ident_map)?),
        ),
        Expression::FunctionCall(name, opt_args) => match ident_map.get(name) {
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

                Expression::FunctionCall(new_name, new_args)
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
    if let FunctionDeclaration(name, opt_params, Some(body), opt_storage_class) = declaration {
        let new_body = label_block(body, label)?;
        return Ok(FunctionDeclaration(
            name.clone(),
            opt_params.clone(),
            Some(new_body),
            opt_storage_class.clone(),
        ));
    }

    Ok(declaration.clone())
}

fn typecheck_for_init(for_init: &ForInit, symbol_table: &mut SymbolTable) -> Result<()> {
    match for_init {
        ForInit::InitDecl(declaration) => {
            if let VariableDeclaration(name, _, Some(_)) = declaration {
                return Err(anyhow!("typecheck_for_init: Storage class on for-init not allowed: {name:?}"));
            }
            typecheck_local_variable(declaration, symbol_table)?;
        }
        ForInit::InitExp(Some(expression)) => typecheck_expression(expression, symbol_table)?,
        _ => (),
    }

    Ok(())
}

fn typecheck_statement(statement: &Statement, symbol_table: &mut SymbolTable) -> Result<()> {
    match statement {
        Statement::Return(expression) => {
            typecheck_expression(expression, symbol_table)?;
        }
        Statement::Expression(expression) => {
            typecheck_expression(expression, symbol_table)?;
        }
        Statement::If(expression, then_branch, else_branch) => {
            typecheck_expression(expression, symbol_table)?;
            typecheck_statement(then_branch, symbol_table)?;
            if let Some(else_part) = else_branch {
                typecheck_statement(else_part, symbol_table)?;
            }
        }
        Statement::Compound(block) => typecheck_block(block, symbol_table)?,
        Statement::While(expression, statement, _) => {
            typecheck_expression(expression, symbol_table)?;
            typecheck_statement(statement, symbol_table)?;
        }
        Statement::DoWhile(statement, expression, _) => {
            typecheck_statement(statement, symbol_table)?;
            typecheck_expression(expression, symbol_table)?;
        }
        Statement::For(for_init, opt_condition, opt_post, body, _) => {
            typecheck_for_init(for_init, symbol_table)?;
            if let Some(condition) = opt_condition {
                typecheck_expression(condition, symbol_table)?;
            }
            if let Some(post) = opt_post {
                typecheck_expression(post, symbol_table)?;
            }
            typecheck_statement(body, symbol_table)?;
        }
        _ => (),
    }

    Ok(())
}

fn typecheck_expression(expression: &Expression, symbol_table: &mut SymbolTable) -> Result<()> {
    match expression {
        Expression::FunctionCall(name, opt_args) => match symbol_table.get(name) {
            Some(entry) => match entry.symbol_type {
                Type::Int => return Err(anyhow!("Variable used as function name: {name:?}")),
                Type::FunType(params_count) => {
                    let args_count = match opt_args {
                        Some(args) => args.len(),
                        None => 0,
                    };

                    if params_count != args_count {
                        return Err(anyhow!("Function called with wrong number of arguments: {name:?}"));
                    }

                    if let Some(args) = opt_args {
                        for arg in args {
                            typecheck_expression(arg, symbol_table)?;
                        }
                    }
                }
            },
            None => return Err(anyhow!("Undefined function call: {name:?}")),
        },
        Expression::Var(name) => match symbol_table.get(name) {
            Some(entry) => {
                if let Type::FunType(_) = entry.symbol_type {
                    return Err(anyhow!("Function name used as variable: {name:?}"));
                }
            }
            None => return Err(anyhow!("Undeclared variable in expression: {name:?}")),
        },
        Expression::Assignment(lvalue, expression) => {
            typecheck_expression(lvalue, symbol_table)?;
            typecheck_expression(expression, symbol_table)?;
        }
        Expression::Unary(_, expression) => {
            typecheck_expression(expression, symbol_table)?;
        }
        Expression::Binary(_, lhs, rhs) => {
            typecheck_expression(lhs, symbol_table)?;
            typecheck_expression(rhs, symbol_table)?;
        }
        Expression::CompoundAssignment(_, lvalue, rhs) => {
            typecheck_expression(lvalue, symbol_table)?;
            typecheck_expression(rhs, symbol_table)?;
        }
        Expression::Conditional(condition, then_branch, else_branch) => {
            typecheck_expression(condition, symbol_table)?;
            typecheck_expression(then_branch, symbol_table)?;
            typecheck_expression(else_branch, symbol_table)?;
        }
        _ => (),
    }

    Ok(())
}

fn typecheck_block(block: &Block, symbol_table: &mut SymbolTable) -> Result<()> {
    for item in block {
        match item {
            BlockItem::D(declaration) => match declaration {
                Declaration::VarDecl(vardecl) => typecheck_local_variable(vardecl, symbol_table)?,
                Declaration::FunDecl(fundecl) => typecheck_function(fundecl, symbol_table)?,
            },
            BlockItem::S(statement) => typecheck_statement(statement, symbol_table)?,
        }
    }

    Ok(())
}

fn typecheck_local_variable(declaration: &VariableDeclaration, symbol_table: &mut SymbolTable) -> Result<()> {
    let VariableDeclaration(name, init, opt_storage_class) = declaration;

    match opt_storage_class {
        Some(StorageClass::Extern) => {
            if init.is_some() {
                return Err(anyhow!(
                    "typecheck_local_variable: Initializer on local extern variable declaration: {name:?}"
                ));
            }
            match symbol_table.get(name) {
                Some(entry) => {
                    if entry.symbol_type != Type::Int {
                        return Err(anyhow!(
                            "typecheck_local_variable: function redeclared as variable: {entry:?}"
                        ));
                    }
                }
                None => {
                    symbol_table.add(
                        name,
                        Symbol {
                            symbol_type: Type::Int,
                            attrs: IdentAttrs::Static(InitialValue::NoInitializer, true),
                        },
                    );
                }
            }
        }
        Some(StorageClass::Static) => {
            let initial_value = match init {
                Some(Expression::Constant(number)) => InitialValue::Initial(*number),
                None => InitialValue::Initial(0),
                _ => {
                    return Err(anyhow!(
                        "typecheck_local_variable: Non-constant initializer on local static variable: {name:?}"
                    ))
                }
            };
            symbol_table.add(
                name,
                Symbol {
                    symbol_type: Type::Int,
                    attrs: IdentAttrs::Static(initial_value, false),
                },
            );
        }
        _ => {
            symbol_table.add(
                name,
                Symbol {
                    symbol_type: Type::Int,
                    attrs: IdentAttrs::Local,
                },
            );

            if let Some(expression) = init {
                typecheck_expression(expression, symbol_table)?;
            }
        }
    }

    Ok(())
}

fn typecheck_file_scope_variable(declaration: &VariableDeclaration, symbol_table: &mut SymbolTable) -> Result<()> {
    let VariableDeclaration(name, init, opt_storage_class) = declaration;

    let mut initial_value = match init {
        Some(Expression::Constant(number)) => InitialValue::Initial(*number),
        None => {
            if matches!(opt_storage_class, Some(StorageClass::Extern)) {
                InitialValue::NoInitializer
            } else {
                InitialValue::Tentative
            }
        }
        _ => return Err(anyhow!("typecheck_file_scope_variable: non-constant initializer: {init:?}")),
    };
    let mut global = !matches!(opt_storage_class, Some(StorageClass::Static));

    if let Some(entry) = symbol_table.get(name) {
        if entry.symbol_type != Type::Int {
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
        if matches!(entry_initial_value, InitialValue::Initial(_)) {
            if matches!(initial_value, InitialValue::Initial(_)) {
                return Err(anyhow!(
                    "typecheck_file_scope_varuable: conflicting file scope variable definitions: {entry:?}"
                ));
            } else {
                initial_value = entry_initial_value;
            }
        } else if !matches!(initial_value, InitialValue::Initial(_)) && matches!(entry_initial_value, InitialValue::Tentative) {
            initial_value = InitialValue::Tentative;
        }
    }

    symbol_table.add(
        name,
        Symbol {
            symbol_type: Type::Int,
            attrs: IdentAttrs::Static(initial_value, global),
        },
    );

    Ok(())
}

fn typecheck_function(declaration: &FunctionDeclaration, symbol_table: &mut SymbolTable) -> Result<()> {
    let FunctionDeclaration(name, parameters, body, opt_storage_class) = declaration;

    let function_type = Type::FunType(parameters.as_ref().map_or(0, |params| params.len()));
    let mut global = !matches!(opt_storage_class, Some(StorageClass::Static));
    let mut already_defined = false;

    if let Some(entry) = symbol_table.get(name) {
        if entry.symbol_type != function_type {
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
            return Err(anyhow!("Static function delcaration follows non-static: {entry:?}"));
        }
        global = entry_is_global;
    }

    symbol_table.add(
        name,
        Symbol {
            symbol_type: function_type,
            attrs: IdentAttrs::Function(already_defined || body.is_some(), global),
        },
    );

    if let Some(block) = body {
        if let Some(params) = parameters {
            for param in params {
                symbol_table.add(
                    param,
                    Symbol {
                        symbol_type: Type::Int,
                        attrs: IdentAttrs::Local,
                    },
                );
            }
        }
        typecheck_block(block, symbol_table)?;
    }

    Ok(())
}
