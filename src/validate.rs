//! validate.rs
//!
//! Validate AST for symantic errors.

use std::collections::HashMap;
use::anyhow::{Result, anyhow};

use crate::parse::{
    Identifier, Label, Block, UnaryOperator, Expression, BlockItem,
    ForInit, Statement, VariableDeclaration, FunctionDeclaration,
    Declaration, Ast,
};
use crate::utils::temp_name;

#[derive(Debug, Clone, PartialEq)]
enum Type {
    Int,
    FunType(usize),
}

#[derive(Debug, Clone, PartialEq)]
struct TypeEntry {
    sym_type: Type,
    defined:  bool,
}

#[derive(Debug, Clone, PartialEq)]
struct TypeMap(HashMap::<Identifier, TypeEntry>);

impl TypeMap {
    fn new() -> Self {
	Self(HashMap::new())
    }

    fn get(&self, name: &String) -> Option<TypeEntry> {
	self.0.get(name).cloned()
    }

    fn add(&mut self, name: &String, ident_type: Type, is_defined: bool) -> Option<TypeEntry> {
	self.0.insert(name.clone(), TypeEntry {
	    sym_type: ident_type,
	    defined : is_defined
	})
    }
}

#[derive(Debug, Clone, PartialEq)]
struct MapEntry {
    new_name:           Identifier,
    from_current_scope: bool,
    has_linkage:        bool,
}

impl MapEntry {
    fn new(name: &String, current: bool, linkage: bool) -> Self {
	Self {
	    new_name          : name.clone(),
	    from_current_scope: current,
	    has_linkage       : linkage,
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

    fn add(&mut self, name: &String, new_name: &String,
	   from_current_scope: bool, has_linkage: bool) -> Option<MapEntry> {
	self.0.insert(name.clone(), MapEntry::new(new_name, from_current_scope, has_linkage))
    }

    fn duplicate(&self) -> IdentMap {
	let mut new_map = IdentMap::new();

	for (name, entry) in self.0.iter() {
	    new_map.add(&name, &entry.new_name, false, false);
	}

	new_map
    }
}

pub fn validate(mut ast: Ast) -> Result<Ast> {
    let Ast::Program(ref mut declarations) = ast;
    let mut ident_map = IdentMap::new();
    let mut type_map  = TypeMap::new();
    
    // Resolve all the variable names in each function
    for declaration in declarations.iter_mut() {
	*declaration = resolve_function(declaration, &mut ident_map)?;
    }

    // Label all the loops, breaks, continues
    for declaration in declarations.iter_mut() {
	*declaration = label_loops(declaration, &None)?;
    }

    // Typecheck all declarations, definitions, and variables
    for declaration in declarations.iter() {
	typecheck_function(declaration, &mut type_map)?;
    }

    Ok(ast)
}

fn resolve_parameter(parameter: &Identifier, ident_map: &mut IdentMap) -> Result<Identifier> {
    if let Some(entry) = ident_map.get(parameter) {
	if entry.from_current_scope {
	    return Err(anyhow!("resolve_declaration: duplicate declaration of variable '{parameter}'"));
	}
    }
    
    let unique_name = temp_name(parameter);
    ident_map.add(parameter, &unique_name, true, false);

    Ok(unique_name)
}

fn resolve_function(declaration: &FunctionDeclaration, ident_map: &mut IdentMap) -> Result<FunctionDeclaration> {
    let FunctionDeclaration(name, opt_params, opt_body) = declaration;

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
	    for param in params.iter() {
		let resolved_param = resolve_parameter(param, &mut inner_map)?;
		resolved_params.push(resolved_param);
	    }
	    Some(resolved_params)
	},
	None         => None,
    };
    let new_body = match opt_body {
	Some(body) => Some(resolve_block(body, &mut inner_map)?),
	None       => None,
    };

    Ok(FunctionDeclaration(name.clone(), new_params, new_body))
}

fn resolve_block(block: &Block, ident_map: &mut IdentMap) -> Result<Block> {
    let mut new_block = Vec::<BlockItem>::new();
    
    for item in block.iter() {
	let new_item = match item {
	    BlockItem::D(declaration) => BlockItem::D(match declaration {
		Declaration::FunDecl(fundecl) => {
		    match fundecl {
			FunctionDeclaration(name, _, Some(_)) => {
			    return Err(anyhow!("resolve_block: nested function definitions not allowed: {name:?}"));
			},
			_ => Declaration::FunDecl(resolve_function(fundecl, ident_map)?)

		    }
		},
		Declaration::VarDecl(vardecl) => Declaration::VarDecl(resolve_variable(vardecl, ident_map)?),
	    }),
	    BlockItem::S(statement)   => BlockItem::S(resolve_statement(statement, ident_map)?),
	};
	new_block.push(new_item);
    }

    Ok(new_block)
}

fn resolve_variable(declaration: &VariableDeclaration, ident_map: &mut IdentMap) -> Result<VariableDeclaration> {
    let VariableDeclaration(name, init) = declaration;

    if let Some(entry) = ident_map.get(name) {
	if entry.from_current_scope {
	    return Err(anyhow!("resolve_declaration: duplicate declaration of variable '{name}'"));
	}
    }
    
    let unique_name = temp_name(name);
    ident_map.add(name, &unique_name, true, false);

    let resolved_init = match init {
	Some(initializer) => Some(resolve_expression(initializer, ident_map)?),
	None => None,
    };

    Ok(VariableDeclaration(unique_name, resolved_init))
}

fn resolve_statement(statement: &Statement, ident_map: &IdentMap) -> Result<Statement> {
    let new_statement = match statement {
	Statement::Return(expression)     => Statement::Return(resolve_expression(expression, ident_map)?),
	Statement::Expression(expression) => Statement::Expression(resolve_expression(expression, ident_map)?),
	Statement::If(condition, then_part, else_part) => {
	    let resolved_condition = resolve_expression(condition, ident_map)?;
	    let resolved_then = Box::new(resolve_statement(then_part, ident_map)?);
	    let resolved_else = match else_part {
		Some(statement) => Some(Box::new(resolve_statement(statement, ident_map)?)),
		None            => None,
	    };
	    Statement::If(resolved_condition, resolved_then, resolved_else)
	},
	Statement::Compound(block) => {
	    let mut new_ident_map = ident_map.duplicate();
	    Statement::Compound(resolve_block(block, &mut new_ident_map)?)
	},
	Statement::Break(_)    => statement.clone(),
	Statement::Continue(_) => statement.clone(),
	Statement::While(condition, body, label) => {
	    let resolved_condition = resolve_expression(condition, ident_map)?;
	    let resolved_body      = resolve_statement(body, ident_map)?;
	    Statement::While(resolved_condition, Box::new(resolved_body), label.clone())
	},
	Statement::DoWhile(body, condition, label) => {
	    let resolved_body      = resolve_statement(body, ident_map)?;
	    let resolved_condition = resolve_expression(condition, ident_map)?;
	    Statement::DoWhile(Box::new(resolved_body), resolved_condition, label.clone())
	},
	Statement::For(for_init, condition, post, body, label) => {
	    let mut new_ident_map    = ident_map.duplicate();
	    let resolved_init      = resolve_for_init(for_init, &mut new_ident_map)?;
	    let resolved_condition = resolve_optional_expression(condition, &new_ident_map)?;
	    let resolved_post      = resolve_optional_expression(post, &new_ident_map)?;
	    let resolved_body      = resolve_statement(body, &new_ident_map)?;
	    Statement::For(resolved_init, resolved_condition, resolved_post, Box::new(resolved_body), label.clone())
	},
	Statement::Null => Statement::Null,
    };

    Ok(new_statement)
}

fn resolve_optional_expression(optional_expression: &Option<Expression>,
			       ident_map: &IdentMap) -> Result<Option<Expression>> {
    let resolved_expression = match optional_expression {
	Some(expression) => Some(resolve_expression(expression, ident_map)?),
	None             => None
    };

    Ok(resolved_expression)
}

fn resolve_for_init(for_init: &ForInit, ident_map: &mut IdentMap) -> Result<ForInit> {
    let resolved_for_init = match for_init {
	ForInit::InitDecl(declaration) => ForInit::InitDecl(resolve_variable(declaration, ident_map)?),
	ForInit::InitExp(expression)   => ForInit::InitExp(resolve_optional_expression(expression, ident_map)?),
    };

    Ok(resolved_for_init)
}

fn resolve_expression(expression: &Expression, ident_map: &IdentMap) -> Result<Expression> {
    let new_expression = match expression {
	Expression::Conditional(condition, then_part, else_part) => {
	    Expression::Conditional(Box::new(resolve_expression(condition, ident_map)?),
				    Box::new(resolve_expression(then_part, ident_map)?),
				    Box::new(resolve_expression(else_part, ident_map)?))
	},
	Expression::Assignment(left, right) => {
	    match **left {            // Here be boxes, arrgh!
		Expression::Var(_) => Expression::Assignment(Box::new(resolve_expression(left, ident_map)?),
							     Box::new(resolve_expression(right, ident_map)?)),
		_                  => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
	    }
	},
	Expression::CompoundAssignment(operator, left, right) => {
	    match **left {            // Here be boxes, arrgh!
		Expression::Var(_) => Expression::CompoundAssignment(operator.clone(),
								     Box::new(resolve_expression(left, ident_map)?),
								     Box::new(resolve_expression(right, ident_map)?)),
		_                  => return Err(anyhow!("resolve_expression: Illegal lvalue: '{left:?}'")),
	    }
	},
	Expression::Var(name) => {
	    match ident_map.get(name) {
		Some(entry)  => Expression::Var(entry.new_name),
		None         => return Err(anyhow!("resolve_expression: Undeclared variable: '{name}'")),
	    }
	},
	Expression::Unary(operator, dst) => {
	    let resolved = resolve_expression(dst, ident_map)?;
	    if matches!(operator,
			UnaryOperator::PreIncrement  |
			UnaryOperator::PreDecrement  |
			UnaryOperator::PostIncrement |
			UnaryOperator::PostDecrement) && ! matches!(resolved, Expression::Var(_)) {
		return Err(anyhow!("resolve_expression: Illegal lvalue: '{dst:?}'"));
	    }
	    
	    Expression::Unary(operator.clone(), Box::new(resolved))
	},
	Expression::Binary(operator, left, right) => {
	    Expression::Binary(operator.clone(),
			       Box::new(resolve_expression(left, ident_map)?),
			       Box::new(resolve_expression(right, ident_map)?))
	},
	Expression::FunctionCall(name, opt_args) => {
	    match ident_map.get(name) {
		Some(entry) => {
		    let new_name = entry.new_name.clone();
		    let new_args = match opt_args {
			Some(args) => {
			    let mut resolved_args = Vec::<Expression>::new();
			    for arg in args.iter() {
				let resolved_arg = resolve_expression(arg, ident_map)?;
				resolved_args.push(resolved_arg);
			    }
			    Some(resolved_args)
			},
			None => None,
		    };
		    
		    Expression::FunctionCall(new_name, new_args)
		},
		None        => return Err(anyhow!("resolve_expression: undeclarated function '{name}'")),
	    }
	},
	_ => expression.clone()
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
	},
	Statement::Compound(block) => {
	    Statement::Compound(label_block(block, label)?)
	},
	Statement::Break(_) => {
	    match label {
		Some(name) => Statement::Break(name.clone()),
		None => return Err(anyhow!("break statement outside of loop")),
	    }
	},
	Statement::Continue(_) => {
	    match label {
		Some(name) => Statement::Continue(name.clone()),
		None => return Err(anyhow!("continue statement outside of loop")),
	    }
	},
	Statement::While(condition, body, _) => {
	    let while_label = temp_name("while");
	    let labeled_body = label_statement(body, &Some(while_label.clone()))?;
	    Statement::While(condition.clone(), Box::new(labeled_body), while_label)
	},
	Statement::DoWhile(body, condition, _) => {
	    let do_while_label = temp_name("dowhile");
	    let labeled_body = label_statement(body, &Some(do_while_label.clone()))?;
	    Statement::DoWhile(Box::new(labeled_body), condition.clone(), do_while_label)
	},
	Statement::For(for_init, condition, post, body, _) => {
	    let for_label = temp_name("for");
	    let labeled_body = label_statement(body, &Some(for_label.clone()))?;
	    Statement::For(for_init.clone(), condition.clone(), post.clone(), Box::new(labeled_body), for_label)
	},
	statement => statement.clone()
    };

    Ok(labeled_statement)
}

fn label_block(block: &Block, label: &Option<Label>) -> Result<Block> {
    let mut new_block = Vec::<BlockItem>::new();
    
    for item in block.iter() {
	match item {
	    BlockItem::D(_) => {
		new_block.push(item.clone());
	    },
	    BlockItem::S(statement) => {
		let labeled_statement = label_statement(statement, label)?;
		new_block.push(BlockItem::S(labeled_statement));
	    }
	}
    }

    Ok(new_block)
}

fn label_loops(declaration: &FunctionDeclaration, label: &Option<Label>) -> Result<FunctionDeclaration> {
    if let FunctionDeclaration(name, opt_params, Some(body)) = declaration {
	let new_body = label_block(body, label)?;
	return Ok(FunctionDeclaration(name.clone(), opt_params.clone(), Some(new_body)));
    }

    Ok(declaration.clone())
}

fn typecheck_for_init(for_init: &ForInit, type_map: &mut TypeMap) -> Result<()> {
    match for_init {
	ForInit::InitDecl(declaration)     => typecheck_variable(declaration, type_map)?,
	ForInit::InitExp(Some(expression)) => typecheck_expression(expression, type_map)?,
	_ => ()
    }

    Ok(())
}

fn typecheck_statement(statement: &Statement, type_map: &mut TypeMap) -> Result<()> {
    match statement {
	Statement::Return(expression) => {
	    typecheck_expression(expression, type_map)?;
	},
	Statement::Expression(expression) => {
	    typecheck_expression(expression, type_map)?;
	},
	Statement::If(expression, then_branch, else_branch) => {
	    typecheck_expression(expression, type_map)?;
	    typecheck_statement(then_branch, type_map)?;
	    if let Some(else_part) = else_branch {
		typecheck_statement(else_part, type_map)?;
	    }
	},
	Statement::Compound(block) => typecheck_block(block, type_map)?,
	Statement::While(expression, statement, _) => {
	    typecheck_expression(expression, type_map)?;
	    typecheck_statement(statement, type_map)?;
	},
	Statement::DoWhile(statement, expression, _) => {
	    typecheck_statement(statement, type_map)?;
	    typecheck_expression(expression, type_map)?;
	},
	Statement::For(for_init, opt_condition, opt_post, body, _) => {
	    typecheck_for_init(for_init, type_map)?;
	    if let Some(condition) = opt_condition {
		typecheck_expression(condition, type_map)?;
	    }
	    if let Some(post) = opt_post {
		typecheck_expression(post, type_map)?;
	    }
	    typecheck_statement(body, type_map)?;
	}
	_ => ()
    }
    
    Ok(())
}

fn typecheck_expression(expression: &Expression, type_map: &mut TypeMap) -> Result<()> {
    match expression {
	Expression::FunctionCall(name, opt_args) => {
	    match type_map.get(name) {
		Some(entry) => {
		    match entry.sym_type {
			Type::Int => return Err(anyhow!("Variable used as function name: {name:?}")),
			Type::FunType(params_count) => {
			    let args_count = match opt_args {
				Some(args) => args.len(),
				None       => 0,
			    };

			    if params_count != args_count {
				return Err(anyhow!("Function called with wrong number of arguments: {name:?}"));
			    }

			    if let Some(args) = opt_args {
				for arg in args {
				    typecheck_expression(arg, type_map)?;
				}
			    }
			}
		    }
		},
		None => return Err(anyhow!("Undefined function call: {name:?}")),
	    }
	},
	Expression::Var(name) => {
	    match type_map.get(name) {
		Some(entry) => {
		    match entry.sym_type {
			Type::FunType(_) => return Err(anyhow!("Function name used as variable: {name:?}")),
			_                => ()
		    }
		},
		None => return Err(anyhow!("Undeclared variable in expression: {name:?}")),
	    }
	},
	Expression::Assignment(lvalue, expression) => {
	    typecheck_expression(lvalue, type_map)?;
	    typecheck_expression(expression, type_map)?;
	},
	Expression::Unary(_, expression) => {
	    typecheck_expression(expression, type_map)?;
	},
	Expression::Binary(_, lhs, rhs) => {
	    typecheck_expression(lhs, type_map)?;
	    typecheck_expression(rhs, type_map)?;
	},
	Expression::CompoundAssignment(_, lvalue, rhs) => {
	    typecheck_expression(lvalue, type_map)?;
	    typecheck_expression(rhs, type_map)?;
	},
	Expression::Conditional(condition, then_branch, else_branch) => {
	    typecheck_expression(condition, type_map)?;
	    typecheck_expression(then_branch, type_map)?;
	    typecheck_expression(else_branch, type_map)?;
	}
	_ => ()
    }
    
    Ok(())
}

fn typecheck_block(block: &Block, type_map: &mut TypeMap) -> Result<()> {
    for item in block.iter() {
	match item {
	    BlockItem::D(declaration) => match declaration {
		Declaration::VarDecl(vardecl) => typecheck_variable(vardecl, type_map)?,
		Declaration::FunDecl(fundecl) => typecheck_function(fundecl, type_map)?,
	    },
	    BlockItem::S(statement) => typecheck_statement(statement, type_map)?,
	}
    }

    Ok(())
}

fn typecheck_variable(declaration: &VariableDeclaration, type_map: &mut TypeMap) -> Result<()> {
    let VariableDeclaration(name, init) = declaration;

    type_map.add(name, Type::Int, false);
    if let Some(expression) = init {
	typecheck_expression(expression, type_map)?;
    }
    
    Ok(())
}

fn typecheck_function(declaration: &FunctionDeclaration, type_map: &mut TypeMap) -> Result<()> {
    let FunctionDeclaration(name, parameters, body) = declaration;

    let function_type = match parameters {
	Some(params) => Type::FunType(params.len()),
	None         => Type::FunType(0),
    };

    let mut already_defined = false;
    if let Some(entry) = type_map.get(name) {
	if entry.sym_type != function_type {
	    return Err(anyhow!("Incompatible function declarations: '{entry:?}'"));
	}
	already_defined = entry.defined;
	if already_defined && body.is_some() {
	    return Err(anyhow!("Function defined more than once: {entry:?}'"));
	}
    }

    type_map.add(name, function_type, already_defined || body.is_some());

    if let Some(block) = body {
	if let Some(params) = parameters {
	    for param in params.iter() {
		type_map.add(param, Type::Int, false);
	    }
	}
	typecheck_block(block, type_map)?;
    }

    Ok(())
}
