//! # parse
//!
//! Creates an AST from the token list supplied by the lexer.

use anyhow::{Result, bail};
use std::iter::Peekable;
use std::mem;
use std::slice::Iter;

use crate::lex::{Token, TokenList};
use crate::utils::temp_name;

pub type Identifier = String;
pub type Label = String;
pub type Block = Vec<BlockItem>;
pub type Parameters = Vec<Parameter>;
pub type FunctionArgs = Vec<Expression>;
pub type Declarations = Vec<Declaration>;

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOperator {
    Complement,
    Negate,
    Not
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOperator {
    Plus,
    Minus,
    Multiply,
    Divide,
    Remainder,
    Leftshift,
    Rightshift,
    BitAnd,
    BitXor,
    BitOr,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual
}

#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    ConstInt(i32),
    ConstLong(i64)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Constant(Const, Type),
    Var(Identifier, Type),
    Cast(Type, Box<Expression>, Type),
    Unary(UnaryOperator, Box<Expression>, Type),
    Binary(BinaryOperator, Box<Expression>, Box<Expression>, Type),
    Assignment(Box<Expression>, Box<Expression>, Type),
    CompoundAssignment(BinaryOperator, Box<Expression>, Box<Expression>, Type),
    Conditional(Box<Expression>, Box<Expression>, Box<Expression>, Type),
    FunctionCall(Identifier, Option<FunctionArgs>, Type)
}

#[allow(dead_code)]
#[rustfmt::skip]
impl Expression {
    pub fn set_type(&self, new_type: Type) -> Expression {
        let mut new_expression = self.clone();
        match &mut new_expression {
            Expression::Constant(_, constant_type)             => *constant_type = new_type,
            Expression::Var(_, var_type)                       => *var_type = new_type,
            Expression::Cast(_, _, cast_type)                  => *cast_type = new_type,
            Expression::Unary(_, _, unary_type)                => *unary_type = new_type,
            Expression::Binary(_, _, _, binary_type)           => *binary_type = new_type,
            Expression::Assignment(_, _, assignment_type)      => *assignment_type = new_type,
            Expression::CompoundAssignment(_, _, _, comp_type) => *comp_type = new_type,
            Expression::Conditional(_, _, _, conditional_type) => *conditional_type = new_type,
            Expression::FunctionCall(_, _, func_type)          => *func_type = new_type,
        }
        new_expression
    }

    pub fn get_type(&self) -> Type {
        let new_type = match self {
            Expression::Constant(_, constant_type)             => constant_type,
            Expression::Var(_, var_type)                       => var_type,
            Expression::Cast(_, _, cast_type)                  => cast_type,
            Expression::Unary(_, _, unary_type)                => unary_type,
            Expression::Binary(_, _, _, binary_type)           => binary_type,
            Expression::Assignment(_, _, assignment_type)      => assignment_type,
            Expression::CompoundAssignment(_, _, _, comp_type) => comp_type,
            Expression::Conditional(_, _, _, conditional_type) => conditional_type,
            Expression::FunctionCall(_, _, func_type)          => func_type,
        };
        new_type.clone()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BlockItem {
    S(Statement),
    D(Declaration)
}

#[derive(Debug, Clone, PartialEq)]
pub enum ForInit {
    InitDecl(VariableDeclaration),
    InitExp(Option<Expression>)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Return(Expression),
    Expression(Expression),
    If(Expression, Box<Statement>, Option<Box<Statement>>),
    Compound(Block),
    Break(Label),
    Continue(Label),
    While(Expression, Box<Statement>, Label),
    DoWhile(Box<Statement>, Expression, Label),
    For(ForInit, Option<Expression>, Option<Expression>, Box<Statement>, Label),
    None
}

#[derive(Debug, Clone, PartialEq)]
pub enum StorageClass {
    Static,
    Extern
}

type ParameterTypes = Box<Vec<Type>>;
type ReturnType = Box<Type>;

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Long,
    FunType(ParameterTypes, ReturnType),
    None
}

#[derive(Debug, Clone, PartialEq)]
pub struct Specifier {
    type_of:       Type,
    storage_class: Option<StorageClass>
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub name:    String,
    pub type_of: Type
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariableDeclaration(pub Identifier, pub Option<Expression>, pub Type, pub Option<StorageClass>);

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDeclaration(pub Identifier,
                               pub Option<Parameters>,
                               pub Option<Block>,
                               pub Type,
                               pub Option<StorageClass>);

#[derive(Debug, Clone, PartialEq)]
pub enum Declaration {
    FunDecl(FunctionDeclaration),
    VarDecl(VariableDeclaration)
}

#[derive(Debug, Clone, PartialEq)]
pub enum Ast {
    Program(Declarations)
}

pub struct TokenStream<'a>(Peekable<Iter<'a, Token>>);

impl TokenStream<'_> {
    fn new(tokens: &TokenList) -> TokenStream {
        TokenStream(tokens.iter().peekable())
    }

    fn peek(&mut self) -> Result<&Token> {
        let token = match self.0.peek() {
            Some(token) => token,
            None => bail!("Unexpected end of token stream")
        };

        Ok(token)
    }

    fn next(&mut self) -> Result<&Token> {
        let token = match self.0.next() {
            Some(token) => token,
            None => bail!("Unexpected end of token stream")
        };

        Ok(token)
    }

    fn expect(&mut self, expected: Token) -> Result<&Token> {
        let token = self.next()?;

        if mem::discriminant(token) != mem::discriminant(&expected) {
            bail!("Expected token: '{expected:?}', Unexpected token: '{token:?}'");
        }

        Ok(token)
    }
}

pub fn parse(token_list: &TokenList) -> Result<Ast> {
    let mut tokens: TokenStream = TokenStream::new(token_list);
    let mut declarations = Vec::<Declaration>::new();

    while *tokens.peek()? != Token::Eot {
        let declaration = parse_declaration(&mut tokens)?;
        declarations.push(declaration);
    }

    Ok(Ast::Program(declarations))
}

fn parse_variable_declaration(tokens: &mut TokenStream, name: String, specifier: &Specifier)
                              -> Result<VariableDeclaration> {
    let expression = match tokens.peek()? {
        Token::Assignment => {
            tokens.next()?;
            parse_optional_expression(tokens, Token::Semicolon)?
        },
        Token::Semicolon => {
            tokens.next()?;
            None
        },
        token => bail!("parse_variable_declaration: unexpected token: '{token:?}'")
    };

    Ok(VariableDeclaration(name, expression, specifier.type_of.clone(), specifier.storage_class.clone()))
}

fn parse_parameter_list(tokens: &mut TokenStream) -> Result<Option<Parameters>> {
    let mut params = Parameters::new();

    tokens.expect(Token::OpenParen)?;
    while *tokens.peek()? != Token::CloseParen {
        match tokens.peek()? {
            Token::Int | Token::Long => {
                let specifier = parse_type_and_storage_class(tokens)?;
                let identifier = match tokens.next()? {
                    Token::Identifier(name) => name.to_string(),
                    token => bail!("parse_parameter: Unexpected token: '{token:?}'")
                };
                params.push(Parameter { name: identifier, type_of: specifier.type_of });
            },
            Token::Comma => {
                tokens.next()?;
                if *tokens.peek()? == Token::CloseParen {
                    bail!("Unexpected trailing comma in function definition");
                }
            },
            Token::Void => {
                tokens.next()?;
                tokens.expect(Token::CloseParen)?;
                return Ok(None);
            },
            token => bail!("parse_parameter_list: unexpected token '{token:?}'")
        }
    }
    tokens.expect(Token::CloseParen)?;

    Ok(Some(params))
}

fn parse_function_declaration(tokens: &mut TokenStream, name: String, specifier: &Specifier)
                              -> Result<FunctionDeclaration> {
    let optional_params = parse_parameter_list(tokens)?;

    let optional_body = match tokens.peek()? {
        Token::Semicolon => {
            tokens.next()?;
            None
        },
        Token::OpenBrace => Some(parse_block(tokens)?),
        token => bail!("parse_function_declaration: unexpected token: '{token:?}'")
    };

    let param_types = {
        let mut types: Vec<Type> = Vec::new();
        if let Some(ref parameters) = optional_params {
            for param in parameters {
                types.push(param.type_of.clone());
            }
        }
        types
    };

    let function_type = Type::FunType(Box::new(param_types), Box::new(specifier.type_of.clone()));

    Ok(FunctionDeclaration(name, optional_params, optional_body, function_type, specifier.storage_class.clone()))
}

fn parse_constant(token: &Token) -> Result<Expression> {
    let number = match token {
        Token::Constant(value) => {
            let number: i64 = value.parse()?;
            if number <= ((2 ^ 31) - 1) {
                Expression::Constant(Const::ConstInt(number as i32), Type::Int)
            } else {
                Expression::Constant(Const::ConstLong(number), Type::Long)
            }
        },
        Token::LConstant(value) => {
            let number: i64 = value.parse()?;
            Expression::Constant(Const::ConstLong(number), Type::Long)
        },
        _ => {
            bail!("parse_constant: unexpected token while parsing constant: {token:?}");
        }
    };

    Ok(number)
}

fn parse_type(specifiers: &Vec<Type>) -> Result<Type> {
    let parsed_type = match specifiers[..] {
        [Type::Int] => Type::Int,
        [Type::Long] | [Type::Long, Type::Int] | [Type::Int, Type::Long] => Type::Long,
        _ => bail!("parse_type: Unrecognized type specifiers: {specifiers:?}")
    };

    Ok(parsed_type)
}

fn parse_type_and_storage_class(tokens: &mut TokenStream) -> Result<Specifier> {
    let mut types: Vec<Type> = Vec::new();
    let mut storage_classes: Vec<StorageClass> = Vec::new();

    loop {
        match tokens.peek()? {
            Token::Int => types.push(Type::Int),
            Token::Long => types.push(Type::Long),
            Token::Static => storage_classes.push(StorageClass::Static),
            Token::Extern => storage_classes.push(StorageClass::Extern),
            _ => break
        }
        tokens.next()?;
    }

    let identifier_type = parse_type(&types)?;

    if storage_classes.len() > 1 {
        bail!("parse_type_and_storage: Invalid storage class: {:?}", storage_classes);
    }

    let identifier_storage_class = match storage_classes.len() {
        1 => Some(storage_classes[0].clone()),
        _ => None
    };

    Ok(Specifier { type_of: identifier_type, storage_class: identifier_storage_class })
}

fn parse_declaration(tokens: &mut TokenStream) -> Result<Declaration> {
    let specifier = parse_type_and_storage_class(tokens)?;

    let identifier = match tokens.peek()? {
        Token::Identifier(name) => {
            let identifier = name.clone();
            tokens.next()?;
            identifier
        },
        token => bail!("parse_declaration: Identifier expected: {token:?}")
    };

    let declaration = match tokens.peek()? {
        Token::OpenParen => Declaration::FunDecl(parse_function_declaration(tokens, identifier, &specifier)?),
        _ => Declaration::VarDecl(parse_variable_declaration(tokens, identifier, &specifier)?)
    };

    Ok(declaration)
}

fn parse_block_item(tokens: &mut TokenStream) -> Result<BlockItem> {
    let block_item = match tokens.peek()? {
        Token::Int | Token::Long | Token::Static | Token::Extern => BlockItem::D(parse_declaration(tokens)?),
        _ => BlockItem::S(parse_statement(tokens)?)
    };

    Ok(block_item)
}

fn parse_block(tokens: &mut TokenStream) -> Result<Block> {
    let mut body = Vec::new();

    tokens.expect(Token::OpenBrace)?;
    while *tokens.peek()? != Token::CloseBrace {
        let block_item = parse_block_item(tokens)?;
        body.push(block_item);
    }
    tokens.next()?;

    Ok(body)
}

fn parse_null(tokens: &mut TokenStream) -> Result<Statement> {
    tokens.expect(Token::Semicolon)?;
    Ok(Statement::None)
}

fn parse_return(tokens: &mut TokenStream) -> Result<Statement> {
    tokens.expect(Token::Return)?;
    let expression = parse_expression(tokens, 0)?;
    tokens.expect(Token::Semicolon)?;

    Ok(Statement::Return(expression))
}

fn parse_if(tokens: &mut TokenStream) -> Result<Statement> {
    tokens.expect(Token::If)?;
    tokens.expect(Token::OpenParen)?;
    let condition = parse_expression(tokens, 0)?;
    tokens.expect(Token::CloseParen)?;
    let then_statement = Box::new(parse_statement(tokens)?);
    let else_statement = match tokens.peek()? {
        Token::Else => {
            tokens.next()?;
            Some(Box::new(parse_statement(tokens)?))
        },
        _ => None
    };

    Ok(Statement::If(condition, then_statement, else_statement))
}

fn parse_statement(tokens: &mut TokenStream) -> Result<Statement> {
    let statement = match tokens.peek()? {
        Token::OpenBrace => Statement::Compound(parse_block(tokens)?),
        Token::Break => {
            tokens.expect(Token::Break)?;
            tokens.expect(Token::Semicolon)?;
            Statement::Break(temp_name("break"))
        },
        Token::Continue => {
            tokens.expect(Token::Continue)?;
            tokens.expect(Token::Semicolon)?;
            Statement::Continue(temp_name("continue"))
        },
        Token::While => {
            tokens.expect(Token::While)?;
            tokens.expect(Token::OpenParen)?;
            let expression = parse_expression(tokens, 0)?;
            tokens.expect(Token::CloseParen)?;
            let statement = parse_statement(tokens)?;
            Statement::While(expression, Box::new(statement), temp_name("while"))
        },
        Token::Do => {
            tokens.expect(Token::Do)?;
            let statement = parse_statement(tokens)?;
            tokens.expect(Token::While)?;
            tokens.expect(Token::OpenParen)?;
            let expression = parse_expression(tokens, 0)?;
            tokens.expect(Token::CloseParen)?;
            tokens.expect(Token::Semicolon)?;
            Statement::DoWhile(Box::new(statement), expression, temp_name("dowhile"))
        },
        Token::For => {
            tokens.expect(Token::For)?;
            tokens.expect(Token::OpenParen)?;
            let for_init = parse_for_init(tokens)?;
            let optional_exp1 = parse_optional_expression(tokens, Token::Semicolon)?;
            let optional_exp2 = parse_optional_expression(tokens, Token::CloseParen)?;
            let statement = parse_statement(tokens)?;
            Statement::For(for_init, optional_exp1, optional_exp2, Box::new(statement), temp_name("for"))
        },
        Token::Semicolon => parse_null(tokens)?,
        Token::Return => parse_return(tokens)?,
        Token::If => parse_if(tokens)?,
        _ => {
            let expression = parse_expression(tokens, 0)?;
            tokens.expect(Token::Semicolon)?;
            Statement::Expression(expression)
        }
    };

    Ok(statement)
}

fn parse_optional_expression(tokens: &mut TokenStream, expected: Token) -> Result<Option<Expression>> {
    let optional_expression = {
        if *tokens.peek()? == expected {
            tokens.expect(expected)?;
            None
        } else {
            let expression = parse_expression(tokens, 0)?;
            tokens.expect(expected)?;
            Some(expression)
        }
    };

    Ok(optional_expression)
}

fn parse_for_init(tokens: &mut TokenStream) -> Result<ForInit> {
    let for_init = match tokens.peek()? {
        Token::Int | Token::Long | Token::Static | Token::Extern => {
            let declaration = parse_declaration(tokens)?;
            match declaration {
                Declaration::FunDecl(_) => {
                    bail!("parse_for_init: Unexpected function declaration: {declaration:?}");
                },
                Declaration::VarDecl(variable_declaration) => ForInit::InitDecl(variable_declaration)
            }
        },
        _ => {
            let init_exp = parse_optional_expression(tokens, Token::Semicolon)?;
            ForInit::InitExp(init_exp)
        }
    };

    Ok(for_init)
}

#[rustfmt::skip]
fn parse_binary(tokens: &mut TokenStream) -> Result<BinaryOperator> {
    let token = tokens.next()?;
    let operator = match token {
        Token::Multiply         => BinaryOperator::Multiply,
        Token::Divide           => BinaryOperator::Divide,
        Token::Remainder        => BinaryOperator::Remainder,
        Token::Plus             => BinaryOperator::Plus,
        Token::Minus            => BinaryOperator::Minus,
        Token::Leftshift        => BinaryOperator::Leftshift,
        Token::Rightshift       => BinaryOperator::Rightshift,
        Token::BitAnd           => BinaryOperator::BitAnd,
        Token::BitOr            => BinaryOperator::BitOr,
        Token::BitXor           => BinaryOperator::BitXor,
        Token::And              => BinaryOperator::And,
        Token::Or               => BinaryOperator::Or,
        Token::Equal            => BinaryOperator::Equal,
        Token::NotEqual         => BinaryOperator::NotEqual,
        Token::LessThan         => BinaryOperator::LessThan,
        Token::LessOrEqual      => BinaryOperator::LessOrEqual,
        Token::GreaterThan      => BinaryOperator::GreaterThan,
        Token::GreaterOrEqual   => BinaryOperator::GreaterOrEqual,
        Token::PlusAssign       => BinaryOperator::Plus,
        Token::MinusAssign      => BinaryOperator::Minus,
        Token::MultiplyAssign   => BinaryOperator::Multiply,
        Token::DivideAssign     => BinaryOperator::Divide,
        Token::RemainderAssign  => BinaryOperator::Remainder,
        Token::BitAndAssign     => BinaryOperator::BitAnd,
        Token::BitOrAssign      => BinaryOperator::BitOr,
        Token::BitXorAssign     => BinaryOperator::BitXor,
        Token::LeftshiftAssign  => BinaryOperator::Leftshift,
        Token::RightshiftAssign => BinaryOperator::Rightshift,
        _ => bail!("Unexpected token for binary operator {token:?}"),
    };

    Ok(operator)
}

fn parse_unary(tokens: &mut TokenStream) -> Result<UnaryOperator> {
    let token = tokens.next()?;
    let operator = match token {
        Token::Complement => UnaryOperator::Complement,
        Token::Minus => UnaryOperator::Negate,
        Token::Not => UnaryOperator::Not,
        _ => bail!("Unexpected token for unary operator {token:?}")
    };

    Ok(operator)
}

fn parse_conditional_middle(tokens: &mut TokenStream) -> Result<Expression> {
    tokens.expect(Token::QuestionMark)?;
    let middle = parse_expression(tokens, 0)?;
    tokens.expect(Token::Colon)?;

    Ok(middle)
}

fn parse_expression(tokens: &mut TokenStream, min_precedence: i32) -> Result<Expression> {
    let mut left = parse_factor(tokens)?;
    let mut token = tokens.peek()?.clone();

    while token.is_binary_operator() && token.precedence() >= min_precedence {
        left = if token == Token::Assignment {
            tokens.next()?;
            let right = parse_expression(tokens, token.precedence())?;
            Expression::Assignment(Box::new(left), Box::new(right), Type::None)
        } else if token.is_compound_assignment() {
            let operator = parse_binary(tokens)?;
            let right = parse_expression(tokens, token.precedence())?;
            Expression::CompoundAssignment(operator, Box::new(left), Box::new(right), Type::None)
        } else if token == Token::QuestionMark {
            let middle = parse_conditional_middle(tokens)?;
            let right = parse_expression(tokens, token.precedence())?;
            Expression::Conditional(Box::new(left), Box::new(middle), Box::new(right), Type::None)
        } else {
            let operator = parse_binary(tokens)?;
            let right = parse_expression(tokens, token.precedence() + 1)?;
            Expression::Binary(operator, Box::new(left), Box::new(right), Type::None)
        };
        token = tokens.peek()?.clone();
    }

    Ok(left)
}

fn parse_function_call(tokens: &mut TokenStream, name: &String) -> Result<Expression> {
    let mut argument_list: FunctionArgs = Vec::new();

    tokens.expect(Token::OpenParen)?;
    while *tokens.peek()? != Token::CloseParen {
        let arg = parse_expression(tokens, 0)?;
        argument_list.push(arg);
        if *tokens.peek()? == Token::Comma {
            tokens.next()?;
            if *tokens.peek()? == Token::CloseParen {
                bail!("Unexpected trailing comma in function call: {name:?}");
            }
        }
    }
    tokens.next()?;

    let arguments = match argument_list.len() {
        0 => None,
        _ => Some(argument_list)
    };

    Ok(Expression::FunctionCall(name.to_string(), arguments, Type::None))
}

fn parse_factor(tokens: &mut TokenStream) -> Result<Expression> {
    let expression = match tokens.peek()?.clone() {
        token @ (Token::Constant(_) | Token::LConstant(_)) => {
            tokens.next()?;
            parse_constant(&token)?
        },
        Token::Identifier(name) => {
            tokens.next()?;
            match tokens.peek()? {
                Token::OpenParen => parse_function_call(tokens, &name)?,
                _ => Expression::Var(name, Type::None)
            }
        },
        Token::Complement | Token::Minus | Token::Not => {
            let operator = parse_unary(tokens)?;
            let inner_expression = parse_factor(tokens)?;
            Expression::Unary(operator, Box::new(inner_expression), Type::None)
        },
        Token::OpenParen => {
            tokens.next()?;
            match tokens.peek()? {
                Token::Int => {
                    tokens.next()?;
                    tokens.expect(Token::CloseParen)?;
                    let inner_expression = parse_factor(tokens)?;
                    Expression::Cast(Type::Int, Box::new(inner_expression), Type::None)
                },
                Token::Long => {
                    tokens.next()?;
                    tokens.expect(Token::CloseParen)?;
                    let inner_expression = parse_factor(tokens)?;
                    Expression::Cast(Type::Long, Box::new(inner_expression), Type::None)
                },
                _ => {
                    let inner_expression = parse_expression(tokens, 0)?;
                    tokens.expect(Token::CloseParen)?;
                    inner_expression
                }
            }
        },
        token => bail!("parse_expression: Unexpected token: '{token:?}'")
    };

    Ok(expression)
}
