//! lex.rs - Lexer for the w2 tiny C compiler

use anyhow::{anyhow, Result};
use once_cell::sync::Lazy;
use regex::Regex;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Eot,
    Identifier(String),
    Constant(String),
    LConstant(String),
    If,
    Else,
    QuestionMark,
    Colon,
    Int,
    Long,
    Void,
    Return,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    Semicolon,
    Complement,
    Decrement,
    Increment,
    Minus,
    Plus,
    Multiply,
    Divide,
    Remainder,
    BitAnd,
    BitOr,
    BitXor,
    Leftshift,
    Rightshift,
    Not,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessOrEqual,
    GreaterOrEqual,
    Assignment,
    PlusAssign,
    MinusAssign,
    MultiplyAssign,
    DivideAssign,
    RemainderAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,
    LeftshiftAssign,
    RightshiftAssign,
    Do,
    While,
    For,
    Break,
    Continue,
    Comma,
    Static,
    Extern,
}

pub type TokenList = Vec<Token>;

#[rustfmt::skip]
impl Token {
    pub fn precedence(&self) -> i32 {
        match self {
            Token::Increment        => 0,
            Token::Decrement        => 0,
            Token::Multiply         => 50,
            Token::Divide           => 50,
            Token::Remainder        => 50,
            Token::Plus             => 45,
            Token::Minus            => 45,
            Token::Leftshift        => 40,
            Token::Rightshift       => 40,
            Token::LessThan         => 35,
            Token::LessOrEqual      => 35,
            Token::GreaterThan      => 35,
            Token::GreaterOrEqual   => 35,
            Token::Equal            => 30,
            Token::NotEqual         => 30,
            Token::BitAnd           => 29,
            Token::BitXor           => 28,
            Token::BitOr            => 27,
            Token::And              => 10,
            Token::Or               => 5,
            Token::QuestionMark     => 3,
            Token::Assignment       => 1,
            Token::PlusAssign       => 1,
            Token::MinusAssign      => 1,
            Token::MultiplyAssign   => 1,
            Token::DivideAssign     => 1,
            Token::RemainderAssign  => 1,
            Token::BitAndAssign     => 1,
            Token::BitOrAssign      => 1,
            Token::BitXorAssign     => 1,
            Token::LeftshiftAssign  => 1,
            Token::RightshiftAssign => 1,
            _ => 0,
        }
    }

    pub fn is_binary_operator(&self) -> bool {
        matches!(
            self,
            Token::Multiply
                | Token::Divide
                | Token::Remainder
                | Token::Plus
                | Token::Minus
                | Token::BitAnd
                | Token::BitOr
                | Token::BitXor
                | Token::Leftshift
                | Token::Rightshift
                | Token::And
                | Token::Or
                | Token::Equal
                | Token::NotEqual
                | Token::LessThan
                | Token::LessOrEqual
                | Token::GreaterThan
                | Token::GreaterOrEqual
                | Token::Assignment
                | Token::PlusAssign
                | Token::MinusAssign
                | Token::MultiplyAssign
                | Token::DivideAssign
                | Token::RemainderAssign
                | Token::BitAndAssign
                | Token::BitOrAssign
                | Token::BitXorAssign
                | Token::LeftshiftAssign
                | Token::RightshiftAssign
                | Token::QuestionMark
        )
    }

    pub fn is_inc_dec(&self) -> bool {
        matches!(self, Token::Increment | Token::Decrement)
    }

    pub fn is_compound_assignment(&self) -> bool {
        matches!(
            self,
            Token::PlusAssign
                | Token::MinusAssign
                | Token::MultiplyAssign
                | Token::DivideAssign
                | Token::RemainderAssign
                | Token::BitAndAssign
                | Token::BitOrAssign
                | Token::BitXorAssign
                | Token::LeftshiftAssign
                | Token::RightshiftAssign
        )
    }
}

#[rustfmt::skip]
/// Create a list of tokens lexed from the c source
pub fn lex(input: &str) -> Result<TokenList> {
    static RE_IDENTIFIER: Lazy<Regex> = Lazy::new(|| Regex::new(r"^[a-zA-Z_]\w*\b").unwrap());
    static RE_LCONSTANT : Lazy<Regex> = Lazy::new(|| Regex::new(r"^[0-9]+[lL]\b").unwrap());
    static RE_CONSTANT  : Lazy<Regex> = Lazy::new(|| Regex::new(r"^[0-9]+\b").unwrap());
    static RE_SEPARATORS: Lazy<Regex> = Lazy::new(|| Regex::new(r"^[\,\{\}\(\)\;\?\:]").unwrap());
    static RE_OPERATORS1: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\+=|^\-=|^\*=|^/=|^\%=|^\&=|^\|=|^\^=|^<<=|^>>=").unwrap());
    static RE_OPERATORS2: Lazy<Regex> = Lazy::new(|| Regex::new(r"^\-\-|^\+\+|^&&|^<<|^>>|^\|\||^==|^!=|^<=|^>=").unwrap());
    static RE_OPERATORS3: Lazy<Regex> = Lazy::new(|| Regex::new(r"^[=!\-~+*/%|&^><]").unwrap());

    let mut tokens: TokenList = Vec::new();
    let mut start: usize = 0;

    while start < input.len() {
        let source = &input[start..];

        if source.as_bytes()[0].is_ascii_whitespace() {
            start += 1;
            continue;
        }

        let (token, length) = {
            if let Some(matched) = RE_IDENTIFIER.find(source) {
                let token = match matched.as_str() {
                    "if"       => Token::If,
                    "else"     => Token::Else,
                    "int"      => Token::Int,
                    "long"     => Token::Long,
                    "void"     => Token::Void,
                    "return"   => Token::Return,
                    "do"       => Token::Do,
                    "while"    => Token::While,
                    "for"      => Token::For,
                    "break"    => Token::Break,
                    "continue" => Token::Continue,
                    "static"   => Token::Static,
                    "extern"   => Token::Extern,
                    name => Token::Identifier(name.to_string()),
                };
                (token, matched.len())
            } else if let Some(matched) = RE_LCONSTANT.find(source) {
                let number_l = matched.as_str();
                let number = number_l[..number_l.len() - 1].to_string();
                let token = Token::LConstant(number);
                (token, matched.len())
            } else if let Some(matched) = RE_CONSTANT.find(source) {
                let number = matched.as_str().to_string();
                let token = Token::Constant(number);
                (token, matched.len())
            } else if let Some(matched) = RE_SEPARATORS.find(source) {
                let token = match matched.as_str() {
                    "(" => Token::OpenParen,
                    ")" => Token::CloseParen,
                    "{" => Token::OpenBrace,
                    "}" => Token::CloseBrace,
                    ";" => Token::Semicolon,
                    ":" => Token::Colon,
                    "?" => Token::QuestionMark,
                    "," => Token::Comma,
                    separator => return Err(anyhow!("Illegal separator: '{separator}'")),
                };
                (token, matched.len())
            } else if let Some(matched) = RE_OPERATORS1.find(source) {
                let token = match matched.as_str() {
                    "+="  => Token::PlusAssign,
                    "-="  => Token::MinusAssign,
                    "*="  => Token::MultiplyAssign,
                    "/="  => Token::DivideAssign,
                    "%="  => Token::RemainderAssign,
                    "&="  => Token::BitAndAssign,
                    "|="  => Token::BitOrAssign,
                    "^="  => Token::BitXorAssign,
                    "<<=" => Token::LeftshiftAssign,
                    ">>=" => Token::RightshiftAssign,
                    operator => return Err(anyhow!("Illegal operator: '{operator}'")),
                };
                (token, matched.len())
            } else if let Some(matched) = RE_OPERATORS2.find(source) {
                let token = match matched.as_str() {
                    "&&" => Token::And,
                    "||" => Token::Or,
                    "==" => Token::Equal,
                    "!=" => Token::NotEqual,
                    "<=" => Token::LessOrEqual,
                    ">=" => Token::GreaterOrEqual,
                    "<<" => Token::Leftshift,
                    ">>" => Token::Rightshift,
                    "--" => Token::Decrement,
                    "++" => Token::Increment,
                    operator => return Err(anyhow!("Illegal operator: '{operator}'")),
                };
                (token, matched.len())
            } else if let Some(matched) = RE_OPERATORS3.find(source) {
                let token = match matched.as_str() {
                    "<" => Token::LessThan,
                    ">" => Token::GreaterThan,
                    "!" => Token::Not,
                    "&" => Token::BitAnd,
                    "|" => Token::BitOr,
                    "^" => Token::BitXor,
                    "-" => Token::Minus,
                    "~" => Token::Complement,
                    "+" => Token::Plus,
                    "*" => Token::Multiply,
                    "/" => Token::Divide,
                    "%" => Token::Remainder,
                    "=" => Token::Assignment,
                    operator => return Err(anyhow!("Illegal operator: '{operator}'")),
                };
                (token, matched.len())
            } else {
                return Err(anyhow!("No tokens found"));
            }
        };

        tokens.push(token);
        start += length;
    }
    tokens.push(Token::Eot);

    Ok(tokens)
}
