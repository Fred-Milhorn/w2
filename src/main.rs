//! w2 - A tiny C complier
//!
//! With guidance from the book "Writing a C Compiler" by Nora Sandler
//!
//! # Summary
//!
//! Given one C file on the command line, create an x86 executable. GCC is doing the
//! work of preprocessing and compiling the x86 assembly language. All the lexing, parsing,
//! and assembly language creation is done by this program, wcc.
//!
//! # Explaination
//!
//! You may ask, why Rust? The driver (our main.rs here) could have so much more easily 
//! been written in bash. Or Python. Rust makes this so much bigger and more complicated
//! than pretty much any other reasonable option. Well, I just wanted to write it in Rust
//! because I've wanted to write a C compiler for a long time (years), and I wanted to
//! have a real, substative project in Rust so I could better learn the language.

// Apparently, this MUST be in the root crate. Used by utils::temp_name() only.
#[macro_use]
extern crate simple_counter;
generate_counter!(Counter, usize);

use std::fs;
use std::process;
use std::path::PathBuf;

use clap::Parser;
use anyhow::Result;

mod utils;
mod lex;
mod parse;
mod validate;
mod tacky;
//mod code;

#[derive(Parser, Debug)]
#[command(version, about = "The w2 tiny C compiler", long_about = None)]
pub struct Opts {
    #[arg(short, long, default_value_t = false, help = "Turn on debugging output")]
    pub debug:     bool,

    #[arg(long, default_value_t = false, help = "Exit after the lexer")]
    pub lex:       bool,

    #[arg(long, default_value_t = false, help = "Exit after the parser")]
    pub parse:     bool,

    #[arg(long, default_value_t = false, help = "Exit after validation")]
    pub validate:  bool,

    #[arg(long, default_value_t = false, help = "Exit after generating the IR")]
    pub tacky:     bool,

    #[arg(long, default_value_t = false, help = "Exit after generating abstract assembly")]
    pub codegen:   bool,

    #[arg(long, default_value_t = false, help = "Exit after generating x64 assembly language")]
    pub emitcode:  bool,

    #[arg(short, default_value_t = false, help = "Just produce an object file (.o)")]
    pub compile:   bool,

    pub files:     Vec<PathBuf>,
}

fn run(opts: &Opts, file: &PathBuf) -> Result<()> {
    // Let's just force our input file to a c source file.
    let file_c = file.with_extension("c");

    let file_i = utils::preprocess(&file_c)?;
    let source = fs::read_to_string(&file_i)?;

    let tokens = lex::lex(&source)?;
    if opts.debug {
	println!("lex: {:?}\n", tokens);
    }
    if opts.lex {
	process::exit(0);
    }

    let ast = parse::parse(&tokens)?;
    if opts.debug {
	println!("parse: {:?}\n", ast);
    }
    if opts.parse {
	process::exit(0);
    }

    let validated_ast = validate::validate(ast)?;
    if opts.debug {
	println!("validate: {:?}\n", validated_ast);
    }
    if opts.validate {
	process::exit(0);
    }

    let tacky = tacky::generate(&validated_ast)?;
    if opts.debug {
	println!("tacky: {:?}\n", tacky);
    }
    if opts.tacky {
	process::exit(0);
    }
    
    // let code = code::generate(&tacky);
    // if opts.debug {
    // 	println!("code: {:?}\n", code);
    // }
    // if opts.codegen {
    // 	process::exit(0);
    // }

    // let assembly = code::emit(&code)?;
    // if opts.debug {
    // 	println!("assembly: {assembly}\n");
    // }
    // if opts.emitcode {
    // 	process::exit(0);
    // }

    // let file_s = file_i.with_extension("s");
    // fs::write(&file_s, &assembly)?;

    // if opts.compile {
    // 	utils::create_object_file(&file_s)?;
    // } else {
    // 	utils::create_executable(&file_s)?;
    // }
    
    Ok(())
}

fn main() -> Result<()> {
    let opts = Opts::parse();

    for file in &opts.files {
	run(&opts, &file)?;
    }

    Ok(())
}
