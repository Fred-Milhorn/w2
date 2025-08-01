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

use anyhow::{Result, bail};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

mod code;
mod convert;
mod lex;
mod parse;
mod tacky;
mod utils;
mod validate;

#[rustfmt::skip]
#[derive(Debug)]
struct Opts {
    debug:    bool,
    lex:      bool,
    parse:    bool,
    validate: bool,
    tacky:    bool,
    codegen:  bool,
    emitcode: bool,
    compile:  bool,
    files:    Vec<PathBuf>,
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}\nUsage: w2 [options] file ...");
    std::process::exit(1);
}

#[rustfmt::skip]
fn main() -> Result<()> {
    let mut opts = Opts {
        debug:    false,
        lex:      false,
        parse:    false,
        validate: false,
        tacky:    false,
        codegen:  false,
        emitcode: false,
        compile:  false,
        files:    Vec::new(),
    };

    for option in env::args().skip(1) {
        if option.starts_with("-") {
            match option.trim_start_matches('-') {
                "debug"    | "d" => opts.debug    = true,
                "lex"      | "l" => opts.lex      = true,
                "parse"    | "p" => opts.parse    = true,
                "validate" | "v" => opts.validate = true,
                "tacky"    | "t" => opts.tacky    = true,
                "codegen"  | "c" => opts.codegen  = true,
                "emitcode" | "e" => opts.emitcode = true,
                "compile"  | "m" => opts.compile  = true,
                unknown => usage(&format!("Unknown option: {unknown:?}")),
            }
        } else {
            opts.files.push(option.into());
        }
    }

    if opts.debug {
        println!("{opts:?}");
    }
    
    if opts.files.is_empty() {
        usage("Need at least one file to compile");
    }

    for file in &opts.files {
        run(&opts, file)?;
    }

    Ok(())
}

fn run(opts: &Opts, file: &PathBuf) -> Result<()> {
    if let Some(extension) = file.extension()
        && extension != "c"
    {
        bail!("Expected C source file: {file:?}");
    }

    let file_i = utils::preprocess(file)?;
    let source = fs::read_to_string(&file_i)?;

    let tokens = lex::lex(&source)?;
    if opts.debug {
        println!("lex: {tokens:?}\n");
    }
    if opts.lex {
        process::exit(0);
    }

    let ast = parse::parse(&tokens)?;
    if opts.debug {
        println!("parse: {ast:?}\n");
    }
    if opts.parse {
        process::exit(0);
    }

    let (validated_ast, mut symbol_table) = validate::validate(ast)?;
    if opts.debug {
        println!("validate: {validated_ast:?}\n");
    }
    if opts.validate {
        process::exit(0);
    }

    let tacky = tacky::generate(&validated_ast, &mut symbol_table)?;
    if opts.debug {
        println!("tacky: {tacky:?}\n");
    }
    if opts.tacky {
        process::exit(0);
    }

    let code = code::generate(&tacky, &symbol_table)?;
    if opts.debug {
        println!("code: {:?}\n", code);
    }
    if opts.codegen {
        process::exit(0);
    }

    let assembly = code::emit(&code)?;
    if opts.debug {
        println!("assembly:\n{assembly}\n");
    }
    if opts.emitcode {
        process::exit(0);
    }

    // let file_s = file_i.with_extension("s");
    // fs::write(&file_s, &assembly)?;

    // if opts.compile {
    //     utils::create_object_file(&file_s)?;
    // } else {
    //     utils::create_executable(&file_s)?;
    // }

    Ok(())
}
