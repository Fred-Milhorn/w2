//! w2 - A tiny C complier
//!
//! With guidance from the book "Writing a C Compiler" by Nora Sandler
//!
//! # Summary
//!
//! Given one C file on the command line, create a macOS executable. GCC is doing the
//! work of preprocessing and compiling the generated assembly language. All the lexing, parsing,
//! and assembly language creation is done by this program, w2.
//!
//! # Explaination
//!
//! You may ask, why Rust? The driver (our main.rs here) could have so much more easily
//! been written in bash. Or Python. Rust makes this so much bigger and more complicated
//! than pretty much any other reasonable option. Well, I just wanted to write it in Rust
//! because I've wanted to write a C compiler for a long time (years), and I wanted to
//! have a real, substative project in Rust so I could better learn the language.

use anyhow::{Result, bail};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

mod arm64;
mod code;
mod convert;
mod lex;
mod parse;
mod tacky;
mod target;
mod utils;
mod validate;
use target::Target;

#[derive(Debug, Default)]
struct Opts {
    debug:    bool,
    lex:      bool,
    parse:    bool,
    validate: bool,
    tacky:    bool,
    codegen:  bool,
    emitcode: bool,
    compile:  bool,
    target:   Option<Target>,
    files:    Vec<PathBuf>
}

fn usage(msg: &str) -> ! {
    eprintln!("{msg}\nUsage: w2 [options] file ...");
    std::process::exit(1);
}

#[rustfmt::skip]
fn main() -> Result<()> {
    let mut opts = Opts::default();
    let args = env::args().skip(1).collect::<Vec<_>>();
    let mut index = 0;

    while index < args.len() {
        let option = &args[index];
        if !option.starts_with("-") {
            opts.files.push(option.into());
            index += 1;
            continue;
        }

        if let Some(target) = option.strip_prefix("--target=") {
            opts.target = Some(Target::parse(target)?);
            index += 1;
            continue;
        }

        match option.trim_start_matches('-') {
            "debug"    | "d" => opts.debug    = true,
            "lex"      | "l" => opts.lex      = true,
            "parse"    | "p" => opts.parse    = true,
            "validate" | "v" => opts.validate = true,
            "tacky"    | "t" => opts.tacky    = true,
            "codegen"  | "g" => opts.codegen  = true,
            "emitcode" | "e" => opts.emitcode = true,
            "compile"  | "m" | "c" => opts.compile  = true,
            "target" => {
                if index + 1 >= args.len() {
                    usage("Missing value for --target");
                }
                opts.target = Some(Target::parse(&args[index + 1])?);
                index += 1;
            },
            unknown => usage(&format!("Unknown option: {unknown:?}")),
        }
        index += 1;
    }

    let target = opts.target.unwrap_or(Target::host()?);
    opts.target = Some(target);

    if opts.debug {
        println!("{opts:?}");
    }
    
    if opts.files.is_empty() {
        usage("Need at least one file to compile");
    }

    for file in &opts.files {
        run(&opts, file, target)?;
    }

    Ok(())
}

fn run(opts: &Opts, file: &PathBuf, target: Target) -> Result<()> {
    if let Some(extension) = file.extension()
        && extension != "c"
    {
        bail!("Expected C source file: {file:?}");
    }

    let file_i = utils::preprocess(file, target)?;
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

    let validated_ast = validate::validate(ast)?;
    if opts.debug {
        println!("validate: {validated_ast:?}\n");
    }
    if opts.validate {
        process::exit(0);
    }

    let tacky = tacky::generate(&validated_ast)?;
    if opts.debug {
        println!("tacky: {tacky:?}\n");
    }
    if opts.tacky {
        process::exit(0);
    }

    let code = match target {
        Target::X86_64 => {
            let code = code::generate(&tacky)?;
            if opts.debug {
                println!("code: {:?}\n", code);
            }
            if opts.codegen {
                process::exit(0);
            }
            code::emit(&code)?
        },
        Target::Arm64 => {
            let code = arm64::generate(&tacky)?;
            if opts.debug {
                println!("code: {:?}\n", code);
            }
            if opts.codegen {
                process::exit(0);
            }
            arm64::emit(&code)?
        }
    };
    if opts.debug {
        println!("assembly:\n{code}\n");
    }
    if opts.emitcode {
        process::exit(0);
    }

    let file_s = file_i.with_extension("s");
    fs::write(&file_s, &code)?;

    if opts.compile {
        utils::create_object_file(&file_s, target)?;
    } else {
        utils::create_executable(&file_s, target)?;
    }

    Ok(())
}
