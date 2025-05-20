//! utils.rs - Some useful utility functions to deal with command-line parsing
//!            and running sub-processes
//!
//! # Summary
//!
//! Most of these functions are very specific to what's needed by the w2 C compiler,
//! with run_cli() being an exception.

use std::path::PathBuf;
use std::process::Command;
use anyhow::{Context, Result, anyhow};

pub fn temp_name(prefix: &str) -> String {
    use crate::Counter;
    prefix.to_owned() + "." + &Counter::next().to_string()
}

#[allow(dead_code)]
pub fn mklabel(prefix: &str, suffix: &str) -> String {
    prefix.to_owned() + "_" + suffix
}

/// Preprocess the .c file to create a .i file.
///
/// We turn off the file/line numbering in the .i output since we can't
/// parse that (yet), and aren't otherwise tracking line numbers.
pub fn preprocess(file_c: &PathBuf) -> Result<PathBuf> {
    let file_i = file_c.with_extension("i");

    let mut preprocess = Command::new("gcc");
    preprocess.arg("-E").arg("-P").arg(file_c).arg("-o").arg(&file_i);
    run_cli(&mut preprocess)?;
    
    Ok(file_i)
}

/// Assemble the .s file into an executable file.
#[allow(dead_code)]
pub fn create_executable(file_s: &PathBuf) -> Result<PathBuf> {
    let file_exe = file_s.with_extension("");

    let mut assemble = Command::new("gcc");
    assemble.arg(file_s).arg("-o").arg(&file_exe);
    run_cli(&mut assemble)?;

    Ok(file_exe)
}

/// Assemble the .s file into an object file.
#[allow(dead_code)]
pub fn create_object_file(file_s: &PathBuf) -> Result<PathBuf> {
    let file_o = file_s.with_extension("o");

    let mut assemble = Command::new("gcc");
    assemble.arg("-c").arg(file_s).arg("-o").arg(&file_o);
    run_cli(&mut assemble)?;

    Ok(file_o)
}

/// Run a command line and handle various errors nicely.
pub fn run_cli(command: &mut Command) -> Result<()> {
    let result = match command.output() {
	Err(err) => Err(err.into()),
	Ok(output) => match output.status.code() {
	    Some(exit_code) => {
		match exit_code {
		    0 => Ok(()),
		    _ => Err(anyhow!("{}non-zero exit code: {exit_code}",
				     String::from_utf8_lossy(&output.stderr))),
		}
	    },
	    None => { // Apparently, this can happen.
		Err(anyhow!("Process terminated by signal"))
	    }
	}
    };

    // Debug formatter double-quotes all the args! ARGH!
    result.with_context(|| format!("{command:?}").replace("\"", ""))
}

