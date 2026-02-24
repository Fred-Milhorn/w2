use std::env;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

type TaskResult<T> = Result<T, String>;

#[derive(Debug, Default)]
struct TestOptions {
    chapter:   Option<String>,
    stage:     Option<String>,
    failfast:  bool,
    backtrace: bool,
    verbose:   bool
}

fn print_help() {
    eprintln!(
        "Usage: cargo xtask <command> [options]\n\
         Commands:\n\
           test          Run chapter tests\n\
           test-init     Initialize chapter-test submodule\n\
           test-update   Update chapter-test submodule pointer\n\
           test-status   Show chapter-test submodule status\n\
         \n\
         Run `cargo xtask test --help` for test options."
    );
}

fn print_test_help() {
    eprintln!(
        "Usage: cargo xtask test [OPTIONS]\n\
         Options:\n\
           -h, --help       Show this help message\n\
           -v, --verbose    Enable verbose mode for harness output\n\
           -f, --failfast   Stop on first test failure\n\
           -b, --backtrace  Force RUST_BACKTRACE=1 while running harness\n\
           -c, --chapter N  Chapter to run (or CHAPTER env var)\n\
           -s, --stage S    Stage to run (or STAGE env var)"
    );
}

fn truthy_env(name: &str) -> bool {
    match env::var(name) {
        Ok(value) => matches!(
            value.as_str(),
            "1" | "full" | "FULL" | "true" | "TRUE" | "yes" | "YES" | "on" | "ON"
        ),
        Err(_) => false
    }
}

fn non_empty_env(name: &str) -> Option<String> {
    match env::var(name) {
        Ok(value) if !value.trim().is_empty() => Some(value),
        _ => None
    }
}

fn repo_root() -> TaskResult<PathBuf> {
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let root = manifest_dir
        .parent()
        .ok_or_else(|| "Could not determine repo root from CARGO_MANIFEST_DIR".to_string())?;
    Ok(root.to_path_buf())
}

fn run_and_forward_exit(command: &mut Command) -> TaskResult<i32> {
    match command.status() {
        Ok(status) => Ok(status.code().unwrap_or(1)),
        Err(err) => Err(format!("Failed to run command {:?}: {err}", command))
    }
}

fn parse_test_args(raw_args: &[String]) -> TaskResult<(TestOptions, bool)> {
    let mut opts = TestOptions::default();
    let mut help_requested = false;
    let mut ix = 0;

    while ix < raw_args.len() {
        match raw_args[ix].as_str() {
            "-h" | "--help" => {
                help_requested = true;
                ix += 1;
            },
            "-v" | "--verbose" => {
                opts.verbose = true;
                ix += 1;
            },
            "-f" | "--failfast" => {
                opts.failfast = true;
                ix += 1;
            },
            "-b" | "--backtrace" => {
                opts.backtrace = true;
                ix += 1;
            },
            "-c" | "--chapter" => {
                if ix + 1 >= raw_args.len() || raw_args[ix + 1].starts_with('-') {
                    return Err("chapter number is required".to_string());
                }
                opts.chapter = Some(raw_args[ix + 1].clone());
                ix += 2;
            },
            value if value.starts_with("--chapter=") => {
                let chapter = value.trim_start_matches("--chapter=").to_string();
                if chapter.is_empty() {
                    return Err("chapter number is required".to_string());
                }
                opts.chapter = Some(chapter);
                ix += 1;
            },
            "-s" | "--stage" => {
                if ix + 1 >= raw_args.len() || raw_args[ix + 1].starts_with('-') {
                    return Err("stage name is required".to_string());
                }
                opts.stage = Some(raw_args[ix + 1].clone());
                ix += 2;
            },
            value if value.starts_with("--stage=") => {
                let stage = value.trim_start_matches("--stage=").to_string();
                if stage.is_empty() {
                    return Err("stage name is required".to_string());
                }
                opts.stage = Some(stage);
                ix += 1;
            },
            unknown => {
                return Err(format!("Invalid option for test: {unknown}"));
            }
        }
    }

    if opts.chapter.is_none() {
        opts.chapter = non_empty_env("CHAPTER");
    }
    if opts.stage.is_none() {
        opts.stage = non_empty_env("STAGE");
    }
    if !opts.failfast {
        opts.failfast = truthy_env("FAILFAST");
    }
    if !opts.backtrace {
        opts.backtrace = truthy_env("RUST_BACKTRACE");
    }

    Ok((opts, help_requested))
}

fn run_test(raw_args: &[String]) -> TaskResult<i32> {
    let (opts, help_requested) = parse_test_args(raw_args)?;
    if help_requested {
        print_test_help();
        return Ok(0);
    }

    let chapter =
        opts.chapter.ok_or_else(|| "Chapter is required. Use --chapter or CHAPTER.".to_string())?;
    let root = repo_root()?;
    let compiler = root.join("target/debug/w2");
    let harness_dir = root.join("writing-a-c-compiler-tests");
    let harness = harness_dir.join("test_compiler");

    if !compiler.exists() {
        return Err(format!(
            "Compiler binary not found at '{}'. Build it first with: cargo build",
            compiler.display()
        ));
    }
    if !harness_dir.is_dir() {
        return Err(format!(
            "Missing test harness directory '{}'. Initialize submodules first: cargo xtask test-init",
            harness_dir.display()
        ));
    }
    if !harness.exists() {
        return Err(format!(
            "Missing test harness runner '{}'. Initialize or update submodules: cargo xtask test-init",
            harness.display()
        ));
    }

    let mut command = Command::new(harness);
    command.current_dir(harness_dir);
    command.arg(&compiler).arg("--chapter").arg(chapter);

    if let Some(stage) = opts.stage {
        command.arg("--stage").arg(stage);
    }
    if opts.failfast {
        command.arg("--failfast");
    }
    if opts.verbose {
        command.arg("--verbose");
    }
    if opts.backtrace {
        command.env("RUST_BACKTRACE", "1");
    }

    run_and_forward_exit(&mut command)
}

fn run_git_submodule(args: &[&str]) -> TaskResult<i32> {
    let root = repo_root()?;
    let mut command = Command::new("git");
    command.current_dir(root);
    command.args(args);
    run_and_forward_exit(&mut command)
}

fn run_main() -> TaskResult<i32> {
    let mut args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        print_help();
        return Ok(1);
    }

    let command = args.remove(0);
    match command.as_str() {
        "test" => run_test(&args),
        "test-init" => run_git_submodule(&[
            "submodule",
            "update",
            "--init",
            "--recursive",
            "writing-a-c-compiler-tests"
        ]),
        "test-update" => run_git_submodule(&[
            "submodule",
            "update",
            "--remote",
            "--merge",
            "writing-a-c-compiler-tests"
        ]),
        "test-status" => {
            run_git_submodule(&["submodule", "status", "--recursive", "writing-a-c-compiler-tests"])
        },
        "-h" | "--help" | "help" => {
            print_help();
            Ok(0)
        },
        unknown => Err(format!("Unknown xtask command: {unknown}"))
    }
}

fn main() -> ExitCode {
    match run_main() {
        Ok(code) => ExitCode::from(code as u8),
        Err(err) => {
            eprintln!("{err}");
            ExitCode::from(1)
        }
    }
}
