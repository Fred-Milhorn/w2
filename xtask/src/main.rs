use std::env;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

mod portable;

type TaskResult<T> = Result<T, String>;

#[derive(Debug, Default)]
struct TestOptions {
    chapter:      Option<String>,
    stage:        Option<String>,
    latest_only:  bool,
    target:       Option<String>,
    failfast:     bool,
    backtrace:    bool,
    verbose:      u8,
    extra_credit: bool,
    increment:    bool,
    goto:         bool,
    switch:       bool
}

fn print_help() {
    eprintln!(
        "Usage: cargo xtask <command> [options]\n\
         Commands:\n\
           test          Run chapter tests\n\
           test-portable Run architecture-agnostic subset without Python harness\n\
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
           -v, --verbose    Enable verbose mode (repeat for more detail)\n\
           --latest-only    Run tests for the selected chapter only\n\
           --target T       Pass backend target to compiler under test (x86_64|arm64)\n\
           -f, --failfast   Stop on first test failure\n\
           -b, --backtrace  Force RUST_BACKTRACE=1 while running harness\n\
           --extra-credit    Include all extra-credit tests\n\
           --increment       Include tests for increment/decrement operators\n\
           --goto            Include tests for goto and labeled statements\n\
           --switch          Include tests for switch statements\n\
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnitOutcome {
    Ok,
    Failed,
    Ignored
}

impl UnitOutcome {
    fn as_cargo_word(&self) -> &'static str {
        match self {
            UnitOutcome::Ok => "ok",
            UnitOutcome::Failed => "FAILED",
            UnitOutcome::Ignored => "ignored"
        }
    }

    fn as_colored_cargo_word(&self, use_color: bool) -> String {
        let word = self.as_cargo_word();
        if !use_color {
            return word.to_string();
        }
        match self {
            UnitOutcome::Ok => format!("\x1b[32m{word}\x1b[0m"),
            UnitOutcome::Failed => format!("\x1b[31m{word}\x1b[0m"),
            UnitOutcome::Ignored => word.to_string()
        }
    }
}

#[derive(Debug)]
struct AdaptedCaseLine {
    name:    String,
    outcome: UnitOutcome
}

#[derive(Debug, Default)]
struct AdaptedSummary {
    total:    usize,
    passed:   usize,
    failed:   usize,
    ignored:  usize,
    duration: Option<String>
}

fn color_enabled_for_stdout() -> bool {
    if env::var_os("NO_COLOR").is_some() {
        return false;
    }
    if matches!(env::var("CLICOLOR"), Ok(value) if value == "0") {
        return false;
    }
    std::io::stdout().is_terminal()
}

fn parse_unittest_case_line(line: &str) -> Option<AdaptedCaseLine> {
    let (lhs, rhs) = line.rsplit_once(" ... ")?;
    let name = lhs.split_once(" (").map(|(prefix, _)| prefix).unwrap_or(lhs).trim();
    if name.is_empty() {
        return None;
    }

    let status = rhs.trim();
    let outcome = if status == "ok" {
        UnitOutcome::Ok
    } else if status == "FAIL" || status == "ERROR" {
        UnitOutcome::Failed
    } else if status.starts_with("skipped") {
        UnitOutcome::Ignored
    } else {
        return None;
    };

    Some(AdaptedCaseLine { name: name.to_string(), outcome })
}

fn parse_unittest_ran_line(line: &str) -> Option<(usize, String)> {
    let trimmed = line.trim();
    let body = trimmed.strip_prefix("Ran ")?;
    let (count_str, duration) = if let Some(parts) = body.split_once(" tests in ") {
        parts
    } else {
        body.split_once(" test in ")?
    };
    let total = count_str.parse::<usize>().ok()?;
    Some((total, duration.trim().to_string()))
}

fn parse_unittest_stream(stream: &str) -> (Vec<AdaptedCaseLine>, Vec<String>, Option<String>) {
    let mut tests = Vec::<AdaptedCaseLine>::new();
    let mut passthrough = Vec::<String>::new();
    let mut duration = None::<String>;

    for line in stream.lines() {
        if let Some(test_line) = parse_unittest_case_line(line) {
            tests.push(test_line);
            continue;
        }
        if let Some((_, parsed_duration)) = parse_unittest_ran_line(line) {
            duration = Some(parsed_duration);
            continue;
        }

        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed == "OK"
            || trimmed.starts_with("FAILED")
            || (!trimmed.is_empty() && trimmed.chars().all(|ch| ch == '-'))
            || (!trimmed.is_empty()
                && trimmed.chars().all(|ch| matches!(ch, '.' | 'F' | 'E' | 's')))
        {
            continue;
        }
        passthrough.push(line.to_string());
    }

    (tests, passthrough, duration)
}

fn emit_cargo_style_output(stdout: &str, stderr: &str, exit_code: i32) -> i32 {
    let use_color = color_enabled_for_stdout();
    let (stdout_tests, stdout_passthrough, stdout_duration) = parse_unittest_stream(stdout);
    let (stderr_tests, stderr_passthrough, stderr_duration) = parse_unittest_stream(stderr);

    let (tests, mut passthrough, duration, other_stream) =
        if stderr_tests.len() > stdout_tests.len() {
            (stderr_tests, stderr_passthrough, stderr_duration, Some(stdout.to_string()))
        } else {
            (stdout_tests, stdout_passthrough, stdout_duration, Some(stderr.to_string()))
        };

    if tests.is_empty() {
        print!("{stdout}");
        eprint!("{stderr}");
        return exit_code;
    }

    let mut summary = AdaptedSummary { total: tests.len(), ..AdaptedSummary::default() };
    summary.duration = duration.or_else(|| Some("0.00s".to_string()));

    println!("running {} tests", summary.total);
    for test in &tests {
        match test.outcome {
            UnitOutcome::Ok => summary.passed += 1,
            UnitOutcome::Failed => summary.failed += 1,
            UnitOutcome::Ignored => summary.ignored += 1
        }
        println!("test {} ... {}", test.name, test.outcome.as_colored_cargo_word(use_color));
    }

    if let Some(extra) = other_stream {
        for line in extra.lines() {
            if line.trim().is_empty() {
                continue;
            }
            passthrough.push(line.to_string());
        }
    }

    if !passthrough.is_empty() {
        println!();
        for line in passthrough {
            println!("{line}");
        }
    }

    let duration_str = summary.duration.unwrap_or_else(|| "0.00s".to_string());
    let result_word = if summary.failed == 0 { "ok" } else { "FAILED" };
    let result_word = if use_color {
        if summary.failed == 0 {
            format!("\x1b[32m{result_word}\x1b[0m")
        } else {
            format!("\x1b[31m{result_word}\x1b[0m")
        }
    } else {
        result_word.to_string()
    };
    println!(
        "\ntest result: {result_word}. {} passed; {} failed; {} ignored; 0 measured; 0 filtered out; finished in {}",
        summary.passed, summary.failed, summary.ignored, duration_str
    );
    exit_code
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
                opts.verbose = opts.verbose.saturating_add(1);
                ix += 1;
            },
            "--latest-only" => {
                opts.latest_only = true;
                ix += 1;
            },
            "--target" => {
                if ix + 1 >= raw_args.len() || raw_args[ix + 1].starts_with('-') {
                    return Err("target is required".to_string());
                }
                opts.target = Some(raw_args[ix + 1].clone());
                ix += 2;
            },
            value if value.starts_with("--target=") => {
                let target = value.trim_start_matches("--target=").to_string();
                if target.is_empty() {
                    return Err("target is required".to_string());
                }
                opts.target = Some(target);
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
            "--extra-credit" => {
                opts.extra_credit = true;
                ix += 1;
            },
            "--increment" => {
                opts.increment = true;
                ix += 1;
            },
            "--goto" => {
                opts.goto = true;
                ix += 1;
            },
            "--switch" => {
                opts.switch = true;
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
    if !opts.increment {
        opts.increment = truthy_env("INCREMENT");
    }
    if !opts.goto {
        opts.goto = truthy_env("GOTO");
    }
    if !opts.switch {
        opts.switch = truthy_env("SWITCH");
    }
    if !opts.extra_credit {
        opts.extra_credit = truthy_env("EXTRA_CREDIT");
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
    if opts.latest_only {
        command.arg("--latest-only");
    }

    if let Some(stage) = opts.stage {
        command.arg("--stage").arg(stage);
    }
    if opts.failfast {
        command.arg("--failfast");
    }
    if opts.verbose > 0 {
        for _ in 0..(opts.verbose + 1) {
            command.arg("--verbose");
        }
    }
    if opts.extra_credit {
        command.arg("--extra-credit");
    }
    if opts.increment {
        command.arg("--increment");
    }
    if opts.goto {
        command.arg("--goto");
    }
    if opts.switch {
        command.arg("--switch");
    }
    if opts.backtrace {
        command.env("RUST_BACKTRACE", "1");
    }
    if let Some(target) = opts.target {
        command.arg("--").arg("--target").arg(target);
    }

    if opts.verbose == 0 {
        return run_and_forward_exit(&mut command);
    }

    match command.output() {
        Ok(output) => {
            let code = output.status.code().unwrap_or(1);
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            Ok(emit_cargo_style_output(&stdout, &stderr, code))
        },
        Err(err) => Err(format!("Failed to run command {:?}: {err}", command))
    }
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
        "test-portable" => portable::run(&args),
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

#[cfg(test)]
mod tests {
    use super::{
        UnitOutcome, parse_unittest_case_line, parse_unittest_ran_line, parse_unittest_stream
    };

    #[test]
    fn parses_unittest_case_line() {
        let parsed = parse_unittest_case_line(
            "test_invalid_parse/missing_type (test_framework.basic.TestChapter1.test_invalid_parse/missing_type) ... ok"
        )
        .expect("case line should parse");
        assert_eq!(parsed.name, "test_invalid_parse/missing_type");
        assert_eq!(parsed.outcome, UnitOutcome::Ok);
    }

    #[test]
    fn parses_unittest_ran_line() {
        let (total, duration) =
            parse_unittest_ran_line("Ran 24 tests in 1.695s").expect("ran line should parse");
        assert_eq!(total, 24);
        assert_eq!(duration, "1.695s");
    }

    #[test]
    fn parses_unittest_stream_case_lines() {
        let output = "test_valid/foo (suite.case) ... ok\nRan 1 test in 0.123s\nOK\n";
        let (tests, passthrough, duration) = parse_unittest_stream(output);
        assert_eq!(tests.len(), 1);
        assert_eq!(tests[0].name, "test_valid/foo");
        assert_eq!(tests[0].outcome, UnitOutcome::Ok);
        assert!(passthrough.is_empty());
        assert_eq!(duration.as_deref(), Some("0.123s"));
    }
}
