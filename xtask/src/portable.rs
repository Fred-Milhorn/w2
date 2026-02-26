use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

type TaskResult<T> = Result<T, String>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stage {
    Lex,
    Parse,
    Validate,
    Tacky,
    Codegen,
    Run
}

impl Stage {
    fn parse(raw: &str) -> TaskResult<Self> {
        match raw.trim() {
            "lex" => Ok(Stage::Lex),
            "parse" => Ok(Stage::Parse),
            "validate" => Ok(Stage::Validate),
            "tacky" => Ok(Stage::Tacky),
            "codegen" => Ok(Stage::Codegen),
            "run" => Ok(Stage::Run),
            _ => Err(format!(
                "Invalid stage {raw:?}. Expected one of: lex, parse, validate, tacky, codegen, run"
            ))
        }
    }

    fn as_flag(&self) -> Option<&'static str> {
        match self {
            Stage::Lex => Some("--lex"),
            Stage::Parse => Some("--parse"),
            Stage::Validate => Some("--validate"),
            Stage::Tacky => Some("--tacky"),
            Stage::Codegen => Some("--codegen"),
            Stage::Run => None
        }
    }

    fn as_name(&self) -> &'static str {
        match self {
            Stage::Lex => "lex",
            Stage::Parse => "parse",
            Stage::Validate => "validate",
            Stage::Tacky => "tacky",
            Stage::Codegen => "codegen",
            Stage::Run => "run"
        }
    }
}

#[derive(Debug, Default)]
struct PortableOptions {
    chapter:      Option<u32>,
    stage:        Option<Stage>,
    latest_only:  bool,
    failfast:     bool,
    backtrace:    bool,
    verbose:      u8,
    extra_credit: bool,
    increment:    bool,
    goto:         bool,
    switch:       bool,
    target:       Option<String>
}

#[derive(Debug, Deserialize)]
struct ExpectedResult {
    return_code: i32,
    #[serde(default)]
    stdout:      String
}

#[derive(Debug, Deserialize)]
struct TestProperties {
    #[serde(default)]
    extra_credit_tests: HashMap<String, Vec<String>>,
    #[serde(default)]
    requires_mathlib:   Vec<String>,
    #[serde(default)]
    libs:               HashMap<String, Vec<String>>,
    #[serde(default)]
    assembly_libs:      HashMap<String, Vec<String>>
}

struct HarnessData {
    tests_dir:    PathBuf,
    compiler:     PathBuf,
    expected:     HashMap<String, ExpectedResult>,
    props:        TestProperties,
    chapter_dirs: Vec<PathBuf>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum CaseKind {
    Invalid,
    Valid
}

#[derive(Debug)]
struct TestCase {
    id:     String,
    source: PathBuf,
    kind:   CaseKind
}

#[derive(Debug, Default)]
struct Summary {
    total:         usize,
    valid_total:   usize,
    invalid_total: usize,
    passed:        usize,
    failed:        usize,
    skipped:       usize,
    failures:      Vec<FailureDetail>
}

#[derive(Debug)]
struct FailureDetail {
    test_id: String,
    message: String
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

fn colorize_status(word: &str, success: bool, use_color: bool) -> String {
    if !use_color {
        return word.to_string();
    }
    if success { format!("\x1b[32m{word}\x1b[0m") } else { format!("\x1b[31m{word}\x1b[0m") }
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

fn print_help() {
    eprintln!(
        "Usage: cargo xtask test-portable [OPTIONS]\n\
         Options:\n\
           -h, --help         Show this help message\n\
           -v, --verbose      Enable verbose output (repeat for more detail)\n\
           --latest-only      Run tests for selected chapter only\n\
           --target T         Pass backend target to compiler under test (x86_64|arm64)\n\
           -f, --failfast     Stop on first test failure\n\
           -b, --backtrace    Force RUST_BACKTRACE=1 for compiler invocations\n\
           --extra-credit     Include all extra-credit tests\n\
           --increment        Include increment/decrement extra-credit tests\n\
           --goto             Include goto/labeled-statement extra-credit tests\n\
           --switch           Include switch/case/default extra-credit tests\n\
           -c, --chapter N    Chapter to run (required; max 10)\n\
           -s, --stage S      Stage: lex|parse|validate|tacky|codegen|run (default run)"
    );
}

fn parse_target_arch(target: &str) -> TaskResult<&'static str> {
    match target.trim().to_ascii_lowercase().as_str() {
        "x86_64" | "x86-64" | "amd64" => Ok("x86_64"),
        "arm64" | "aarch64" => Ok("arm64"),
        _ => Err(format!(
            "Invalid target {target:?}. Expected one of: x86_64, x86-64, amd64, arm64, aarch64"
        ))
    }
}

fn parse_args(raw_args: &[String]) -> TaskResult<(PortableOptions, bool)> {
    let mut opts = PortableOptions::default();
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
                let value = value.trim_start_matches("--target=").to_string();
                if value.is_empty() {
                    return Err("target is required".to_string());
                }
                opts.target = Some(value);
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
                opts.chapter = Some(
                    raw_args[ix + 1]
                        .parse::<u32>()
                        .map_err(|_| format!("Invalid chapter: {:?}", raw_args[ix + 1]))?
                );
                ix += 2;
            },
            value if value.starts_with("--chapter=") => {
                let chapter = value.trim_start_matches("--chapter=");
                opts.chapter = Some(
                    chapter.parse::<u32>().map_err(|_| format!("Invalid chapter: {chapter:?}"))?
                );
                ix += 1;
            },
            "-s" | "--stage" => {
                if ix + 1 >= raw_args.len() || raw_args[ix + 1].starts_with('-') {
                    return Err("stage name is required".to_string());
                }
                opts.stage = Some(Stage::parse(&raw_args[ix + 1])?);
                ix += 2;
            },
            value if value.starts_with("--stage=") => {
                let stage = value.trim_start_matches("--stage=");
                if stage.is_empty() {
                    return Err("stage name is required".to_string());
                }
                opts.stage = Some(Stage::parse(stage)?);
                ix += 1;
            },
            unknown => return Err(format!("Invalid option for test-portable: {unknown}"))
        }
    }

    if opts.chapter.is_none() {
        opts.chapter = non_empty_env("CHAPTER")
            .as_deref()
            .map(str::parse::<u32>)
            .transpose()
            .map_err(|_| "Invalid CHAPTER env var".to_string())?;
    }
    if opts.stage.is_none() {
        opts.stage = non_empty_env("STAGE").as_deref().map(Stage::parse).transpose()?;
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

fn read_json_file<T: for<'de> Deserialize<'de>>(path: &Path) -> TaskResult<T> {
    let raw = fs::read_to_string(path).map_err(|err| format!("Failed to read {path:?}: {err}"))?;
    serde_json::from_str::<T>(&raw).map_err(|err| format!("Failed to parse {path:?}: {err}"))
}

fn load_data(opts: &PortableOptions) -> TaskResult<HarnessData> {
    let chapter = opts.chapter.ok_or_else(|| "Chapter is required.".to_string())?;
    if chapter == 0 || chapter > 10 {
        return Err(format!(
            "test-portable currently supports chapters 1 through 10. Got chapter {chapter}. \
             See README.md section \"Portable Harness Scope\" for details."
        ));
    }

    if let Some(target) = &opts.target {
        let _ = parse_target_arch(target)?;
    }

    let root = repo_root()?;
    let tests_root = root.join("writing-a-c-compiler-tests");
    let tests_dir = tests_root.join("tests");
    let compiler = root.join("target/debug/w2");
    if !compiler.exists() {
        return Err(format!(
            "Compiler binary not found at '{}'. Build it first with: cargo build",
            compiler.display()
        ));
    }
    if !tests_dir.is_dir() {
        return Err(format!(
            "Missing test harness directory '{}'. Initialize submodules first: cargo xtask test-init",
            tests_root.display()
        ));
    }

    let chapter_dirs = if opts.latest_only {
        vec![tests_dir.join(format!("chapter_{chapter}"))]
    } else {
        (1..=chapter).map(|number| tests_dir.join(format!("chapter_{number}"))).collect::<Vec<_>>()
    };

    let expected = read_json_file::<HashMap<String, ExpectedResult>>(
        &tests_root.join("expected_results.json")
    )?;
    let props = read_json_file::<TestProperties>(&tests_root.join("test_properties.json"))?;

    Ok(HarnessData { tests_dir, compiler, expected, props, chapter_dirs })
}

fn enabled_extra_credit(feature: &str, opts: &PortableOptions) -> bool {
    if opts.extra_credit {
        return true;
    }
    match feature {
        "increment" => opts.increment,
        "goto" => opts.goto,
        "switch" => opts.switch,
        _ => false
    }
}

fn props_key(tests_dir: &Path, source_file: &Path) -> TaskResult<String> {
    let mut relative = source_file
        .strip_prefix(tests_dir)
        .map_err(|_| format!("Source is not under tests dir: {source_file:?}"))?
        .to_path_buf();

    let stem = source_file
        .file_stem()
        .and_then(|value| value.to_str())
        .ok_or_else(|| format!("Invalid source filename: {source_file:?}"))?;
    if let Some(base) = stem.strip_suffix("_client") {
        relative.set_file_name(format!("{base}.c"));
    }

    Ok(relative.to_string_lossy().replace('\\', "/"))
}

fn excluded_extra_credit(
    data: &HarnessData, source_file: &Path, key: &str, opts: &PortableOptions
) -> bool {
    if !source_file.components().any(|component| component.as_os_str() == "extra_credit") {
        return false;
    }
    let Some(required) = data.props.extra_credit_tests.get(key) else {
        return true;
    };
    required.iter().any(|feature| !enabled_extra_credit(feature, opts))
}

fn is_assembly_coupled(data: &HarnessData, key: &str) -> bool {
    data.props.assembly_libs.contains_key(key)
}

fn stage_invalid_dirs(stage: Stage) -> &'static [&'static str] {
    const ALL_INVALID: &[&str] = &[
        "invalid_lex",
        "invalid_parse",
        "invalid_semantics",
        "invalid_declarations",
        "invalid_types",
        "invalid_labels",
        "invalid_struct_tags"
    ];

    match stage {
        Stage::Lex => &["invalid_lex"],
        Stage::Parse => &["invalid_lex", "invalid_parse"],
        Stage::Validate | Stage::Tacky | Stage::Codegen | Stage::Run => ALL_INVALID
    }
}

fn stage_valid_dirs(stage: Stage) -> &'static [&'static str] {
    match stage {
        Stage::Lex => &[
            "invalid_parse",
            "invalid_semantics",
            "invalid_declarations",
            "invalid_types",
            "invalid_labels",
            "invalid_struct_tags",
            "valid"
        ],
        Stage::Parse => &[
            "invalid_semantics",
            "invalid_declarations",
            "invalid_types",
            "invalid_labels",
            "invalid_struct_tags",
            "valid"
        ],
        Stage::Validate | Stage::Tacky | Stage::Codegen | Stage::Run => &["valid"]
    }
}

fn collect_c_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if !dir.is_dir() {
        return files;
    }

    let mut stack = vec![dir.to_path_buf()];
    while let Some(path) = stack.pop() {
        let Ok(entries) = fs::read_dir(&path) else {
            continue;
        };
        for entry in entries.flatten() {
            let entry_path = entry.path();
            if entry_path.is_dir() {
                stack.push(entry_path);
            } else if entry_path.extension().and_then(|ext| ext.to_str()) == Some("c") {
                files.push(entry_path);
            }
        }
    }

    files.sort();
    files
}

fn discover_tests(
    data: &HarnessData, opts: &PortableOptions, stage: Stage
) -> TaskResult<(Vec<TestCase>, usize)> {
    let mut tests = Vec::new();
    let mut seen = HashSet::<(String, CaseKind)>::new();
    let mut skipped = 0;

    for chapter_dir in &data.chapter_dirs {
        for invalid_subdir in stage_invalid_dirs(stage) {
            let subdir = chapter_dir.join(invalid_subdir);
            for source in collect_c_files(&subdir) {
                let key = props_key(&data.tests_dir, &source)?;
                if excluded_extra_credit(data, &source, &key, opts)
                    || is_assembly_coupled(data, &key)
                {
                    skipped += 1;
                    continue;
                }
                let id = source
                    .strip_prefix(&data.tests_dir)
                    .map_err(|_| format!("Bad test path: {source:?}"))?
                    .to_string_lossy()
                    .replace('\\', "/");
                if seen.insert((id.clone(), CaseKind::Invalid)) {
                    tests.push(TestCase { id, source, kind: CaseKind::Invalid });
                }
            }
        }

        for valid_subdir in stage_valid_dirs(stage) {
            let subdir = chapter_dir.join(valid_subdir);
            for source in collect_c_files(&subdir) {
                let key = props_key(&data.tests_dir, &source)?;
                if excluded_extra_credit(data, &source, &key, opts)
                    || is_assembly_coupled(data, &key)
                {
                    skipped += 1;
                    continue;
                }
                let id = source
                    .strip_prefix(&data.tests_dir)
                    .map_err(|_| format!("Bad test path: {source:?}"))?
                    .to_string_lossy()
                    .replace('\\', "/");
                if seen.insert((id.clone(), CaseKind::Valid)) {
                    tests.push(TestCase { id, source, kind: CaseKind::Valid });
                }
            }
        }
    }

    Ok((tests, skipped))
}

fn compiler_invocation(
    data: &HarnessData, opts: &PortableOptions, source_file: &Path, stage: Stage,
    extra_compiler_opt: Option<&str>
) -> TaskResult<std::process::Output> {
    let mut command = Command::new(&data.compiler);
    if opts.backtrace {
        command.env("RUST_BACKTRACE", "1");
    }

    if let Some(target) = &opts.target {
        command.arg("--target").arg(target);
    }
    if let Some(stage_flag) = stage.as_flag() {
        command.arg(stage_flag);
    }
    if let Some(extra_option) = extra_compiler_opt {
        command.arg(extra_option);
    }
    command.arg(source_file);

    command.output().map_err(|err| format!("Failed to invoke compiler for {source_file:?}: {err}"))
}

fn ensure_no_output(source_file: &Path) -> TaskResult<()> {
    let assembly_file = source_file.with_extension("s");
    let executable_file = source_file.with_extension("");
    if assembly_file.exists() {
        return Err(format!(
            "Found assembly file {assembly_file:?} when testing invalid program or intermediate stage"
        ));
    }
    if executable_file.exists() {
        return Err(format!(
            "Found executable file {executable_file:?} when testing invalid program or intermediate stage"
        ));
    }
    Ok(())
}

fn cleanup_generated(source_file: &Path) {
    for extension in ["i", "s", "o"] {
        let path = source_file.with_extension(extension);
        if path.exists() {
            let _ = fs::remove_file(path);
        }
    }
    let executable = source_file.with_extension("");
    if executable.exists() {
        let _ = fs::remove_file(executable);
    }
}

fn verify_no_output_and_cleanup(source_file: &Path) -> TaskResult<()> {
    let result = ensure_no_output(source_file);
    cleanup_generated(source_file);
    result
}

fn get_c_libs(data: &HarnessData, source_file: &Path) -> TaskResult<Vec<PathBuf>> {
    let key = props_key(&data.tests_dir, source_file)?;
    let mut libs = Vec::new();
    if let Some(entries) = data.props.libs.get(&key) {
        for entry in entries {
            if entry.ends_with(".c") {
                libs.push(data.tests_dir.join(entry));
            }
        }
    }
    Ok(libs)
}

fn replace_stem(path: &Path, new_stem: &str) -> PathBuf {
    let extension = path.extension().and_then(|ext| ext.to_str());
    match extension {
        Some(ext) => path.with_file_name(format!("{new_stem}.{ext}")),
        None => path.with_file_name(new_stem)
    }
}

fn needs_mathlib(data: &HarnessData, source_file: &Path) -> TaskResult<bool> {
    if cfg!(target_os = "macos") {
        return Ok(false);
    }
    let key = props_key(&data.tests_dir, source_file)?;
    Ok(data.props.requires_mathlib.iter().any(|entry| entry == &key))
}

fn validation_key(data: &HarnessData, source_file: &Path) -> TaskResult<String> {
    props_key(&data.tests_dir, source_file)
}

fn validate_run_output(
    data: &HarnessData, source_file: &Path, run_output: &std::process::Output
) -> TaskResult<()> {
    let key = validation_key(data, source_file)?;
    let expected = data
        .expected
        .get(&key)
        .ok_or_else(|| format!("Missing expected result entry for {key:?}"))?;

    let return_code = run_output.status.code().unwrap_or(-1);
    if return_code != expected.return_code {
        return Err(format!(
            "Incorrect return code for {key}: expected {}, got {return_code}",
            expected.return_code
        ));
    }

    let stdout = String::from_utf8_lossy(&run_output.stdout).to_string();
    if stdout != expected.stdout {
        return Err(format!(
            "Incorrect stdout for {key}: expected {:?}, got {:?}",
            expected.stdout, stdout
        ));
    }

    if !run_output.stderr.is_empty() {
        return Err(format!(
            "Expected no stderr for {key}, got: {}",
            String::from_utf8_lossy(&run_output.stderr)
        ));
    }

    Ok(())
}

fn run_executable(executable: &Path) -> TaskResult<std::process::Output> {
    Command::new(executable)
        .output()
        .map_err(|err| format!("Failed to run executable {executable:?}: {err}"))
}

fn run_library_case(
    data: &HarnessData, opts: &PortableOptions, file_under_test: &Path, other_files: &[PathBuf]
) -> TaskResult<()> {
    let compile_result =
        compiler_invocation(data, opts, file_under_test, Stage::Run, Some("--compile"))?;
    if !compile_result.status.success() {
        cleanup_generated(file_under_test);
        return Err(format!(
            "Compilation of {file_under_test:?} failed:\n{}",
            String::from_utf8_lossy(&compile_result.stderr)
        ));
    }

    let compiled_file = file_under_test.with_extension("o");
    let executable = file_under_test.with_extension("");

    let mut command = Command::new("gcc");
    if let Some(target) = &opts.target {
        let arch = parse_target_arch(target)?;
        command.arg("-arch").arg(arch);
    }
    command.arg("-D").arg("SUPPRESS_WARNINGS").arg(&compiled_file);
    for source in other_files {
        command.arg(source);
    }

    let mut other_requires_mathlib = false;
    for path in other_files {
        if needs_mathlib(data, path)? {
            other_requires_mathlib = true;
            break;
        }
    }

    if needs_mathlib(data, file_under_test)? || other_requires_mathlib {
        command.arg("-lm");
    }

    command.arg("-o").arg(&executable);
    let link_result = command
        .output()
        .map_err(|err| format!("Failed to run gcc for {file_under_test:?}: {err}"))?;
    if !link_result.status.success() {
        cleanup_generated(file_under_test);
        return Err(format!(
            "Link failed for {file_under_test:?}:\n{}",
            String::from_utf8_lossy(&link_result.stderr)
        ));
    }

    let run_output = run_executable(&executable)?;
    let validate_result = validate_run_output(data, file_under_test, &run_output);
    cleanup_generated(file_under_test);
    validate_result
}

fn run_valid_case(
    data: &HarnessData, opts: &PortableOptions, source_file: &Path, stage: Stage
) -> TaskResult<()> {
    if stage != Stage::Run {
        let result = compiler_invocation(data, opts, source_file, stage, None)?;
        let status_ok = result.status.success();
        if !status_ok {
            cleanup_generated(source_file);
            return Err(format!(
                "Compilation of {source_file:?} failed:\n{}",
                String::from_utf8_lossy(&result.stderr)
            ));
        }
        return verify_no_output_and_cleanup(source_file);
    }

    let relative = source_file
        .strip_prefix(&data.tests_dir)
        .map_err(|_| format!("Source is not under tests dir: {source_file:?}"))?;
    let in_libraries = relative.components().any(|component| component.as_os_str() == "libraries");

    let extra_libs = get_c_libs(data, source_file)?;
    if in_libraries {
        let stem = source_file
            .file_stem()
            .and_then(|value| value.to_str())
            .ok_or_else(|| format!("Bad source filename: {source_file:?}"))?;

        let mut others = Vec::<PathBuf>::new();
        if let Some(base) = stem.strip_suffix("_client") {
            others.push(replace_stem(source_file, base));
        } else {
            others.push(replace_stem(source_file, &(stem.to_string() + "_client")));
        }
        others.extend(extra_libs);
        return run_library_case(data, opts, source_file, &others);
    }

    if !extra_libs.is_empty() {
        return run_library_case(data, opts, source_file, &extra_libs);
    }

    let compile_result = compiler_invocation(data, opts, source_file, Stage::Run, None)?;
    let status_ok = compile_result.status.success();
    if !status_ok {
        cleanup_generated(source_file);
        return Err(format!(
            "Compilation of {source_file:?} failed:\n{}",
            String::from_utf8_lossy(&compile_result.stderr)
        ));
    }

    let executable = source_file.with_extension("");
    let run_output = run_executable(&executable)?;
    let validate_result = validate_run_output(data, source_file, &run_output);
    cleanup_generated(source_file);
    validate_result
}

fn run_invalid_case(
    data: &HarnessData, opts: &PortableOptions, source_file: &Path, stage: Stage
) -> TaskResult<()> {
    let result = compiler_invocation(data, opts, source_file, stage, None)?;
    let status_ok = result.status.success();
    if status_ok {
        cleanup_generated(source_file);
        return Err(format!("Expected compilation failure for {source_file:?}"));
    }
    verify_no_output_and_cleanup(source_file)
}

fn run_case(
    data: &HarnessData, opts: &PortableOptions, test: &TestCase, stage: Stage
) -> TaskResult<()> {
    match test.kind {
        CaseKind::Invalid => run_invalid_case(data, opts, &test.source, stage),
        CaseKind::Valid => run_valid_case(data, opts, &test.source, stage)
    }
}

fn run_all(
    data: &HarnessData, opts: &PortableOptions, tests: &[TestCase], skipped: usize, stage: Stage,
    use_color: bool
) -> Summary {
    let invalid_total = tests.iter().filter(|test| test.kind == CaseKind::Invalid).count();
    let valid_total = tests.len().saturating_sub(invalid_total);
    let mut summary =
        Summary { total: tests.len(), valid_total, invalid_total, skipped, ..Summary::default() };

    for test in tests {
        let result = run_case(data, opts, test, stage);
        match result {
            Ok(()) => {
                summary.passed += 1;
                if opts.verbose > 0 {
                    println!("test {} ... {}", test.id, colorize_status("ok", true, use_color));
                }
            },
            Err(message) => {
                summary.failed += 1;
                if opts.verbose > 0 {
                    println!(
                        "test {} ... {}",
                        test.id,
                        colorize_status("FAILED", false, use_color)
                    );
                    summary.failures.push(FailureDetail { test_id: test.id.clone(), message });
                } else {
                    eprintln!("[FAIL] {}\n{}", test.id, message);
                }
                if opts.failfast {
                    break;
                }
            }
        }
    }

    summary
}

pub fn run(raw_args: &[String]) -> TaskResult<i32> {
    let (opts, help_requested) = parse_args(raw_args)?;
    if help_requested {
        print_help();
        return Ok(0);
    }

    let stage = opts.stage.unwrap_or(Stage::Run);
    let data = load_data(&opts)?;
    let (tests, skipped) = discover_tests(&data, &opts, stage)?;
    let started = Instant::now();
    let use_color = color_enabled_for_stdout();
    if opts.verbose > 0 {
        println!("running {} tests", tests.len());
    }
    let summary = run_all(&data, &opts, &tests, skipped, stage, use_color);

    if opts.verbose > 0 {
        if !summary.failures.is_empty() {
            println!("\nfailures:\n");
            for failure in &summary.failures {
                println!("---- {} ----", failure.test_id);
                println!("{}", failure.message);
                println!();
            }
        }
        let result_word = if summary.failed == 0 { "ok" } else { "FAILED" };
        let result_word = colorize_status(result_word, summary.failed == 0, use_color);
        println!(
            "test result: {result_word}. {} passed; {} failed; {} ignored; 0 measured; 0 filtered out; finished in {:.2}s",
            summary.passed,
            summary.failed,
            summary.skipped,
            started.elapsed().as_secs_f64()
        );
        let target = opts.target.as_deref().unwrap_or("host");
        println!(
            "portable metadata: stage={} target={} skipped_by_filters={}",
            stage.as_name(),
            target,
            summary.skipped
        );
    } else {
        println!(
            "portable summary: total={} valid={} invalid={} passed={} failed={} skipped={}",
            summary.total,
            summary.valid_total,
            summary.invalid_total,
            summary.passed,
            summary.failed,
            summary.skipped
        );
    }

    if summary.failed == 0 { Ok(0) } else { Ok(1) }
}

#[cfg(test)]
mod tests {
    use super::{PortableOptions, Stage, enabled_extra_credit, parse_target_arch, props_key};
    use std::path::Path;

    #[test]
    fn stage_parser_accepts_known_values() {
        assert!(matches!(Stage::parse("lex"), Ok(Stage::Lex)));
        assert!(matches!(Stage::parse("parse"), Ok(Stage::Parse)));
        assert!(matches!(Stage::parse("validate"), Ok(Stage::Validate)));
        assert!(matches!(Stage::parse("tacky"), Ok(Stage::Tacky)));
        assert!(matches!(Stage::parse("codegen"), Ok(Stage::Codegen)));
        assert!(matches!(Stage::parse("run"), Ok(Stage::Run)));
    }

    #[test]
    fn target_parser_accepts_aliases() {
        assert_eq!(parse_target_arch("x86_64").expect("x86_64"), "x86_64");
        assert_eq!(parse_target_arch("amd64").expect("amd64"), "x86_64");
        assert_eq!(parse_target_arch("arm64").expect("arm64"), "arm64");
        assert_eq!(parse_target_arch("aarch64").expect("aarch64"), "arm64");
    }

    #[test]
    fn props_key_maps_client_to_library_key() {
        let tests_dir = Path::new("/tmp/tests");
        let source = Path::new("/tmp/tests/chapter_10/valid/libraries/foo_client.c");
        let key = props_key(tests_dir, source).expect("props key");
        assert_eq!(key, "chapter_10/valid/libraries/foo.c");
    }

    #[test]
    fn extra_credit_defaults_disabled() {
        let opts = PortableOptions::default();
        assert!(!enabled_extra_credit("increment", &opts));
        assert!(!enabled_extra_credit("goto", &opts));
        assert!(!enabled_extra_credit("switch", &opts));
    }

    #[test]
    fn extra_credit_flag_enables_all_features() {
        let opts = PortableOptions { extra_credit: true, ..PortableOptions::default() };
        assert!(enabled_extra_credit("increment", &opts));
        assert!(enabled_extra_credit("goto", &opts));
        assert!(enabled_extra_credit("switch", &opts));
        assert!(enabled_extra_credit("bitwise", &opts));
    }
}
