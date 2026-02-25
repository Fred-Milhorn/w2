use anyhow::{Result, anyhow, bail};
use std::process::Command;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    X86_64,
    Arm64
}

#[cfg(test)]
mod tests {
    use super::Target;

    #[test]
    fn parses_known_targets() {
        assert_eq!(Target::parse("x86_64").expect("x86_64 should parse"), Target::X86_64);
        assert_eq!(Target::parse("amd64").expect("amd64 should parse"), Target::X86_64);
        assert_eq!(Target::parse("arm64").expect("arm64 should parse"), Target::Arm64);
        assert_eq!(Target::parse("aarch64").expect("aarch64 should parse"), Target::Arm64);
    }
}

impl Target {
    pub fn parse(value: &str) -> Result<Self> {
        match value.trim().to_ascii_lowercase().as_str() {
            "x86_64" | "x86-64" | "amd64" => Ok(Target::X86_64),
            "arm64" | "aarch64" => Ok(Target::Arm64),
            _ => bail!("Unknown target: {value:?} (expected x86_64 or arm64)")
        }
    }

    pub fn host() -> Result<Self> {
        if let Ok(output) = Command::new("uname").arg("-m").output()
            && output.status.success()
        {
            let machine = String::from_utf8_lossy(&output.stdout).trim().to_ascii_lowercase();
            match machine.as_str() {
                "x86_64" | "amd64" | "i386" => return Ok(Target::X86_64),
                "arm64" | "aarch64" => return Ok(Target::Arm64),
                _ => ()
            }
        }

        match std::env::consts::ARCH {
            "x86_64" => Ok(Target::X86_64),
            "aarch64" => Ok(Target::Arm64),
            other => Err(anyhow!("Unsupported host architecture: {other:?}"))
        }
    }

    pub fn arch_flag(&self) -> &'static str {
        match self {
            Target::X86_64 => "x86_64",
            Target::Arm64 => "arm64"
        }
    }
}
