use clap::{Parser, Subcommand, Args, ValueEnum};
use colored::Colorize;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
    #[arg(short, long)]
    pub verbose: bool,

    #[command(subcommand)]
    pub command: Option<Commands>, 

}

#[derive(Subcommand)]
pub enum Commands {
    Input {
        files: Vec<String>,

        #[arg(short, long)]
        output: Option<String>,

        #[command(flatten)]
        flags: InputFlags,

        #[arg(long = "ldflags", num_args=1..)]
        ldflags: Vec<String>,
    },

    ListTargets,
}

#[derive(Args, Debug, Default, Clone)]
pub struct InputFlags {
    #[arg(short, long)]
    pub verbose: bool,

    // a bit less type checks
    #[arg(long = "fpermissive")]
    pub permissive: bool,

    // Runs in check-only mode 
    // (so binaries wouldnt be generated)
    #[arg(long = "check")]
    pub check: bool,

    #[arg(short, long, default_value_t = Target::get_def())]
    pub target: Target,

    #[arg(long, default_value_t = def_ldas())]
    pub ldas: String,
}

fn def_ldas() -> String {
    #[cfg(target_os = "linux")]
    {
        return "gcc".to_string();
    }

    #[cfg(any(target_os = "macos", target_os = "freebsd"))]
    {
        return "clang".to_string();
    }

    // Fallback for other OSes
    "gcc".to_string()
}

#[derive(Clone, ValueEnum, Copy, Debug, Default, EnumIter)]
#[clap(rename_all = "snake_case")]
pub enum Target {
    #[default]
    Amd64Sysv,
    Amd64Win,
    Aarch64Apple,
    Aarch64Sysv,
    Riscv64Sysv,
}

impl Target {
    pub fn into_qbe_name(&self) -> String {
        match self {
            Target::Amd64Sysv => "amd64_sysv".into(),
            Target::Amd64Win => "amd64_win".into(),
            Target::Aarch64Apple => "arm64_apple".into(),
            Target::Aarch64Sysv => "arm64".into(),
            Target::Riscv64Sysv => "rv64".into(),
        }
    }

    pub fn get_def() -> Target {
        match (std::env::consts::ARCH, std::env::consts::OS) {
        ("x86_64", "linux") | ("x86_64", "freebsd") => Target::Amd64Sysv,
        ("x86_64", "windows") => Target::Amd64Win,
        ("aarch64", "macos") => Target::Aarch64Apple,
        ("aarch64", "linux") => Target::Aarch64Sysv,
        ("riscv64", "linux") => Target::Riscv64Sysv,
        _ => {
                println!("{}: unknown arch+os combination, using\
                amd64 SysV ABI as target.\n\
                {}: to list available targets, use `fencyc list-targets`;\n\
                you may specify needed target in compilation using `-t targetname` flag",
                "Warning".yellow(), "help".blue());

                Target::Amd64Sysv
            },
        }
    }

    pub fn list() {
        for target in Target::iter() {
            println!("{}", target.to_string());
        }
        println!("{}: {}", 
            "Default".green(),
            Self::get_def().to_string()
            );
    }
}

impl Into<String> for Target {
    fn into(self) -> String {
        match self {
            Target::Amd64Sysv    => "amd64_sysv"    .into(),
            Target::Amd64Win     => "amd64_win"     .into(),
            Target::Aarch64Apple => "aarch64_apple" .into(),
            Target::Aarch64Sysv  => "aarch64_sysv"  .into(),
            Target::Riscv64Sysv  => "riscv64_sysv"  .into(),
        }
    }
}

impl ToString for Target {
    fn to_string(&self) -> String {
        Into::<String>::into(*self)
    }
}
