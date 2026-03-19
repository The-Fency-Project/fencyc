use clap::{Parser, Subcommand, Args, ValueEnum};
use colored::Colorize;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
    #[arg(short, long, help = "Currently unused")]
    pub verbose: bool,

    #[command(subcommand)]
    pub command: Option<Commands>, 

}

#[derive(Subcommand)]
pub enum Commands {
    /// Compile some files
    Input {
        #[arg(help = "List input .fcy source code files")]
        files: Vec<String>,

        #[arg(short, long, help = "Specify output filename")]
        output: Option<String>,

        #[command(flatten)]
        flags: InputFlags,

        #[arg(long = "ldflags", num_args=1.., help = "Linker flags (dashes prepended)")]
        ldflags: Vec<String>,
    },

    /// List available targets
    ListTargets,

    /// Build project using build.fcy
    Build {
        #[arg(short, long, help = "Flags that will be passed into build (optional)",
            num_args=1..)]
        args: Vec<String>,
    },
}

#[derive(Args, Debug, Default, Clone)]
pub struct InputFlags {
    #[arg(short, long, help = "Currently unused")]
    pub verbose: bool,

    // a bit less type checks
    #[arg(long = "fpermissive", help = "Disables some type checks. Not much")]
    pub permissive: bool,

    // Runs in check-only mode 
    // (so binaries wouldnt be generated)
    #[arg(long = "check", help = "Only check source code for errors \
        (no binaries would be generated)")]
    pub check: bool,

    #[arg(short, long, default_value_t = Target::get_def(), help = "Target ABI \
        (see `fencyc list-targets`)")]
    pub target: Target, 

    #[arg(long, default_value_t = def_ldas(), help = "Default assembler + \
        linker executable (gcc/clang by default)")]
    pub ldas: String, // specify ldas (linker+assembler)

    #[arg(long, help = "Do not link fency std and runtime libs")]
    pub nostd: bool, // compile w/o fency runtime lib and fency std 

    #[arg(long, help = "Generate only object files")]
    pub onlyobjs: bool, // generate only obj files
                        
    #[arg(long, help = "Compile as shared library")]
    pub shared: bool, // compile as shared library
}

pub fn def_ldas() -> String {
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

#[derive(Clone, ValueEnum, Copy, Debug, Default, EnumIter, PartialEq, Eq, Hash)]
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
