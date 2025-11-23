use std::{fs::File, io::BufReader};

use clap::{Parser, Subcommand};

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
use crate::{fcparse::fcparse as fparser, lexer::lexer as lex};

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct CliArgs {
    #[arg(short, long)]
    verbose: bool,

    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    Input {
        file: String,

        #[arg(short, long)]
        output: Option<String>,
    },
}

fn main() {
    let cli = CliArgs::parse();
    
    match cli.command {
        Some(Commands::Input { file, output } ) => {
            start_compiling(file, output, cli.verbose);
            return;
        }
        None => {
            eprintln!("Please, specify command or try fencyc --help.");
        }
    }
}

fn start_compiling(input: String, output: Option<String>, verbose: bool) -> Result<(), ()> {
    let output_name = match output {
        Some(v) => v,
        None => input.replace(".fcy", ".vve"),
    };

    let toks = lex::tokenize(&input); 

    let mut parser = fparser::FcParser::new(toks);
    let ast_node = parser.parse_expr(0);

    Ok(())
}
