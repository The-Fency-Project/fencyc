#[cfg(not(debug_assertions))]
use std::fs;
use std::{fs::File, io::BufReader, process::Command};

use clap::{Parser, Subcommand};

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
use crate::{codegen::codegen as cgen, fcparse::fcparse::{self as fparser, AstNode}, lexer::lexer as lex, seman::seman as sem};

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

    let toks = lex::tokenize(&input.clone());
    //println!("toks {:#?}", toks);

    let mut parser = fparser::FcParser::new(toks);
    
    let ast: Vec<AstNode> = parser.parse_everything();
    
    let mut gene = cgen::CodeGen::new(ast);
    gene.gen_everything();

    let temp_fname = format!("{}_temp.vvs", input.replace(".fcy", ""));

    if let Err(e) = gene.write_file(&temp_fname) {
        panic!("Error writing temp into file: {}", e.to_string());
    }; 

    assemble(&temp_fname, &output_name);

    #[cfg(not(debug_assertions))] // deleting temp asm file 
                                // if fencyc build is release
    if let Err(e) = std::fs::remove_file(&temp_fname) {
        eprintln!("Failed to delete temp asm file {}", temp_fname);
    };

    Ok(())
}

fn assemble(input_name: &str, output_name: &str) {
    let com = format!("voxvm --vas={} --vas-out={}", input_name, output_name);

    let output = if cfg!(target_os = "windows") {
        Command::new("cmd")
            .args(["/C", &com])
            .output()
            .expect("failed to execute voxasm process")
    } else {
        Command::new("sh")
            .arg("-c")
            .arg(&com)
            .output()
            .expect("failed to execute voxasm process")
    };

    let out = output.stdout;
    println!("{}", String::from_utf8_lossy(&out));
}
