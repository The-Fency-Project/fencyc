#[cfg(not(debug_assertions))]
use std::fs;
use std::{fs::File, io::BufReader, process::{exit, Command}, time::Instant};

use clap::{Parser, Subcommand};

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
mod logger {pub mod logger;}
use crate::{codegen::codegen as cgen, fcparse::fcparse::{self as fparser, AstNode, AstRoot}, lexer::lexer as lex, logger::logger::{self as log, Logger}, seman::seman as Seman, seman::seman as sem};

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

        #[arg(long = "fpermissive")]
        fpermissive: bool,
    },
}

fn main() {
    let cli = CliArgs::parse();
    
    match cli.command {
        Some(Commands::Input { file, output, fpermissive } ) => {
            start_compiling(file, output, cli.verbose, fpermissive);
            return;
        }
        None => {
            eprintln!("Please, specify command or try fencyc --help.");
        }
    }
}

fn start_compiling(input: String, output: Option<String>, verbose: bool, fpermissive: bool) -> Result<(), ()> {
    let output_name = match output {
        Some(v) => v,
        None => {
            if cfg!(target_os = "windows") {
                input.replace(".fcy", ".exe")
            } else {
                input.replace(".fcy", "")
            }
        },
    };

    let mut logger: log::Logger = Logger::new();
    logger.start_timer();

    let toks = lex::tokenize(&input.clone());

    let mut parser = fparser::FcParser::new(toks);
    let parsing_res = parser.parse_everything();
    let ast = parsing_res.0;
    let func_tab = parsing_res.1;

    let mut seman = Seman::SemAn::new(fpermissive, func_tab);
    seman.analyze(&ast, &mut logger);
    let matched_overloads = seman.matched_overloads.clone();

    if logger.should_interrupt() {
        logger.finalize();
        exit(1);
    }

    let mut gene = cgen::CodeGen::new(ast, matched_overloads);
    gene.gen_everything();
    #[cfg(debug_assertions)] { 
        println!("{}", gene.module);
    }

    let temp_fname = format!("{}_temp.ssa", input.replace(".fcy", ""));

    if let Err(e) = gene.write_file(&temp_fname) {
        panic!("Error writing temp into file: {}", e.to_string());
    }; 

    match assemble(&temp_fname, &output_name) {
        ExternalResult::Ok => {},
        other => {
            logger.extrn_err = other;
        }
    };

    let ret = logger.finalize();
    ret
}

#[derive(Debug)]
enum ExternalResult {
    Ok,
    QBEError(),
    LinkError(),
}

fn assemble(input_name: &str, output_name: &str) -> ExternalResult {
    let nat_fname = input_name.replace(".ssa", ".s");
    
    let out1 = match run_command("qbe", &["-o", &nat_fname, input_name]) {
        Ok(sv) => sv,
        Err(()) => {
            return ExternalResult::QBEError();
        }
    };
    print_stds(out1);
 
    let out2 = match run_command("gcc", &[&nat_fname, "-o", output_name]) {
        Ok(sv) => sv,
        Err(()) => {
            return ExternalResult::LinkError();
        }
    };
    print_stds(out2);

    release_cleanup(vec![input_name, &nat_fname]);

    ExternalResult::Ok
}

fn release_cleanup(files: Vec<&str>) {
    if !cfg!(debug_assertions) {
        for file in files {
            if let Err(e) = std::fs::remove_file(file) {
                eprintln!("Failed to delete temp asm file {}: {}", file, e);
            };
        }
    }
}

/// Prints strings if they're not empty, 
/// assuming [0] is stdout and [1] is stderr
fn print_stds(ss: Vec<String>) {
    if !ss[0].is_empty() {
        println!("Stdout: {}", ss[0]);
    }
    if !ss[1].is_empty() {
        println!("Stdout: {}", ss[1]);
    }
}

#[cfg(target_os = "windows")]
fn run_command(cmd: &str, args: &[&str]) -> Result<Vec<String>, ()> {
    let output = Command::new("cmd")
        .args(["/C", cmd])
        .args(args)
        .output()
        .expect(&format!("Failed to run {}", cmd));
   
    if !output.status.success() {
        eprintln!("Error: Command '{}' failed with {}", cmd, output.status);
        eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        return Err(()); 
    }

    let mut res = Vec::new();
    res.push(String::from_utf8_lossy(&output.stdout).to_string());
    res.push(String::from_utf8_lossy(&output.stderr).to_string());
    Ok(res)
}

#[cfg(not(target_os = "windows"))]
fn run_command(cmd: &str, args: &[&str]) -> Result<Vec<String>, ()> {
    let output = Command::new(cmd)
        .args(args)
        .output()
        .expect(&format!("Failed to run {}", cmd));

    if !output.status.success() {
        eprintln!("Error: Command '{}' failed with {}", cmd, output.status);
        eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        return Err(()); 
    }
    
    let mut res = Vec::new();
    res.push(String::from_utf8_lossy(&output.stdout).to_string());
    res.push(String::from_utf8_lossy(&output.stderr).to_string());

    Ok(res)
}
