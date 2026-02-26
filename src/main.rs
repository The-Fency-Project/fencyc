#[cfg(not(debug_assertions))]
use std::fs;
use std::{fs::File, io::BufReader, process::{Command, exit}, sync::mpsc::{self, Sender}, time::Instant};

use clap::{Parser, Subcommand, Args};

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
mod logger {pub mod logger;}
mod tests;
use crate::{codegen::codegen as cgen, fcparse::fcparse::{self as fparser, AstNode, AstRoot, FuncTable}, lexer::lexer as lex, logger::logger::{self as log, LogMessage, Logger, LoggerQuery, spawn_logger_thread}, seman::seman as Seman, seman::seman as sem};

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
        files: Vec<String>,

        #[arg(short, long)]
        output: Option<String>,

        #[command(flatten)]
        flags: InputFlags,

        #[arg(long = "ldflags")]
        ldflags: Vec<String>,
    },
}

#[derive(Args, Debug, Default, Clone, Copy)]
struct InputFlags {
    #[arg(short, long)]
    verbose: bool,

    #[arg(long = "fpermissive")]
    permissive: bool,
}

fn main() {
    let cli = CliArgs::parse();
    
    match cli.command {
        Some(Commands::Input { files, output, flags, ldflags } ) => {
            match compile(files, output, flags, ldflags) {
                Ok(_) => {return;}
                Err(_) => {exit(1);}
            }
        }
        None => {
            eprintln!("Please, specify command or try fencyc --help.");
        }
    }
}

fn compile(files: Vec<String>, output: Option<String>, flags: InputFlags,
    ldflags: Vec<String>) -> Result<(), CompilationError> {
    let (log_tx, log_rx) = mpsc::channel::<LogMessage>();
    let (log_resp, resp_get) = mpsc::channel::<LogMessage>();
    let handle = spawn_logger_thread(log_rx, log_resp);


    let mut asts      = Vec::new();
    let mut func_tabs = Vec::new();

    for file in files.iter() {
        let (ast, func_tab) = build_ast(
            file, 
            log_tx.clone()
        );

        asts.push(ast);
        func_tabs.push(func_tab);
    }

    let out = match output {
        Some(s) => s,
        None => String::from("program")
    };

    let functab = FuncTable::from_several(&mut func_tabs);
    let mut nat_fnames = Vec::new();
    let mut fin_msg = LogMessage::from_query(LoggerQuery::Stop);
    let int_msg = LogMessage::from_query(LoggerQuery::Status);

    // TODO: extract these into a function
    for (idx, ast) in asts.drain(..).enumerate() {
        let fname = files[idx].clone(); // todo: map asts with filenames instead

        let mut seman = Seman::SemAn::new(
            flags.permissive, functab.clone(), fname.clone()
        );
        seman.analyze(&ast, &log_tx);

        log_tx.send(int_msg.clone());

        match resp_get.recv() {
            Ok(m) => {
                match m.query {
                    Some(v) => match v {
                        LoggerQuery::StatusResp(b) => {
                            if b {
                                log_tx.send(fin_msg);
                                handle.join().unwrap();
                                return Err(CompilationError::Compilation);
                            }
                        }
                        other => unreachable!()
                    }
                    None => unreachable!()
                }
            }
            Err(e) => {
            }
        }
        let matched_overloads = seman.matched_overloads.clone();

        let mut gene = cgen::CodeGen::new(ast, matched_overloads, 
            idx == 0, functab.clone());
        gene.gen_everything();
        if cfg!(debug_assertions) { 
            println!("{}", gene.module);
        }

        let temp_fname = format!("{}_temp.ssa", fname.replace(".fcy", ""));

        if let Err(e) = gene.write_file(&temp_fname) {
            panic!("Error writing temp into file: {}", e.to_string());
        }; 

        let nname = match assemble(&temp_fname) {
            CompilationError::OkFile(f) => {f},
            other => {
                //logger.extrn_err = other; TODO: send 
                String::from("")
            }
        };
        nat_fnames.push(nname);
    }

    let strs = nat_fnames.iter()
        .map(String::as_str)
        .collect();
    link(&strs, &out, &ldflags)?;

    log_tx.send(fin_msg);

    handle.join().unwrap();
    Ok(())
}

fn build_ast(input: &str, log_tx: Sender<LogMessage>)
    -> (Vec<AstRoot>, FuncTable) {
    let toks = lex::tokenize(&input);

    let mut parser = fparser::FcParser::new(toks);
    let parsing_res = parser.parse_everything();
    let ast = parsing_res.0;
    let func_tab = parsing_res.1;
    
    (ast, func_tab)
}

#[derive(Debug)]
enum CompilationError {
    Ok, // fname
    OkFile(String),
    QBEError(),
    LinkError(),
    Compilation,
    Unknown,
}

fn assemble(input_name: &str)
        -> CompilationError {
    let nat_fname = input_name.replace(".ssa", ".s");
    
    let out1 = match run_command("qbe", &["-o", &nat_fname, input_name]) {
        Ok(sv) => sv,
        Err(()) => {
            return CompilationError::QBEError();
        }
    };
    print_stds(out1);
 
    
    release_cleanup(vec![input_name]);

    CompilationError::OkFile(nat_fname.clone())
}

fn link(nat_fnames: &Vec<&str>, output_name: &str, ldflags: &Vec<String>)
    -> Result<(), CompilationError> {
    let mut args: Vec<&str> = Vec::new();
    args.extend(nat_fnames);
    args.push("-o");
    args.push(output_name);

    let dash_flags: Vec<String> = ldflags.iter().map(|s| format!("-{}", s))
        .collect();
    args.extend(dash_flags.iter().map(|s| s.as_str()));  

    let out2 = match run_command("gcc", &args) {
        Ok(sv) => sv,
        Err(()) => {
            return Err(CompilationError::LinkError());
        }
    };
    print_stds(out2);


    Ok(())
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
