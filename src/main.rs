use std::{collections::{HashMap, HashSet}, path::{Path, PathBuf}, process::{Command, exit}, sync::mpsc::{self, Sender}, time::Instant};

use clap::{FromArgMatches, Parser};
use colored::Colorize;
use indexmap::IndexSet;

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
mod logger {pub mod logger;}
mod tests;
mod cli;
use crate::{cli::{Commands, InputFlags, Target, def_ldas}, codegen::codegen as cgen, fcparse::fcparse::{self as fparser, AstRoot, FcParser, FuncTable, TraitTable}, lexer::lexer as lex, logger::logger::{LogMessage, LoggerQuery, spawn_logger_thread}, seman::seman::{self as Seman, StructTable}};

// prepend home here 
const FENCY_DIR: &str = ".fency";

fn main() {
    let fency_root = get_homedpath(FENCY_DIR);
    let fail_fcypath = fency_root.is_err();
    
    let mut runtime_dir = PathBuf::new();
    let mut libs_dir = PathBuf::new();

    if let Ok(r) = fency_root {
        runtime_dir = r.join("runtime");
        libs_dir = r.join("libs");

        if !runtime_dir.exists() {
            std::fs::create_dir_all(&libs_dir)
                .expect("Failed to create libs directory");
            std::fs::create_dir_all(&runtime_dir)
                .expect("Failed to create runtime directory");
    }
    } else {
        println!("Can't get HOME path. Some functions may be unavailable");
    }

    let cli = cli::CliArgs::parse();
    let paths = vec![runtime_dir, libs_dir];
    
    match cli.command {
        Some(Commands::Input { files, output, flags, mut ldflags } ) => {
            if !(flags.nostd || fail_fcypath) {
                ldflags.push("lfcyrt".to_owned());
            } 

            match compile(files, output, flags, ldflags, paths) {
                Ok(_) => {return;}
                Err(_) => {exit(1);}
            }
        }
        Some(Commands::ListTargets) => {
            Target::list(); 
        }
        Some(Commands::Build { args }) => {
            let build_scr_spath = "build.fcy".to_owned();
            let build_scr_path = Path::new(&build_scr_spath);
            if !build_scr_path.exists() {
                println!("{}: build script file doesn't exist\n\
                {}: `fencyc build` is intended to be used with build.fcy script",
                "ERROR".red(), "help".blue());
                exit(1);
            }

            let build_o_name = "builder".to_owned();
            let mut iflags = InputFlags::default();
            iflags.ldas = def_ldas();
            iflags.target = Target::get_def();

            match compile(
                vec![build_scr_spath], Some(build_o_name.clone()), 
                iflags,
                vec![], paths
            ) {
                Ok(_) => {},
                Err(_) => {exit(1);}
            }

            let args_slice: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
            #[cfg(not(target_os = "windows"))] let build_run_name = 
                format!("./{}", build_o_name);
           
            #[cfg(target_os = "windows")] let build_run_name = 
                format!("{}", build_o_name);

            // TODO: check for errs and do corresp exit code
            match run_command(&build_run_name, &args_slice) {
                Ok(vs) => {
                    for v in vs {
                        println!("{}", v);
                    }
                }
                Err(_) => {
                    println!("Build error occured!");
                    exit(1);
                }
            }
        }
        None => {
            eprintln!("Please, specify command or try fencyc --help.");
        }
    }
}

// 1st path is runtime dir, 2nd path is libs dir
fn compile(files: Vec<String>, output: Option<String>, flags: InputFlags,
    ldflags: Vec<String>, paths: Vec<PathBuf>) -> Result<(), CompilationError> {
    // TODO: this function has a lot of clones. maybe move to refs instead.
    let (log_tx, log_rx) = mpsc::channel::<LogMessage>();
    let (log_resp, resp_get) = mpsc::channel::<LogMessage>();
    let handle = spawn_logger_thread(log_rx, log_resp);

    let mut asts      = Vec::new();
    let mut func_tabs = Vec::new();
    let mut struct_tabs = Vec::new();
    let mut trait_tabs = Vec::new();
    let mut genfunc_tabs = Vec::new();
    
    for file in files.iter() {
        let (ast, func_tab, p) = build_ast(
            file, 
            log_tx.clone()
        );

        asts.push(ast);
        func_tabs.push(func_tab);
        struct_tabs.push(p.structs);
        trait_tabs.push(p.traits);
        genfunc_tabs.push(p.generic_funcs);
    }

    let out = match output {
        Some(s) => s,
        None => String::from("program")
    };

    let functab    = FuncTable::from_several(func_tabs);
    let struct_tab = StructTable::from_several(&struct_tabs);
    let trait_tab  = TraitTable::from_several(trait_tabs); 
    let genfunc_tab: HashMap<String, AstRoot> = genfunc_tabs
        .into_iter()
        .flat_map(|g| {g.into_iter()})
        .collect();

    let mut nat_fnames = Vec::new();
    let fin_msg = LogMessage::from_query(LoggerQuery::Stop);
    let int_msg = LogMessage::from_query(LoggerQuery::Status);

    // hashset of which generics funcs were already generated 
    let mut generated_gens: IndexSet<String> = IndexSet::new(); 

    // TODO: extract this into a function
    for (idx, ast) in asts.drain(..).enumerate() {
        let fname = files[idx].clone(); // todo: map asts with filenames instead

        let mut seman = Seman::SemAn::new(
            flags.permissive, 
            functab.clone(), 
            fname.clone(),
            struct_tab.clone(),
            flags.target,
            trait_tab.clone(),
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
                        _other => unreachable!()
                    }
                    None => unreachable!()
                }
            }
            Err(_e) => {
            }
        }

        if flags.check {
            continue;
        }

        let matched_overloads = seman.matched_overloads.clone();

        let old_gg_size = generated_gens.len();
        
        let mut gene = cgen::CodeGen::new(ast, matched_overloads, 
            idx == 0, functab.clone(), struct_tab.clone(), flags.target,
            genfunc_tab.clone(), generated_gens.clone());
        gene.gen_everything(flags.shared);
        
        if gene.prev_gen.len() > old_gg_size {
            let n = gene.prev_gen.len() - old_gg_size;
            generated_gens.extend(
                gene.prev_gen
                    .iter()
                    .rev()
                    .take(n)
                    .cloned()
            );
        }

        if cfg!(debug_assertions) { 
            println!("{}", gene.module);
        }

        let temp_fname = format!("{}_temp.ssa", fname.replace(".fcy", ""));

        if let Err(e) = gene.write_file(&temp_fname) {
            panic!("Error writing temp into file: {}", e.to_string());
        }; 

        let nname = match genasm(&temp_fname, flags.target) {
            CompilationError::OkFile(f) => {f},
            _other => {
                //logger.extrn_err = other; TODO: send 
                String::from("")
            }
        };
        nat_fnames.push(nname);
    }

    if !flags.check {
        let strs = nat_fnames.iter()
            .map(String::as_str)
            .collect();
        link(&strs, &out, &ldflags, &flags, &paths)?;
    }

    log_tx.send(fin_msg);

    handle.join().unwrap();
    Ok(())
}

fn build_ast(input: &str, _log_tx: Sender<LogMessage>)
    -> (Vec<AstRoot>, FuncTable, FcParser) {
    let toks = lex::tokenize(&input);

    let mut parser = fparser::FcParser::new(toks);
    let parsing_res = parser.parse_everything();
    let ast = parsing_res.0;
    let func_tab = parsing_res.1;
    
    (ast, func_tab, parser)
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

fn genasm(input_name: &str, t: Target)
        -> CompilationError {
    let nat_fname = input_name.replace(".ssa", ".s");
    
    let out1 = match run_command("qbe", &["-t", &t.into_qbe_name(),
    "-o", &nat_fname, input_name]) {
        Ok(sv) => sv,
        Err(()) => {
            return CompilationError::QBEError();
        }
    };
    print_stds(out1);
 
    release_cleanup(&vec![input_name]);

    CompilationError::OkFile(nat_fname.clone())
}

fn link(asm_fnames: &Vec<&str>, output_name: &str, ldflags: &Vec<String>, 
    flags: &InputFlags, fcy_paths: &Vec<PathBuf>)
    -> Result<(), CompilationError> {
    let mut args: Vec<&str> = Vec::new();
    args.extend(asm_fnames);
    
    if !flags.onlyobjs {
        if flags.shared {
            args.push("-fPIC");
            args.push("-shared");
        }

        args.push("-o");
        args.push(output_name);
    } else {
        args.push("-c");
    }

    let mut s_v: Vec<String> = Vec::new();

    for v in fcy_paths {
        let new_arg = format!("-L{}", v.display());
        s_v.push(new_arg);
    }

    args.extend(s_v.iter().map(|s| {s.as_str()}));

    let dash_flags: Vec<String> = ldflags.iter().map(|s| format!("-{}", s))
        .collect();
    args.extend(dash_flags.iter().map(|s| s.as_str())); 

    let out2 = match run_command(&flags.ldas, &args) {
        Ok(sv) => sv,
        Err(()) => {
            return Err(CompilationError::LinkError());
        }
    };
    print_stds(out2);
    release_cleanup(asm_fnames);

    Ok(())
}

fn release_cleanup(files: &Vec<&str>) {
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

pub fn get_homedpath(append: &str) -> Result<PathBuf, ()> {
    if let Some(path) = std::env::home_dir() {
        let res = path.join(PathBuf::from(append));
        
        Ok(res)
    } else {
        Err(())
    }
}

