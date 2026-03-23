use std::{collections::{HashMap, HashSet}, path::{Path, PathBuf}, process::{Command, exit}, sync::{Arc, Mutex, RwLock, atomic::{AtomicUsize, Ordering}, mpsc::{self, Sender}}, time::Instant};

use clap::{FromArgMatches, Parser};
use colored::Colorize;
use indexmap::IndexSet;
use rayon::prelude::*;

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
mod logger {pub mod logger;}
mod tests;
mod cli;
use crate::{cli::{Commands, InputFlags, Target, def_ldas}, codegen::codegen as cgen, fcparse::fcparse::{self as fparser, AstRoot, FcParser, FuncTable, TraitTable}, lexer::lexer as lex, logger::logger::{LogMessage, LoggerQuery, spawn_logger_thread}, seman::seman::{self as Seman, OverloadTable, SemanResult, StructTable}};

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
        Some(Commands::Input { files, output, mut flags, mut ldflags, extfiles } ) => {
            if !(flags.nostd || fail_fcypath) {
                ldflags.push("lfcyrt".to_owned());
            }
            flags.verbose |= cli.verbose;

            match compile(files, output, flags, ldflags, paths, extfiles) {
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
            iflags.verbose = cli.verbose;

            match compile(
                vec![build_scr_spath], Some(build_o_name.clone()), 
                iflags,
                vec![], paths, vec![]
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
    ldflags: Vec<String>, paths: Vec<PathBuf>, extfiles: Vec<String>)
    -> Result<(), CompilationError> {
    let (log_tx, log_rx) = mpsc::channel::<LogMessage>();
    let (log_resp, resp_get) = mpsc::channel::<LogMessage>();
    let handle = spawn_logger_thread(log_rx, log_resp);

    let out = match output {
        Some(s) => s,
        None => String::from("program")
    };

    let ast_results: Vec<_> = files.par_iter()
        .map(|file| {
            let (ast, func_tab, p) = build_ast(file, log_tx.clone());
            (Arc::new(ast), func_tab, p)
        })
        .collect();

    let mut asts = Vec::with_capacity(ast_results.len());
    let mut func_tabs = Vec::with_capacity(ast_results.len());
    let mut struct_tabs = Vec::with_capacity(ast_results.len());
    let mut trait_tabs  = Vec::with_capacity(ast_results.len());
    let mut genfunc_tabs = Vec::with_capacity(ast_results.len());

    for (ast, func_tab, p) in ast_results {
        asts.push(ast);
        func_tabs.push(func_tab);
        struct_tabs.push(p.structs);
        trait_tabs.push(p.traits);
        genfunc_tabs.push(p.generic_funcs);
    }   

    let functab    = Arc::new(FuncTable::from_several(func_tabs));
    let struct_tab = Arc::new(StructTable::from_several(&struct_tabs));
    let trait_tab  = Arc::new(TraitTable::from_several(trait_tabs)); 
    let genfunc_tab: Arc<HashMap<String, AstRoot>> = Arc::new(genfunc_tabs
        .into_iter()
        .flat_map(|g| {g.into_iter()})
        .collect());

    let fin_msg = LogMessage::from_query(LoggerQuery::Stop);
    let int_msg = LogMessage::from_query(LoggerQuery::Status);

    let total_files = asts.len();
    let seman_counter = Arc::new(AtomicUsize::new(0));
    let matched_ovs: HashMap<usize, OverloadTable> = asts.par_iter()
        .enumerate()
        .map(|(idx, ast)| {
        
        let fname = files[idx].clone();
        let progress = seman_counter.fetch_add(1, Ordering::SeqCst);
        if flags.verbose {
            println!("[{}/{}] {} {}", progress + 1, total_files, 
                "Analyzing".bright_blue(), fname)
        }

        let mut seman = Seman::SemAn::new(
            flags.permissive,
            functab.clone(),
            fname.clone(),
            struct_tab.clone(),
            flags.target,
            trait_tab.clone(),
        );
        seman.analyze(ast.clone(), &log_tx); 
        (idx, seman.matched_overloads.clone())
    }).collect();

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
        Err(_e) => {}
    }

    let global_gens = Arc::new(RwLock::new(IndexSet::new()));
    
    let counter = Arc::new(AtomicUsize::new(0));
    let nat_fnames: Vec<String> = asts.par_iter().enumerate().map(|(idx, ast)| {
        let fname = files[idx].clone();

        let progress = counter.fetch_add(1, Ordering::SeqCst); // atomic increment
        
        if flags.verbose {
            println!("[{}/{}] {} {}", progress + 1, total_files, 
                "Generating".blue() , fname);
        }

        let gens = global_gens.clone();

        let mut gene = cgen::CodeGen::new(
            ast.clone(),
            matched_ovs.get(&idx).unwrap().clone(),
            idx == 0,
            functab.clone(),
            struct_tab.clone(),
            flags.target,
            genfunc_tab.clone(),
            gens, 
        );

        gene.gen_everything(flags.shared);

        let temp_fname = format!("{}_temp.ssa", fname.replace(".fcy", ""));
        gene.write_file(&temp_fname).unwrap();

        match genasm(&temp_fname, flags.target) {
            CompilationError::OkFile(f) => f,
            _ => String::new(),
        }
    }).collect();

    if !flags.check {
        let strs = nat_fnames.iter()
            .map(String::as_str)
            .collect();
        ldas(&strs, &out, &ldflags, &flags, &paths, &extfiles)?;
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
    AsmFault,
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

fn ldas(asm_fnames: &Vec<&str>, output_name: &str, ldflags: &Vec<String>, 
    flags: &InputFlags, fcy_paths: &Vec<PathBuf>, extfiles: &Vec<String>)
    -> Result<(), CompilationError> {

    let mut obj_files = Arc::new(Mutex::new(Vec::new()));
    let mut input_files = asm_fnames.clone();
    input_files.extend(extfiles.iter().map(|s| {s.as_str()}));

    let counter = Arc::new(AtomicUsize::new(0));
    let total = input_files.len();
    
    let errs_count: usize = input_files.par_iter()
        .enumerate()
        .map(|(i, v)| {
        
        let obj_filename = format!("{}.o", v);
        {
            let mut vec = obj_files.lock().unwrap();
            vec.push(obj_filename.clone());
        }

        let progress = counter.fetch_add(1, Ordering::SeqCst); // atomic increment
        if flags.verbose {
            println!("[{}/{}] {} object file {}",
                progress + 1, total, "Assembling".cyan(), obj_filename);
        }

        let args = match flags.shared {
            true  => vec!["-c", "-fPIC", &v, "-o", &obj_filename],
            false => vec!["-c", &v, "-o", &obj_filename],
        };
        match run_command(&flags.ldas, &args) {
            Ok(vs) => {
                for s in vs {
                    if !s.is_empty() {
                        println!("asm: {}", s);
                    }
                }
            },
            Err(_) => {
                return 1;
            }
        }
        0
    }).sum();
    if errs_count > 0 {
        return Err(CompilationError::AsmFault);
    }

    let mut fin_args: Vec<String> = Vec::new();
    let shared_flag = String::from("-shared");
    if flags.shared {
        fin_args.push(shared_flag);
    }
    {
        let vec = obj_files.lock().unwrap();
        fin_args.extend(vec.iter().cloned());
    }
    fin_args.push("-o".to_owned());
    fin_args.push(output_name.to_owned());
    fin_args.extend(fcy_paths.iter().map(|p| {
        format!("-L{}", p.display())
    }));
    fin_args.extend(ldflags.iter().map(|s| {
        format!("-{}", s)
    }));

    if flags.verbose {
        println!("{} program {}...", "Linking".bright_green(), output_name);
    }
    let args_strs: Vec<&str> = fin_args.iter().map(|s| {s.as_str()})
        .collect();
    match run_command(&flags.ldas, &args_strs) {
        Ok(vs) => {
            print_stds(vs); 
        }
        Err(_) => {
            return Err(CompilationError::LinkError())
        }
    }

    release_cleanup(asm_fnames);
    {
        let vec = obj_files.lock().unwrap();
        let obj_files_refs = vec.iter().map(|s| {s.as_str()}).collect();
        cleanup(&obj_files_refs);
    }

    Ok(())
}

fn release_cleanup(files: &Vec<&str>) {
    if !cfg!(debug_assertions) {
        cleanup(files); 
    }
}

fn cleanup(files: &Vec<&str>) {
    for file in files {
        if let Err(e) = std::fs::remove_file(file) {
            eprintln!("Failed to delete temp asm file {}: {}", file, e);
        };
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

