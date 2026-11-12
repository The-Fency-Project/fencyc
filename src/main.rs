use std::{collections::{HashMap, HashSet}, path::{Path, PathBuf}, process::{Command, exit}, sync::{Arc, Mutex, RwLock, atomic::{AtomicUsize, Ordering}, mpsc::{self, Sender}}, time::Instant};

use clap::{FromArgMatches, Parser};
use colored::Colorize;
use indexmap::IndexSet;
use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target as LTarget, TargetMachine, TargetTriple};
use rayon::prelude::*;

mod fcparse {pub mod fcparse;}
mod codegen {pub mod codegen; pub mod mirtoqbe; pub mod mirtollvm;}
mod lexer {pub mod lexer;}
mod seman {pub mod seman;}
mod logger {pub mod logger;}
mod mir {pub mod mir;}
mod tests;
mod cli;
mod artifact;
#[cfg(test)]
mod artifact_tests;
use crate::{cli::{Commands, CompBackend, InputFlags, Target, def_ldas}, codegen::{codegen::{self as cgen, CodeGen}, mirtollvm::LLVMBackend, mirtoqbe::QBEBackend}, fcparse::fcparse::{self as fparser, AstRoot, FcParser, FuncTable, TraitTable}, lexer::lexer as lex, logger::logger::{LogMessage, LoggerQuery, spawn_logger_thread}, mir::mir::{self as fmir, FFunction, FModule, MIRTranslator}, seman::seman::{self as Seman, OverloadTable, SemanResult, StructTable}};

// prepend home here 
const FENCY_DIR: &str = ".fency";

fn main() {
    let fency_root = installation_root();
    let cli = cli::CliArgs::parse();
    let mut paths = fency_root.as_ref()
        .map(|root| vec![root.join("runtime"), root.join("libs")])
        .unwrap_or_default();
    
    match cli.command {
        Some(Commands::Input { files, output, mut flags, mut ldflags, extfiles } ) => {
            flags.verbose |= cli.verbose;
            let mut flags = flags.finalize();
            let installation = if !flags.nostd {
                Some(match discover_installation(flags.target, flags.backend.unwrap()) {
                    Ok(installation) => installation,
                    Err(message) => {
                        eprintln!("{message}");
                        exit(1);
                    }
                })
            } else { None };
            if let Some(installation) = installation {
                flags.dependencies.push(installation.std_metadata);
                paths.extend(installation.search_paths);
                if !flags.library && !flags.check && !flags.onlyobjs {
                    ldflags.push(installation.runtime_link_flag);
                }
            }

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
            // Build scripts are the bootstrap path for stdlib and native setup.
            // They declare their own externs and are compiled without the installed std.
            iflags.nostd = true;

            match compile(
                vec![build_scr_spath], Some(build_o_name.clone()), 
                iflags.finalize(),
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
    let recipe = artifact::Recipe::new(files, output, flags, ldflags, paths, extfiles)
        .map_err(|message| { eprintln!("{message}"); CompilationError::Compilation })?;
    artifact::run(recipe).map_err(|message| { eprintln!("{message}"); CompilationError::Compilation })
}

fn compile_unit(recipe: &artifact::Recipe, imports: &[artifact::Metadata], staging: &Path)
    -> Result<artifact::Product, CompilationError> {
    let files = &recipe.files;
    let flags = &recipe.flags;
    let (log_tx, log_rx) = mpsc::channel::<LogMessage>();
    let (log_resp, resp_get) = mpsc::channel::<LogMessage>();
    let handle = spawn_logger_thread(log_rx, log_resp);

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
    let mut genstruct_uses = Vec::new();
    let mut genimpl_tabs = Vec::with_capacity(ast_results.len());

    for (ast, func_tab, p) in ast_results {
        asts.push(ast);
        func_tabs.push(func_tab);
        struct_tabs.push(p.structs);
        trait_tabs.push(p.traits);
        genfunc_tabs.push(p.generic_funcs);
        genstruct_uses.extend(p.generic_structs);
        genimpl_tabs.push(p.generic_impls);
    }   

    let own = artifact::Interface {
        functions: FuncTable::from_several(func_tabs),
        structs: StructTable::from_several(&struct_tabs),
        traits: TraitTable::from_several(trait_tabs),
        generic_functions: genfunc_tabs.into_iter().flat_map(|g| g.into_iter()).collect(),
        generic_impls: genimpl_tabs.into_iter().flat_map(|g| g.into_iter()).collect(),
        generic_uses: genstruct_uses,
    };
    let merged = artifact::merge(&own, imports).map_err(|message| {
        eprintln!("{message}"); CompilationError::Compilation
    })?;
    let functab = Arc::new(merged.functions);
    let mut struct_tab = merged.structs;
    struct_tab.instantiate_many(&merged.generic_uses);
    struct_tab.recalc_layouts().map_err(|message| {
        eprintln!("{message}"); CompilationError::LayoutErr(message)
    })?;
    let struct_tab = Arc::new(struct_tab);
    let trait_tab = Arc::new(merged.traits);
    let genfunc_tab = Arc::new(merged.generic_functions);
    let genimpl_tab = Arc::new(merged.generic_impls);

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

    if flags.check {
        log_tx.send(fin_msg).ok();
        handle.join().unwrap();
        return Ok(artifact::Product { interface: own, objects: vec![], specializations: vec![] });
    }

    let mut known_generics = IndexSet::new();
    for import in imports { known_generics.extend(import.specializations.iter().cloned()); }
    let initial_generics = known_generics.clone();
    let global_gens = Arc::new(RwLock::new(known_generics));
    let flags_arc   = Arc::new(flags.clone());
    let signatures = Arc::new(Mutex::new(Vec::new()));

    let counter                 = Arc::new(AtomicUsize::new(0));
    let nat_results: Vec<Result<String, CompilationError>> = asts.par_iter().enumerate().map(|(idx, ast)| {
        let fname = files[idx].clone();
        let cflags = flags_arc.clone();

        let progress = counter.fetch_add(1, Ordering::SeqCst); // atomic increment
        
        if cflags.verbose {
            println!("[{}/{}] {} {}", progress + 1, total_files, 
                "Generating".blue() , fname);
        }

        let gens = global_gens.clone();

        let mut gene = cgen::CodeGen::new(
            ast.clone(),
            matched_ovs.get(&idx).unwrap().clone(),
            functab.clone(),
            struct_tab.clone(),
            trait_tab.clone(),
            flags_arc.clone(),
            genfunc_tab.clone(),
            genimpl_tab.clone(),
            gens, 
        );

        gene.gen_everything(cflags.shared || cflags.library || cflags.onlyobjs);

        if !gene.specialization_errors.is_empty() {
            for message in gene.specialization_errors { log_tx.send(message).ok(); }
            return Err(CompilationError::Compilation);
        }
        {
            let defined = gene.module.funcs.iter().filter(|f| !f.blocks.is_empty()).map(|f| &f.name).collect::<HashSet<_>>();
            signatures.lock().unwrap().extend(gene.specialization_signatures.iter().filter(|s| defined.contains(&s.symbol_name(0))).cloned());
        }
        if cfg!(debug_assertions) { println!("DBG module \n{}", gene.module); }

        let temp_fname = staging.join(format!("unit_{idx}.ssa")).to_string_lossy().into_owned();
        match lower_mir(&gene, &cflags, &temp_fname) {
            CompilationError::OkFile(f) => {
                // Separately built consumers can instantiate the same generic. Let the
                // native linker coalesce these definitions while retaining ordinary symbols.
                let defined = gene.module.funcs.iter().filter(|func| !func.blocks.is_empty()).map(|func| &func.name).collect::<HashSet<_>>();
                let weak = gene.specialization_signatures.iter().map(|s| s.symbol_name(0)).filter(|s| defined.contains(s)).collect::<HashSet<_>>();
                if !weak.is_empty() {
                    use std::io::Write;
                    let mut asm = std::fs::OpenOptions::new().append(true).open(&f).map_err(|_| CompilationError::AsmFault)?;
                    for name in weak {
                        let directive = if matches!(cflags.target, Target::Aarch64Apple) { format!("\n.weak_definition _{name}\n") }
                            else { format!("\n.weak {name}\n") };
                        asm.write_all(directive.as_bytes()).map_err(|_| CompilationError::AsmFault)?;
                    }
                }
                Ok(f)
            },
            error => Err(error),
        }

        
    }).collect();

    let nat_fnames = nat_results.into_iter().collect::<Result<Vec<_>, _>>()?;

    let mut objects = Vec::new();
    for (idx, path) in nat_fnames.iter().chain(&recipe.external).enumerate() {
        let suffix = if path.ends_with(".a") { "a" } else { "o" };
        let object = staging.join(format!("object_{idx}.{suffix}"));
        if path.ends_with(".o") || path.ends_with(".a") {
            std::fs::copy(path, &object).map_err(|_| CompilationError::AsmFault)?;
        } else {
            let mut args = vec!["-c".to_owned()];
            if flags.shared { args.push("-fPIC".into()); }
            args.extend([path.clone(), "-o".into(), object.to_string_lossy().into_owned()]);
            run_command(&flags.ldas, &args.iter().map(String::as_str).collect::<Vec<_>>())
                .map_err(|_| CompilationError::AsmFault)?;
        }
        objects.push(object);
    }
    let specializations = global_gens.read().unwrap().iter()
        .filter(|name| !initial_generics.contains(*name)).cloned().collect();
    log_tx.send(fin_msg).ok();
    handle.join().unwrap();
    let mut interface = own;
    for (name, info) in &mut interface.structs.tab {
        if let Some(computed) = struct_tab.tab.get(name) { *info = computed.clone(); }
    }
    for signature in signatures.lock().unwrap().iter() {
        interface.functions.ft.entry(signature.name.path_to_string()).or_insert_with(|| vec![signature.clone()]);
    }
    Ok(artifact::Product { interface, objects, specializations })
}

fn build_ast(input: &str, log_tx: Sender<LogMessage>)
    -> (Vec<AstRoot>, FuncTable, FcParser) {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let toks = lex::tokenize(&input);
        let mut parser = fparser::FcParser::new(toks);
        let parsing_res = parser.parse_everything();
        (parsing_res.0, parsing_res.1, parser)
    }));
    let (ast, func_tab, parser) = match result {
        Ok(value) => value,
        Err(_) => {
            log_tx.send(LogMessage::new(
                logger::logger::LogLevel::Error(logger::logger::ErrKind::Internal(
                    "parser panicked while reading input".into())),
                0, input.to_owned())).ok();
            let parser = fparser::FcParser::new(Vec::new());
            (vec![AstRoot::new(fparser::AstNode::Invalid(
                logger::logger::LogLevel::Error(logger::logger::ErrKind::Internal(
                    "parser panicked while reading input".into()))), 0)],
                FuncTable::new(), parser)
        }
    };
    for root in &ast {
        if let fparser::AstNode::Invalid(level) = &root.node {
            log_tx.send(LogMessage::new(level.clone(), root.line, input.to_owned())).ok();
        }
    }
    
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
    LayoutErr(String),
    Unknown,
}

fn lower_mir(gene: &CodeGen, flags: &InputFlags, temp_fname: &str) 
    -> CompilationError {
    match flags.backend.unwrap() {
        CompBackend::QBE => {
            //gene.write_file(&temp_fname).unwrap();
            let mut qb = QBEBackend::new();
            let qmod = gene.translate(&mut qb);

            if let Some(parent) = std::path::Path::new(temp_fname).parent() {
                match std::fs::create_dir_all(parent) {
                    Ok(_) => {},
                    Err(e) => eprintln!("{}", e),
                }
            }
            match std::fs::write(temp_fname, &format!("{}", qmod)) {
                Ok(_) => {},
                Err(e) => {
                    eprintln!("{}", e);
                }
            };

            genasm_qbe(&temp_fname, flags.target)
        }
        CompBackend::LLVM => {
            let context   = inkwell::context::Context::create();
            let object_fname = temp_fname.replace(".ssa", ".o");
            let mod_name  = temp_fname.split(".").next().unwrap_or(temp_fname);
            let tgt_mchn  = target_machine_from_cli(flags); 
            let mut llvm  = LLVMBackend::new(&context, mod_name, tgt_mchn);

            let _module = gene.translate(&mut llvm);

            let defined = gene.module.funcs.iter().filter(|func| !func.blocks.is_empty()).map(|func| &func.name).collect::<HashSet<_>>();
            let weak = gene.specialization_signatures.iter().map(|s| s.symbol_name(0)).filter(|name| defined.contains(name)).collect::<HashSet<_>>();
            llvm.mark_weak(&weak);

            if let Some(parent) = std::path::Path::new(temp_fname).parent() {
                if let Err(e) = std::fs::create_dir_all(parent) {
                    eprintln!("{e}");
                }
            }


            // llvm.run_mem2reg(); // running in translate() now
            match llvm.emit_object_file(&object_fname) {
                Ok(_) => CompilationError::OkFile(object_fname),
                _ => CompilationError::AsmFault
            }
        }

        other => todo!("{:?}", other)
    }
}

fn genasm_qbe(input_name: &str, t: Target)
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

fn genasm_llvm(input_name: &str, tgt: Target)
    -> CompilationError
{
    let obj_name = input_name.replace(".ssa", ".o");

    // TODO: add target + opt level
    let llc_out = match run_command(
        "llc",
        &[
            "-filetype=obj",
            input_name,
            "-o",
            &obj_name,
        ],
    ) {
        Ok(v) => v,
        Err(_) => return CompilationError::AsmFault,
    };

    print_stds(llc_out);

    release_cleanup(&vec![input_name]);

    CompilationError::OkFile(obj_name)
}

fn link_objects(objects: &[PathBuf], output: &Path, flags: &InputFlags,
    paths: &[PathBuf], ldflags: &[String]) -> Result<(), CompilationError> {
    if let Some(parent) = output.parent() { std::fs::create_dir_all(parent).map_err(|_| CompilationError::LinkError())?; }
    let mut args = Vec::new();
    if flags.shared { args.push("-shared".to_owned()); }
    args.extend(objects.iter().map(|p| p.to_string_lossy().into_owned()));
    let temporary = output.with_file_name(format!("{}.{}.tmp", output.file_name().unwrap().to_string_lossy(), std::process::id()));
    args.extend(["-o".into(), temporary.to_string_lossy().into_owned()]);
    args.extend(paths.iter().map(|p| format!("-L{}", p.display())));
    for flag in ldflags {
        if let Some(argument) = flag.strip_prefix('@') {
            // Internal raw linker argument (used for an absolute runtime path).
            args.push(argument.to_owned());
        } else {
            args.push(format!("-{flag}"));
        }
    }
    if flags.verbose { println!("Linking {}", output.display()); }
    run_command(&flags.ldas, &args.iter().map(String::as_str).collect::<Vec<_>>())
        .map_err(|_| CompilationError::LinkError())?;
    std::fs::rename(temporary, output).map_err(|_| CompilationError::LinkError())?;
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

struct FencyInstallation {
    std_metadata: PathBuf,
    runtime_link_flag: String,
    search_paths: Vec<PathBuf>,
}

/// Locate the installed compiler support files. `FENCY_HOME` is useful for
/// isolated toolchains and tests; the normal installation remains `~/.fency`.
fn installation_root() -> Option<PathBuf> {
    std::env::var_os("FENCY_HOME")
        .map(PathBuf::from)
        .or_else(|| get_homedpath(FENCY_DIR).ok())
}

fn target_runtime_names(target: Target) -> (&'static str, &'static str, &'static [&'static str]) {
    match target {
        Target::Amd64Sysv => ("linux-x86_64", "libfcyrt.a", &["amd64_sysv"]),
        Target::Amd64Win => ("windows-x86_64", "libfcyrt.lib", &["amd64_win"]),
        Target::Aarch64Apple => ("macos-aarch64", "libfcyrt.a", &["aarch64_apple"]),
        Target::Aarch64Sysv => ("linux-aarch64", "libfcyrt.a", &["aarch64_sysv"]),
        Target::Riscv64Sysv => ("linux-riscv64", "libfcyrt.a", &["riscv64_sysv"]),
    }
}

fn discover_installation(target: Target, backend: CompBackend) -> Result<FencyInstallation, String> {
    let root = installation_root().ok_or_else(|| {
        "fency setup not found; compilation is only possible with --nostd".to_owned()
    })?;
    let std_root = root.join("libs").join("std");
    let backend_name = backend.to_string().to_lowercase();
    let std_metadata = [
        std_root.join(format!("std-{backend_name}.fmeta")),
        std_root.join("std.fmeta"),
    ].into_iter().find(|path| path.is_file());
    let Some(std_metadata) = std_metadata else {
        return Err(format!(
            "fency setup not found: standard library metadata for {backend_name} is missing under {}; compilation is only possible with --nostd",
            std_root.display()
        ));
    };

    let (target_dir_name, runtime_name, legacy_names) = target_runtime_names(target);
    let runtime_root = root.join("runtime");
    let target_dir = runtime_root.join(target_dir_name);
    let mut runtime_path = [target_dir.join(runtime_name), runtime_root.join(runtime_name)]
        .into_iter()
        .find(|path| path.is_file());
    if runtime_path.is_none() {
        runtime_path = legacy_names.iter()
            .map(|name| runtime_root.join(name).join(runtime_name))
            .find(|path| path.is_file());
    }
    let runtime_path = runtime_path.ok_or_else(|| format!(
        "fency setup not found: runtime library is missing (expected {}/{}); compilation is only possible with --nostd",
        target_dir.display(), runtime_name
    ))?;

    let runtime_dir = runtime_path.parent().unwrap_or(&runtime_root).to_owned();
    let mut search_paths = vec![runtime_dir, root.join("libs")];
    if !search_paths.iter().any(|path| path == &runtime_root) {
        search_paths.push(runtime_root);
    }
    Ok(FencyInstallation {
        std_metadata,
        // `link_objects` accepts an `@`-prefixed raw argument so this works
        // with GNU and Darwin linkers without relying on `-l:` support.
        runtime_link_flag: format!("@{}", runtime_path.display()),
        search_paths,
    })
}

fn target_machine_from_cli(flags: &InputFlags) -> TargetMachine {
    LTarget::initialize_all(&InitializationConfig::default());

    let (triple_str, cpu) = match flags.target {
        crate::Target::Amd64Sysv => ("x86_64-unknown-linux-gnu", "generic"),
        crate::Target::Amd64Win => ("x86_64-pc-windows-msvc", "generic"),
        crate::Target::Aarch64Apple => ("aarch64-apple-darwin", "generic"),
        crate::Target::Aarch64Sysv => ("aarch64-unknown-linux-gnu", "generic"),
        crate::Target::Riscv64Sysv => ("riscv64-unknown-linux-gnu", "generic"),
    };

    let triple = TargetTriple::create(triple_str);

    let llvm_target = LTarget::from_triple(&triple)
        .expect("Failed to create LLVM target from triple");

    let o_lvl = match flags.opt_level {
        0 => inkwell::OptimizationLevel::None,
        1 => inkwell::OptimizationLevel::Less,
        2 => inkwell::OptimizationLevel::Default,
        3 => inkwell::OptimizationLevel::Aggressive,
        other => unreachable!("Opt level {}", other)
    };

    llvm_target
        .create_target_machine(
            &triple,
            cpu,
            "",
            o_lvl,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .expect("Failed to create target machine")
}
