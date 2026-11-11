use sha2::{Digest, Sha256};
use std::{fs, path::{Path, PathBuf}};

fn sources(root: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() { sources(&path, files); }
        else if path.extension().is_some_and(|s| s == "rs") { files.push(path); }
    }
}

fn main() {
    let mut files = vec!["Cargo.toml".into(), "Cargo.lock".into(), "build.rs".into(), "vendor/qbe/Cargo.toml".into()];
    sources(Path::new("src"), &mut files);
    sources(Path::new("vendor/qbe/src"), &mut files);
    files.sort();
    let mut digest = Sha256::new();
    for path in files {
        println!("cargo:rerun-if-changed={}", path.display());
        digest.update(path.to_string_lossy().as_bytes());
        digest.update(fs::read(path).unwrap());
    }
    for key in ["RUSTC", "TARGET", "PROFILE", "OPT_LEVEL", "DEBUG", "CARGO_CFG_TARGET_FEATURE", "LLVM_SYS_211_PREFIX", "CARGO_ENCODED_RUSTFLAGS"] {
        println!("cargo:rerun-if-env-changed={key}");
        digest.update(std::env::var(key).unwrap_or_default().as_bytes());
    }
    let rustc = std::process::Command::new(std::env::var("RUSTC").unwrap()).args(["--version", "--verbose"]).output().unwrap();
    digest.update(rustc.stdout);
    println!("cargo:rustc-env=FENCY_BUILD_ID={:x}", digest.finalize());
}
