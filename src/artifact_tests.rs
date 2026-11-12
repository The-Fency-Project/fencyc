use std::{fs, path::{Path, PathBuf}, process::Command};
use crate::artifact::{self, Metadata};

struct Project { dir: PathBuf, backend: String }
impl Project {
    fn new(name: &str) -> Self {
        let backend = std::env::var("FCY_BACKEND").unwrap_or_else(|_| "llvm".into());
        let dir = std::env::current_dir().unwrap().join(format!("testbins/artifacts_{name}_{backend}"));
        if dir.exists() { fs::remove_dir_all(&dir).unwrap(); }
        fs::create_dir_all(&dir).unwrap();
        Self { dir, backend }
    }
    fn write(&self, path: &str, source: &str) { fs::write(self.dir.join(path), source).unwrap(); }
    fn command(&self, args: &[&str], success: bool) -> String {
        let output = Command::new("cargo").args(["run", "--quiet", "--manifest-path"])
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml"))
            .args(["--", "input"]).args(args).args(["--backend", &self.backend, "--nostd", "--verbose"])
            .current_dir(&self.dir).output().unwrap();
        let text = format!("{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.status.success(), success, "{text}");
        assert!(!text.contains("panicked"), "{text}");
        text
    }
    fn meta(&self, path: &str) -> Metadata { artifact::read(&self.dir.join(path)).unwrap() }
    fn cached_meta(&self, source: &str) -> Metadata {
        fn find(dir: &Path, source: &Path) -> Option<Metadata> {
            for entry in fs::read_dir(dir).ok()? {
                let path = entry.ok()?.path();
                if path.is_dir() {
                    if let Some(meta) = find(&path, source) { return Some(meta); }
                } else if path.file_name().unwrap() == "latest.fmeta" {
                    let meta = artifact::read(&path).ok()?;
                    if meta.recipe.files.iter().any(|f| Path::new(f) == source) { return Some(meta); }
                }
            }
            None
        }
        find(&self.dir.join(".fency/incr"), &self.dir.join(source)).unwrap()
    }
    fn run(&self) -> String {
        let output = Command::new(self.dir.join("program")).output().unwrap();
        assert!(output.status.success());
        String::from_utf8(output.stdout).unwrap().trim().into()
    }
}

#[test]
fn reuse_rebuild_and_recover_objects() {
    let p = Project::new("reuse");
    p.write("lib.fcy", "module lib { pub func value() -> int { return 7; } }");
    p.write("main.fcy", "extern func printf(f: str, ...) -> i32; func main() { printf(\"%ld\\n\", lib::value()); return; }");
    let library = ["lib.fcy", "--library", "-o", "lib.fmeta"];
    let app = ["main.fcy", "--dep", "lib.fmeta", "-o", "program"];
    p.command(&library, true);
    let old = p.meta("lib.fmeta");
    p.command(&app, true);
    assert_eq!(p.run(), "7");
    let hit = p.command(&app, true);
    assert_eq!(hit.matches("Cache hit:").count(), 2, "{hit}");
    assert!(!hit.contains("Analyzing"));
    assert_eq!(p.meta("lib.fmeta").objects[0].path, old.objects[0].path);
    // Re-link even if the executable was deleted.
    fs::remove_file(p.dir.join("program")).unwrap();
    p.command(&app, true);
    assert_eq!(p.run(), "7");
    // Consumer source edits leave library objects untouched.
    p.write("main.fcy", "extern func printf(f: str, ...) -> i32; func main() { printf(\"%ld\\n\", lib::value() + 1); return; }");
    p.command(&app, true);
    assert_eq!(p.meta("lib.fmeta").objects[0].path, old.objects[0].path);
    assert_eq!(p.run(), "8");
    // Building the consumer alone discovers and rebuilds a changed dependency.
    p.write("lib.fcy", "module lib { pub func value() -> int { return 20; } }");
    p.command(&app, true);
    let changed = p.meta("lib.fmeta");
    assert_ne!(old.key, changed.key);
    assert_eq!(p.run(), "21");
    // Corrupt/missing objects rebuild, even when sources have not changed.
    let original_cache = p.cached_meta("lib.fcy");
    fs::write(&original_cache.objects[0].path, b"broken").unwrap();
    p.command(&app, true);
    let recovered = p.cached_meta("lib.fcy");
    assert_ne!(original_cache.objects[0].path, recovered.objects[0].path);
    fs::remove_file(&recovered.objects[0].path).unwrap();
    p.command(&app, true);
    assert_eq!(p.run(), "21");
    // A failed compilation preserves the previous good metadata.
    let before = fs::read(p.dir.join("lib.fmeta")).unwrap();
    p.write("lib.fcy", "module lib { pub func value() -> int { return true; } }");
    p.command(&app, false);
    assert_eq!(fs::read(p.dir.join("lib.fmeta")).unwrap(), before);
}

#[test]
fn transitive_diamond_and_generic_imports() {
    let p = Project::new("generics");
    p.write("base.fcy", r#"module base {
        pub struct Box<T> { pub value: T }
        pub func add(x: int) -> int { return x + 1; }
        pub func identity<T>(x: T) -> T { return x; }
        pub func mapped<T>(x: T) -> int { return add(4); }
        pub func existing() -> int { return identity(2); }
    }"#);
    p.write("mid.fcy", "module mid { pub func value() -> int { return base::add(10); } }");
    p.write("main.fcy", r#"extern func printf(f: str, ...) -> i32;
        func main() {
            let b = base::Box<int> { value: 3; };
            printf("%ld %ld %lu %ld %ld\n", mid::value(), base::identity(5), base::identity(6u), b.value, base::mapped(0));
            return;
        }"#);
    p.command(&["base.fcy", "--library", "-o", "base.fmeta"], true);
    let base = p.meta("base.fmeta");
    assert!(!base.specializations.is_empty());
    p.command(&["mid.fcy", "--dep", "base.fmeta", "--library", "-o", "mid.fmeta"], true);
    // Import both base and mid: base must be linked and merged once.
    let app = ["main.fcy", "--dep", "mid.fmeta", "--dep", "base.fmeta", "-o", "program"];
    p.command(&app, true);
    assert_eq!(p.run(), "11 5 6 3 5");
    let hit = p.command(&app, true);
    assert_eq!(hit.matches("Cache hit:").count(), 3, "{hit}");
    p.write("base.fcy", &fs::read_to_string(p.dir.join("base.fcy")).unwrap().replace("x + 1", "x + 2"));
    p.command(&app, true);
    assert_eq!(p.run(), "12 5 6 3 6");
}

#[test]
fn reject_bad_metadata_and_duplicate_symbols() {
    let p = Project::new("invalid");
    p.write("a.fcy", "module duplicate { pub func f() { return; } }");
    p.write("b.fcy", "module duplicate { pub func f() { return; } }");
    p.write("main.fcy", "func main() { return; }");
    p.command(&["a.fcy", "--library", "-o", "a.fmeta"], true);
    p.command(&["b.fcy", "--library", "-o", "b.fmeta"], true);
    let duplicate = p.command(&["main.fcy", "--dep", "a.fmeta", "--dep", "b.fmeta"], false);
    assert!(duplicate.contains("duplicate function"), "{duplicate}");
    let mut bytes = fs::read(p.dir.join("a.fmeta")).unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    fs::write(p.dir.join("a.fmeta"), bytes).unwrap();
    let corrupt = p.command(&["main.fcy", "--dep", "a.fmeta"], false);
    assert!(corrupt.contains("checksum"), "{corrupt}");
    let missing = p.command(&["main.fcy", "--dep", "missing.fmeta"], false);
    assert!(missing.contains("cannot read metadata"), "{missing}");
    let mut cyclic = p.meta("b.fmeta");
    cyclic.recipe.flags.dependencies.push(p.dir.join("b.fmeta"));
    artifact::write(&p.dir.join("b.fmeta"), &cyclic).unwrap();
    let cycle = p.command(&["main.fcy", "--dep", "b.fmeta"], false);
    assert!(cycle.contains("dependency cycle"), "{cycle}");
}

#[test]
fn installed_artifact_without_sources_and_configuration_checks() {
    let p = Project::new("installed");
    p.write("lib.fcy", "module lib { pub func value() -> int { return 5; } }");
    p.write("main.fcy", "extern func printf(f: str, ...) -> i32; func main() { printf(\"%ld\\n\", lib::value()); return; }");
    p.command(&["lib.fcy", "--library", "-o", "lib.fmeta"], true);
    let meta = p.meta("lib.fmeta");
    fs::create_dir_all(p.dir.join("installed")).unwrap();
    for object in &meta.objects {
        let relative = object.path.strip_prefix(&p.dir).unwrap();
        let target = p.dir.join("installed").join(relative);
        fs::create_dir_all(target.parent().unwrap()).unwrap();
        fs::copy(&object.path, target).unwrap();
    }
    fs::copy(p.dir.join("lib.fmeta"), p.dir.join("installed/lib.fmeta")).unwrap();
    fs::remove_file(p.dir.join("lib.fcy")).unwrap();
    let args = ["main.fcy", "--dep", "installed/lib.fmeta", "--frozen-deps", "-o", "program"];
    p.command(&args, true);
    assert_eq!(p.run(), "5");
    assert!(p.command(&args, true).contains("Cache hit:"));
    let mut different = args.to_vec();
    different.extend(["-O", "1"]);
    assert!(p.command(&different, true).contains("Rebuilding:"));
    // Wrong target and compiler metadata are rejected before reaching a backend/linker.
    let mut wrong = p.meta("installed/lib.fmeta");
    wrong.recipe.flags.target = crate::cli::Target::Amd64Win;
    artifact::write(&p.dir.join("installed/lib.fmeta"), &wrong).unwrap();
    assert!(p.command(&args, false).contains("incompatible target"));
    wrong.recipe.flags.target = crate::cli::Target::get_def();
    wrong.compiler = "different compiler".into();
    artifact::write(&p.dir.join("installed/lib.fmeta"), &wrong).unwrap();
    assert!(p.command(&args, false).contains("incompatible with this compiler"));
}

#[test]
fn independent_consumers_share_generic_specializations() {
    let p = Project::new("coalesce");
    p.write("base.fcy", "module base { func helper(x: int) -> int { return x + 1; } pub func generic<T>(x: T) -> int { return helper(4); } }");
    p.write("left.fcy", "module left { pub func value() -> int { return base::generic(1); } }");
    p.write("right.fcy", "module right { pub func value() -> int { return base::generic(2); } }");
    p.write("main.fcy", "extern func printf(f: str, ...) -> i32; func main() { printf(\"%ld %ld\\n\", left::value(), right::value()); return; }");
    p.command(&["base.fcy", "--library", "-o", "base.fmeta"], true);
    p.command(&["left.fcy", "--dep", "base.fmeta", "--library", "-o", "left.fmeta"], true);
    p.command(&["right.fcy", "--dep", "base.fmeta", "--library", "-o", "right.fmeta"], true);
    p.command(&["main.fcy", "--dep", "left.fmeta", "--dep", "right.fmeta", "-o", "program"], true);
    assert_eq!(p.run(), "5 5");
    p.write("base.fcy", "module base { func helper(x: int) -> int { return x + 2; } pub func generic<T>(x: T) -> int { return helper(4); } }");
    p.command(&["base.fcy", "--library", "-o", "base.fmeta"], true);
    let mismatch = p.command(&["main.fcy", "--dep", "left.fmeta", "--frozen-deps", "-o", "program"], false);
    assert!(mismatch.contains("dependency version mismatch"), "{mismatch}");
}

#[test]
fn generic_unions_and_enums_cross_library_boundary() {
    let p = Project::new("generic_aggregates");
    p.write("base.fcy", r#"module base {
        pub union Slot<T> { pub value: T }
        pub enum Maybe<T> { Some(T), None }
    }"#);
    p.write("main.fcy", r#"extern func printf(f: str, ...) -> i32;
        func main() {
            let slot = base::Slot<int> { value: 4; };
            let value = base::Maybe<int>::Some(8);
            let result = match value {
                base::Maybe<int>::Some(v) => { v; }
                base::Maybe<int>::None => { 0; }
            };
            printf("%ld %ld\n", slot.value, result);
            return;
        }"#);
    p.command(&["base.fcy", "--library", "-o", "base.fmeta"], true);
    p.command(&["main.fcy", "--dep", "base.fmeta", "-o", "program"], true);
    assert_eq!(p.run(), "4 8");
}

#[test]
fn concurrent_builds_publish_complete_objects() {
    let p = Project::new("concurrent");
    p.write("lib.fcy", "module lib { pub func value() -> int { return 8; } }");
    p.write("main.fcy", "extern func printf(f: str, ...) -> i32; func main() { printf(\"%ld\\n\", lib::value()); return; }");
    p.command(&["lib.fcy", "--library", "-o", "lib.fmeta"], true);
    let args = ["main.fcy", "--dep", "lib.fmeta", "-o", "program"];
    std::thread::scope(|scope| {
        let first = scope.spawn(|| p.command(&args, true));
        let second = scope.spawn(|| p.command(&args, true));
        let results = [first.join().unwrap(), second.join().unwrap()];
        assert!(results.iter().any(|text| text.contains("Rebuilding:")));
        assert!(results.iter().any(|text| !text.contains("Analyzing")));
    });
    assert_eq!(p.run(), "8");
    for object in p.cached_meta("main.fcy").objects {
        assert_eq!(artifact::hash(&fs::read(object.path).unwrap()), object.checksum);
    }
}
