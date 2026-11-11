//! Coarse compilation-unit caching and explicit, separately compiled dependencies.
use std::{collections::{HashMap, HashSet}, fs, path::{Path, PathBuf}};
use bincode::Options;
use fs2::FileExt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use crate::{cli::InputFlags, fcparse::fcparse::{AstRoot, FuncTable, TraitTable}, seman::seman::StructTable};

type Result<T> = std::result::Result<T, String>;
const MAGIC: &[u8; 8] = b"FENCYMET";
const SCHEMA: u32 = 1;
const LIMIT: u64 = 64 * 1024 * 1024;

#[derive(Clone, Serialize, Deserialize)]
pub struct Interface {
    pub functions: FuncTable,
    pub structs: StructTable,
    pub traits: TraitTable,
    pub generic_functions: HashMap<String, AstRoot>,
    pub generic_impls: HashMap<String, AstRoot>,
    pub generic_uses: Vec<(String, Vec<crate::seman::seman::FType>)>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Recipe {
    pub files: Vec<String>,
    pub output: PathBuf,
    pub flags: InputFlags,
    pub ldflags: Vec<String>,
    pub search_paths: Vec<PathBuf>,
    pub external: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Object {
    pub path: PathBuf,
    pub checksum: String,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct Metadata {
    pub compiler: String,
    pub key: String,
    pub recipe: Recipe,
    pub interface: Interface,
    pub objects: Vec<Object>,
    pub specializations: Vec<String>,
    pub dependency_keys: Vec<(PathBuf, String)>,
}

pub struct Product {
    pub interface: Interface,
    pub objects: Vec<PathBuf>,
    pub specializations: Vec<String>,
}

pub fn hash(bytes: &[u8]) -> String { format!("{:x}", Sha256::digest(bytes)) }
fn file_hash(path: &Path) -> Result<String> {
    fs::read(path).map(|b| hash(&b)).map_err(|e| format!("{}: {e}", path.display()))
}
fn codec() -> impl Options {
    bincode::DefaultOptions::new().with_fixint_encoding().with_limit(LIMIT).reject_trailing_bytes()
}
pub fn read(path: &Path) -> Result<Metadata> {
    if fs::metadata(path).map_err(|e| format!("cannot read metadata {}: {e}", path.display()))?.len() > LIMIT {
        return Err(format!("metadata exceeds size limit: {}", path.display()));
    }
    let bytes = fs::read(path).map_err(|e| format!("cannot read metadata {}: {e}", path.display()))?;
    if bytes.len() < 44 || &bytes[..8] != MAGIC || bytes[8..12] != SCHEMA.to_le_bytes() {
        return Err(format!("invalid or incompatible metadata header: {}", path.display()));
    }
    if bytes.len() as u64 > LIMIT || Sha256::digest(&bytes[44..]).as_slice() != &bytes[12..44] {
        return Err(format!("metadata checksum/size mismatch: {}", path.display()));
    }
    let mut metadata: Metadata = codec().deserialize(&bytes[44..]).map_err(|e| format!("invalid metadata {}: {e}", path.display()))?;
    let parent = absolute(path)?.parent().unwrap().to_owned();
    for object in &mut metadata.objects {
        if object.path.is_relative() { object.path = parent.join(&object.path); }
    }
    for dependency in &mut metadata.recipe.flags.dependencies {
        if dependency.is_relative() { *dependency = parent.join(&dependency); }
        if let Ok(canonical) = fs::canonicalize(&dependency) { *dependency = canonical; }
    }
    for (dependency, _) in &mut metadata.dependency_keys {
        if dependency.is_relative() { *dependency = parent.join(&dependency); }
        if let Ok(canonical) = fs::canonicalize(&dependency) { *dependency = canonical; }
    }
    if metadata.recipe.flags.library { metadata.recipe.output = fs::canonicalize(path).map_err(|e| e.to_string())?; }
    Ok(metadata)
}
pub(crate) fn write(path: &Path, metadata: &Metadata) -> Result<()> {
    let payload = codec().serialize(metadata).map_err(|e| e.to_string())?;
    let mut bytes = Vec::with_capacity(payload.len() + 44);
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(&SCHEMA.to_le_bytes());
    bytes.extend_from_slice(&Sha256::digest(&payload));
    bytes.extend_from_slice(&payload);
    let parent = path.parent().ok_or("metadata needs a parent directory")?;
    fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    let temp = path.with_extension(format!("fmeta.{}.tmp", std::process::id()));
    fs::write(&temp, bytes).map_err(|e| e.to_string())?;
    fs::rename(&temp, path).map_err(|e| format!("publishing {}: {e}", path.display()))
}
fn absolute(path: &Path) -> Result<PathBuf> {
    if path.is_absolute() { Ok(path.to_owned()) }
    else { Ok(std::env::current_dir().map_err(|e| e.to_string())?.join(path)) }
}

fn publish_library(path: &Path, meta: &Metadata) -> Result<()> {
    let mut published = meta.clone();
    let parent = path.parent().ok_or("library output needs a parent")?;
    let identity = hash(meta.objects.iter().map(|o| o.checksum.as_str()).collect::<String>().as_bytes());
    let directory = PathBuf::from(format!("{}.objects", path.file_name().unwrap().to_string_lossy())).join(&identity[..16]);
    fs::create_dir_all(parent.join(&directory)).map_err(|e| e.to_string())?;
    for (i, object) in published.objects.iter_mut().enumerate() {
        let relative = directory.join(format!("object_{i}.{}", object.path.extension().unwrap_or_default().to_string_lossy()));
        let destination = parent.join(&relative);
        if file_hash(&destination).ok().as_ref() != Some(&object.checksum) {
            let temporary = destination.with_extension(format!("{}.tmp", std::process::id()));
            fs::copy(&object.path, &temporary).map_err(|e| e.to_string())?;
            fs::rename(temporary, &destination).map_err(|e| e.to_string())?;
        }
        object.path = relative;
    }
    for dependency in &mut published.recipe.flags.dependencies {
        if let Ok(relative) = dependency.strip_prefix(parent) { *dependency = relative.to_owned(); }
    }
    for (dependency, _) in &mut published.dependency_keys {
        if let Ok(relative) = dependency.strip_prefix(parent) { *dependency = relative.to_owned(); }
    }
    write(path, &published)
}
impl Recipe {
    pub fn new(files: Vec<String>, output: Option<String>, mut flags: InputFlags,
        ldflags: Vec<String>, search_paths: Vec<PathBuf>, external: Vec<String>) -> Result<Self> {
        let files = files.into_iter().map(|p| fs::canonicalize(&p).map(|p| p.to_string_lossy().into_owned())
            .map_err(|e| format!("{p}: {e}"))).collect::<Result<Vec<_>>>()?;
        if files.is_empty() { return Err("at least one input source file is required".into()); }
        flags.dependencies = flags.dependencies.iter().map(|p| absolute(p).map(|p| fs::canonicalize(&p).unwrap_or(p))).collect::<Result<_>>()?;
        flags.cache_dir = Some(absolute(flags.cache_dir.as_deref().unwrap_or(Path::new(".fency/incr")))?);
        let output = absolute(Path::new(&output.unwrap_or_else(|| if flags.library { "library.fmeta" } else { "program" }.into())))?;
        let external = external.iter().map(|p| absolute(Path::new(p)).map(|p| p.to_string_lossy().into_owned())).collect::<Result<_>>()?;
        Ok(Self { files, output, flags, ldflags, search_paths, external })
    }
    fn cache(&self) -> PathBuf {
        // Unit identity is separate from its build key, so latest.fmeta has a stable location.
        let identity = hash(self.output.to_string_lossy().as_bytes());
        self.flags.cache_dir.as_ref().unwrap().join(self.flags.target.to_string())
            .join(self.flags.backend.unwrap().to_string()).join(format!("O{}", self.flags.opt_level))
            .join(&identity[..16])
    }
}

pub fn run(recipe: Recipe) -> Result<()> {
    let mut builder = Builder::new()?;
    let metadata = builder.build(recipe.clone())?;
    if recipe.flags.check || recipe.flags.library || recipe.flags.onlyobjs { return Ok(()); }
    let mut objects = Vec::new();
    let mut seen = HashSet::new();
    builder.collect_objects(&metadata, &mut objects, &mut seen)?;
    let mut ldflags = Vec::new();
    builder.collect_link_flags(&metadata, &mut ldflags, &mut HashSet::new())?;
    crate::link_objects(&objects, &recipe.output, &recipe.flags, &recipe.search_paths, &ldflags)
        .map_err(|e| format!("link failed: {e:?}"))
}

struct Builder {
    compiler: String,
    active: HashSet<PathBuf>,
    done: HashMap<PathBuf, Metadata>,
}
impl Builder {
    fn new() -> Result<Self> {
        Ok(Self { compiler: format!("{}:{}", env!("CARGO_PKG_VERSION"), env!("FENCY_BUILD_ID")), active: HashSet::new(), done: HashMap::new() })
    }
    fn dependency(&mut self, path: &Path, consumer: &Recipe) -> Result<Metadata> {
        if let Some(meta) = self.done.get(path) { return Ok(meta.clone()); }
        if !self.active.insert(path.to_owned()) { return Err(format!("dependency cycle at {}", path.display())); }
        let mut old = read(path)?;
        if !old.recipe.flags.library { return Err(format!("{} is not a library", path.display())); }
        if old.recipe.flags.target != consumer.flags.target || old.recipe.flags.backend != consumer.flags.backend
            || old.recipe.flags.shared != consumer.flags.shared {
            return Err(format!("library {} has an incompatible target, backend, or PIC configuration", path.display()));
        }
        if consumer.flags.frozen_deps {
            if old.compiler != self.compiler { return Err(format!("installed library {} is incompatible with this compiler", path.display())); }
            for object in &old.objects {
                if file_hash(&object.path)? != object.checksum { return Err(format!("installed library object checksum mismatch: {}", object.path.display())); }
            }
            for (dependency, expected) in &old.dependency_keys {
                if self.dependency(dependency, consumer)?.key != *expected {
                    return Err(format!("installed library dependency version mismatch: {}", dependency.display()));
                }
            }
            self.active.remove(path);
            self.done.insert(path.to_owned(), old.clone());
            return Ok(old);
        }
        old.recipe.flags.verbose = consumer.flags.verbose;
        old.recipe.flags.no_incremental = false;
        let rebuilt = self.build(old.recipe)?;
        self.active.remove(path);
        self.done.insert(path.to_owned(), rebuilt.clone());
        Ok(rebuilt)
    }
    fn build(&mut self, recipe: Recipe) -> Result<Metadata> {
        // Resolve the graph before acquiring unit locks, avoiding lock-order deadlocks on cycles.
        let mut imports = Vec::new();
        let mut visited = HashSet::new();
        for path in &recipe.flags.dependencies {
            let dep = self.dependency(path, &recipe)?;
            self.collect_interfaces(&dep, &mut imports, &mut visited)?;
        }
        let cache = recipe.cache();
        fs::create_dir_all(&cache).map_err(|e| e.to_string())?;
        let lock = fs::OpenOptions::new().create(true).truncate(false).read(true).write(true)
            .open(cache.join("build.lock")).map_err(|e| e.to_string())?;
        lock.lock_exclusive().map_err(|e| e.to_string())?;
        let latest = cache.join("latest.fmeta");
        let key = self.key(&recipe, &imports)?;
        let native_sources = recipe.external.iter().any(|p| !p.ends_with(".o") && !p.ends_with(".a"));
        if !recipe.flags.no_incremental && !recipe.flags.check && !native_sources {
            if let Ok(mut cached) = read(&latest) {
                if cached.compiler == self.compiler && cached.key == key && cached.objects.iter().all(|o| file_hash(&o.path).ok().as_ref() == Some(&o.checksum)) {
                    if recipe.flags.verbose { println!("Cache hit: {}", recipe.output.display()); }
                    cached.recipe = recipe.clone();
                    if recipe.flags.library { publish_library(&recipe.output, &cached)?; }
                    return Ok(cached);
                }
            }
        }
        if recipe.flags.verbose { println!("Rebuilding: {}", recipe.output.display()); }
        let staging = cache.join(format!("staging-{}", std::process::id()));
        if staging.exists() { fs::remove_dir_all(&staging).map_err(|e| e.to_string())?; }
        fs::create_dir_all(&staging).map_err(|e| e.to_string())?;
        let product = crate::compile_unit(&recipe, &imports, &staging).map_err(|e| format!("compilation failed: {e:?}"))?;
        let dependency_keys = recipe.flags.dependencies.iter().map(|p| (p.clone(), self.done[p].key.clone())).collect();
        let mut meta = Metadata { compiler: self.compiler.clone(), key: key.clone(), recipe: recipe.clone(), interface: product.interface, objects: vec![], specializations: product.specializations, dependency_keys };
        if recipe.flags.check { let _ = fs::remove_dir_all(staging); return Ok(meta); }
        // Never replace objects referenced by a previous manifest. Concurrent linkers may still use them.
        let generation = cache.join(format!("{}-{}-{}", &key[..16], std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        for object in &product.objects {
            let name = object.file_name().ok_or("object has no filename")?;
            meta.objects.push(Object { path: generation.join(name), checksum: file_hash(object)? });
        }
        fs::rename(&staging, &generation).map_err(|e| e.to_string())?;
        // A source edit during compilation must not publish objects under the old input key.
        if self.key(&recipe, &imports)? != key { return Err("inputs changed during compilation; retry the build".into()); }
        write(&latest, &meta)?;
        if recipe.flags.library { publish_library(&recipe.output, &meta)?; }
        Ok(meta)
    }
    fn key(&self, recipe: &Recipe, imports: &[Metadata]) -> Result<String> {
        let mut normalized = recipe.clone();
        normalized.flags.verbose = false;
        normalized.flags.no_incremental = false;
        let mut bytes = codec().serialize(&normalized).map_err(|e| e.to_string())?;
        bytes.extend_from_slice(self.compiler.as_bytes());
        for path in recipe.files.iter().chain(&recipe.external) {
            bytes.extend_from_slice(file_hash(Path::new(path))?.as_bytes());
        }
        // Include resolved native tools, so switching PATH or tool versions invalidates objects.
        for tool in [recipe.flags.ldas.as_str(), if recipe.flags.backend == Some(crate::cli::CompBackend::QBE) { "qbe" } else { recipe.flags.ldas.as_str() }] {
            let path = resolve_tool(tool)?;
            bytes.extend_from_slice(path.to_string_lossy().as_bytes());
            bytes.extend_from_slice(file_hash(&path)?.as_bytes());
        }
        for dep in imports { bytes.extend_from_slice(dep.key.as_bytes()); }
        Ok(hash(&bytes))
    }
    fn collect_interfaces(&self, meta: &Metadata, result: &mut Vec<Metadata>, seen: &mut HashSet<PathBuf>) -> Result<()> {
        if !seen.insert(meta.recipe.output.clone()) { return Ok(()); }
        for path in &meta.recipe.flags.dependencies {
            self.collect_interfaces(self.done.get(path).ok_or("missing resolved dependency")?, result, seen)?;
        }
        result.push(meta.clone());
        Ok(())
    }
    fn collect_objects(&self, meta: &Metadata, result: &mut Vec<PathBuf>, seen: &mut HashSet<PathBuf>) -> Result<()> {
        if !seen.insert(meta.recipe.output.clone()) { return Ok(()); }
        for object in &meta.objects { result.push(object.path.clone()); }
        for path in &meta.recipe.flags.dependencies {
            self.collect_objects(self.done.get(path).ok_or("missing resolved dependency")?, result, seen)?;
        }
        Ok(())
    }
    fn collect_link_flags(&self, meta: &Metadata, result: &mut Vec<String>, seen: &mut HashSet<PathBuf>) -> Result<()> {
        if !seen.insert(meta.recipe.output.clone()) { return Ok(()); }
        result.extend(meta.recipe.ldflags.iter().cloned());
        for path in &meta.recipe.flags.dependencies {
            self.collect_link_flags(self.done.get(path).ok_or("missing resolved dependency")?, result, seen)?;
        }
        Ok(())
    }
}
fn resolve_tool(name: &str) -> Result<PathBuf> {
    if name.contains(std::path::MAIN_SEPARATOR) { return fs::canonicalize(name).map_err(|e| e.to_string()); }
    for dir in std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()) {
        let path = dir.join(name);
        if path.is_file() { return fs::canonicalize(path).map_err(|e| e.to_string()); }
    }
    Err(format!("native tool not found: {name}"))
}

/// Only direct interfaces are stored in each artifact; graph traversal deduplicates diamonds.
pub fn merge(own: &Interface, imports: &[Metadata]) -> Result<Interface> {
    let specializations = imports.iter().flat_map(|m| m.specializations.iter()).collect::<HashSet<_>>();
    let mut result = Interface { functions: FuncTable::new(), structs: StructTable::new(), traits: TraitTable::new(),
        generic_functions: HashMap::new(), generic_impls: HashMap::new(), generic_uses: vec![] };
    for interface in imports.iter().map(|m| &m.interface).chain(std::iter::once(own)) {
        for (name, functions) in &interface.functions.ft {
            if let Some(previous) = result.functions.ft.get(name) {
                // Repeating an identical external declaration is harmless (e.g. libc printf).
                if previous.len() == functions.len() && previous.iter().zip(functions).all(|(a, b)|
                    ((a.externed && b.externed && a.real_name == b.real_name) || specializations.contains(name))
                        && a.function_type() == b.function_type()) { continue; }
                return Err(format!("duplicate function from separate units: {name}"));
            }
            result.functions.ft.insert(name.clone(), functions.clone());
        }
        for (name, info) in &interface.structs.tab {
            if result.structs.tab.insert(name.clone(), info.clone()).is_some() {
                return Err(format!("duplicate aggregate from separate units: {name}"));
            }
        }
        for (name, info) in &interface.traits.t {
            if result.traits.t.insert(name.clone(), info.clone()).is_some() {
                return Err(format!("duplicate trait from separate units: {name}"));
            }
        }
        for (name, traits) in &interface.traits.impls {
            result.traits.impls.entry(name.clone()).or_default().extend(traits.iter().cloned());
        }
        result.generic_functions.extend(interface.generic_functions.clone());
        result.generic_impls.extend(interface.generic_impls.clone());
        result.generic_uses.extend(interface.generic_uses.clone());
    }
    Ok(result)
}
