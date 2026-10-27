//! An index of the items in a crate's source files.

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// A module: a file, or an inline `mod m { .. }` inside one.
#[derive(Debug)]
pub struct Module {
    /// The file, relative to the crate root that was loaded.
    pub file: String,
    /// Inline modules within the file.
    pub inline: Vec<String>,
    /// Module path components, from the file path and inline modules.
    pub path: Vec<String>,
    /// Names brought in by `use`, mapped to the full path.
    pub uses: HashMap<String, syn::Path>,
}

impl Module {
    pub fn display(&self) -> String {
        std::iter::once(self.file.clone())
            .chain(self.inline.iter().cloned())
            .collect::<Vec<_>>()
            .join("::")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Fn,
    Const,
    Static,
    TypeAlias,
    /// A struct, enum or union.
    Type,
    ForeignFn,
    ForeignStatic,
}

#[derive(Debug)]
pub struct Entry {
    pub module: usize,
    pub name: String,
    pub kind: Kind,
    /// The item, except for foreign items.
    pub item: Option<syn::Item>,
    /// The linker symbol: of a `#[no_mangle]`/`#[export_name]` function, or of a
    /// foreign function.
    pub symbol: Option<String>,
}

#[derive(Debug, Default)]
pub struct CrateIndex {
    pub modules: Vec<Module>,
    pub entries: Vec<Entry>,
    /// Files that failed to parse, with the error.
    pub parse_errors: Vec<(String, String)>,
}

impl CrateIndex {
    /// Index every `.rs` file under `root` (or `root` itself if it's a file),
    /// skipping `target` and hidden directories.
    pub fn load(root: &Path) -> io::Result<Self> {
        let mut files = Vec::new();
        if root.is_file() {
            files.push(root.to_path_buf());
        } else {
            collect_rs_files(root, &mut files)?;
        }
        files.sort();
        let base = if root.is_file() {
            root.parent().unwrap_or(Path::new("")).to_path_buf()
        } else {
            root.to_path_buf()
        };
        let mut index = Self::default();
        for file in files {
            let rel = file
                .strip_prefix(&base)
                .unwrap_or(&file)
                .to_string_lossy()
                .replace('\\', "/");
            let source = fs::read_to_string(&file)?;
            match syn::parse_file(&source) {
                Ok(parsed) => index.add_file(&rel, parsed.items),
                Err(e) => index.parse_errors.push((rel, e.to_string())),
            }
        }
        Ok(index)
    }

    /// Index a single file's source, as if it were at `rel`.
    pub fn add_source(&mut self, rel: &str, source: &str) -> syn::Result<()> {
        let parsed = syn::parse_file(source)?;
        self.add_file(rel, parsed.items);
        Ok(())
    }

    fn add_file(&mut self, rel: &str, items: Vec<syn::Item>) {
        let mut path: Vec<String> = rel
            .trim_end_matches(".rs")
            .split('/')
            .map(str::to_owned)
            .collect();
        if matches!(
            path.last().map(String::as_str),
            Some("mod" | "lib" | "main")
        ) {
            path.pop();
        }
        self.add_module(rel.to_owned(), vec![], path, items);
    }

    fn add_module(
        &mut self,
        file: String,
        inline: Vec<String>,
        path: Vec<String>,
        items: Vec<syn::Item>,
    ) {
        let module = self.modules.len();
        self.modules.push(Module {
            file: file.clone(),
            inline: inline.clone(),
            path: path.clone(),
            uses: HashMap::new(),
        });
        for item in items {
            match &item {
                syn::Item::Fn(f) => {
                    let symbol = export_symbol(&f.attrs, &f.sig.ident.to_string());
                    self.push(
                        module,
                        f.sig.ident.to_string(),
                        Kind::Fn,
                        Some(item),
                        symbol,
                    );
                }
                syn::Item::Const(c) => {
                    self.push(module, c.ident.to_string(), Kind::Const, Some(item), None)
                }
                syn::Item::Static(s) => {
                    self.push(module, s.ident.to_string(), Kind::Static, Some(item), None)
                }
                syn::Item::Type(t) => self.push(
                    module,
                    t.ident.to_string(),
                    Kind::TypeAlias,
                    Some(item),
                    None,
                ),
                syn::Item::Struct(s) => {
                    self.push(module, s.ident.to_string(), Kind::Type, Some(item), None)
                }
                syn::Item::Enum(e) => {
                    self.push(module, e.ident.to_string(), Kind::Type, Some(item), None)
                }
                syn::Item::Union(u) => {
                    self.push(module, u.ident.to_string(), Kind::Type, Some(item), None)
                }
                syn::Item::ForeignMod(m) => {
                    for foreign in &m.items {
                        // Store each foreign item as its own one-item `extern`
                        // block, so it can be pulled into a unit (and emitted
                        // as a valid declaration) when the heap path models it.
                        let wrap = |fi: syn::ForeignItem| {
                            syn::Item::ForeignMod(syn::ItemForeignMod {
                                attrs: vec![],
                                unsafety: m.unsafety,
                                abi: m.abi.clone(),
                                brace_token: m.brace_token,
                                items: vec![fi],
                            })
                        };
                        match foreign {
                            syn::ForeignItem::Fn(f) => {
                                let name = f.sig.ident.to_string();
                                let symbol = link_name(&f.attrs).unwrap_or_else(|| name.clone());
                                let item = wrap(syn::ForeignItem::Fn(f.clone()));
                                self.push(module, name, Kind::ForeignFn, Some(item), Some(symbol));
                            }
                            syn::ForeignItem::Static(s) => {
                                let item = wrap(syn::ForeignItem::Static(s.clone()));
                                self.push(
                                    module,
                                    s.ident.to_string(),
                                    Kind::ForeignStatic,
                                    Some(item),
                                    None,
                                );
                            }
                            _ => {}
                        }
                    }
                }
                syn::Item::Use(u) => {
                    let mut prefix = syn::Path {
                        leading_colon: u.leading_colon,
                        segments: Default::default(),
                    };
                    let uses = &mut self.modules[module].uses;
                    collect_uses(&u.tree, &mut prefix, uses);
                }
                syn::Item::Mod(m) => {
                    if let Some((_, items)) = &m.content {
                        let mut inline = inline.clone();
                        inline.push(m.ident.to_string());
                        let mut path = path.clone();
                        path.push(m.ident.to_string());
                        self.add_module(file.clone(), inline, path, items.clone());
                    }
                }
                _ => {}
            }
        }
    }

    fn push(
        &mut self,
        module: usize,
        name: String,
        kind: Kind,
        item: Option<syn::Item>,
        symbol: Option<String>,
    ) {
        self.entries.push(Entry {
            module,
            name,
            kind,
            item,
            symbol,
        });
    }

    /// A function's ID: its file, inline modules and name, e.g. `src/a.rs::m::f`.
    pub fn id(&self, entry: usize) -> String {
        let e = &self.entries[entry];
        format!("{}::{}", self.modules[e.module].display(), e.name)
    }

    /// All functions, as entry indices.
    pub fn functions(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.entries.len()).filter(|&i| self.entries[i].kind == Kind::Fn)
    }

    /// Find functions by ID, or by bare name if `query` has no `::`.
    pub fn find_functions(&self, query: &str) -> Vec<usize> {
        self.functions()
            .filter(|&i| {
                if query.contains("::") {
                    self.id(i) == query
                } else {
                    self.entries[i].name == query
                }
            })
            .collect()
    }

    /// Functions defined with this linker symbol.
    pub fn defs_by_symbol(&self, symbol: &str) -> Vec<usize> {
        self.functions()
            .filter(|&i| self.entries[i].symbol.as_deref() == Some(symbol))
            .collect()
    }
}

fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if entry.file_type()?.is_dir() {
            if name != "target" && !name.starts_with('.') {
                collect_rs_files(&path, out)?;
            }
        } else if name.ends_with(".rs") {
            out.push(path);
        }
    }
    Ok(())
}

fn collect_uses(tree: &syn::UseTree, prefix: &mut syn::Path, out: &mut HashMap<String, syn::Path>) {
    match tree {
        syn::UseTree::Path(p) => {
            prefix.segments.push(p.ident.clone().into());
            collect_uses(&p.tree, prefix, out);
            prefix.segments.pop();
        }
        syn::UseTree::Name(n) => {
            if n.ident == "self" {
                if let Some(last) = prefix.segments.last() {
                    out.insert(last.ident.to_string(), prefix.clone());
                }
            } else {
                let mut full = prefix.clone();
                full.segments.push(n.ident.clone().into());
                out.insert(n.ident.to_string(), full);
            }
        }
        syn::UseTree::Rename(r) => {
            let mut full = prefix.clone();
            if r.ident != "self" {
                full.segments.push(r.ident.clone().into());
            }
            out.insert(r.rename.to_string(), full);
        }
        syn::UseTree::Group(g) => {
            for item in &g.items {
                collect_uses(item, prefix, out);
            }
        }
        syn::UseTree::Glob(_) => {}
    }
}

/// The symbol a function is exported under, if it's `#[no_mangle]` or `#[export_name]`.
fn export_symbol(attrs: &[syn::Attribute], name: &str) -> Option<String> {
    for attr in attrs {
        let meta = unwrap_unsafe_attr(&attr.meta);
        let Some(meta) = meta else { continue };
        if meta.path().is_ident("no_mangle") {
            return Some(name.to_owned());
        }
        if meta.path().is_ident("export_name") {
            if let syn::Meta::NameValue(nv) = &meta {
                if let Some(s) = lit_str(&nv.value) {
                    return Some(s);
                }
            }
        }
    }
    None
}

fn link_name(attrs: &[syn::Attribute]) -> Option<String> {
    attrs.iter().find_map(|attr| {
        let meta = unwrap_unsafe_attr(&attr.meta)?;
        match &meta {
            syn::Meta::NameValue(nv) if nv.path.is_ident("link_name") => lit_str(&nv.value),
            _ => None,
        }
    })
}

/// `#[unsafe(no_mangle)]` (edition 2024) to `no_mangle`; other attributes unchanged.
fn unwrap_unsafe_attr(meta: &syn::Meta) -> Option<syn::Meta> {
    match meta {
        syn::Meta::List(list) if list.path.is_ident("unsafe") => list.parse_args().ok(),
        _ => Some(meta.clone()),
    }
}

fn lit_str(expr: &syn::Expr) -> Option<String> {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(s),
            ..
        }) => Some(s.value()),
        _ => None,
    }
}
