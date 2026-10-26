//! A function together with the items it needs, independent of any crate.

use std::fmt;

use quote::ToTokens;
use serde::{Deserialize, Serialize};
use syn::visit::Visit;

use crate::scalar::{self, ScalarKind};

/// Arguments beyond this many aren't supported.
pub const MAX_ARGS: usize = 8;

/// A function and its callee closure: every function, constant and type alias it uses,
/// directly or through other callees.
///
/// The items must be self-contained: paths to other items in the unit are bare
/// identifiers, and everything else is a path into `core`, `std` or `alloc`.
#[derive(Clone, Debug)]
pub struct FnUnit {
    pub function: syn::ItemFn,
    pub callees: Vec<syn::Item>,
}

/// Why a function wasn't checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Skip {
    /// A short, fixed label for grouping, e.g. `global`.
    pub category: String,
    pub detail: String,
}

impl Skip {
    pub fn new(category: &str, detail: impl Into<String>) -> Self {
        Self {
            category: category.to_owned(),
            detail: detail.into(),
        }
    }
}

impl fmt::Display for Skip {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.category, self.detail)
    }
}

/// The scalar kinds of a function's arguments and return value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub args: Vec<ScalarKind>,
    pub ret: ScalarKind,
}

impl Signature {
    pub fn uses_floats(&self) -> bool {
        self.args
            .iter()
            .chain([&self.ret])
            .any(|&k| k == ScalarKind::Float)
    }
}

impl FnUnit {
    /// Parse a unit from source text.
    pub fn parse(function: &str, callees: &[&str]) -> syn::Result<Self> {
        Ok(Self {
            function: syn::parse_str(function)?,
            callees: callees
                .iter()
                .map(|s| syn::parse_str(s))
                .collect::<syn::Result<_>>()?,
        })
    }

    pub fn name(&self) -> String {
        self.function.sig.ident.to_string()
    }

    /// The callees followed by the function.
    pub fn items(&self) -> Vec<syn::Item> {
        let mut items = self.callees.clone();
        items.push(syn::Item::Fn(self.function.clone()));
        items
    }

    /// Formatted source of [`Self::items`].
    pub fn source(&self) -> String {
        prettyplease::unparse(&syn::File {
            shebang: None,
            attrs: vec![],
            items: self.items(),
        })
    }

    /// Check that the unit is in scope for this version, and return its signature.
    pub fn validate(&self) -> Result<Signature, Skip> {
        let sig = self.signature()?;
        let mut checker = BodyChecker { skip: None };
        for item in self.items() {
            checker.visit_item(&item);
        }
        match checker.skip {
            Some(skip) => Err(skip),
            None => Ok(sig),
        }
    }

    /// The function's signature, if every argument and the return value are scalars.
    pub fn signature(&self) -> Result<Signature, Skip> {
        let sig = &self.function.sig;
        if !sig.generics.params.is_empty() {
            return Err(Skip::new("signature", "generic function"));
        }
        if sig.asyncness.is_some() {
            return Err(Skip::new("signature", "async function"));
        }
        if sig.variadic.is_some() {
            return Err(Skip::new("signature", "variadic function"));
        }
        if sig.inputs.len() > MAX_ARGS {
            return Err(Skip::new(
                "signature",
                format!("more than {MAX_ARGS} arguments"),
            ));
        }
        let mut args = Vec::new();
        for input in &sig.inputs {
            let syn::FnArg::Typed(pat_ty) = input else {
                return Err(Skip::new("signature", "method with a receiver"));
            };
            if !matches!(&*pat_ty.pat, syn::Pat::Ident(_) | syn::Pat::Wild(_)) {
                return Err(Skip::new(
                    "signature",
                    "argument with a destructuring pattern",
                ));
            }
            match self.kind_of(&pat_ty.ty, 0) {
                Some(ScalarKind::Unit) | None => {
                    return Err(Skip::new(
                        "signature",
                        format!(
                            "argument `{}` has non-scalar type `{}`",
                            pat_ty.pat.to_token_stream(),
                            pat_ty.ty.to_token_stream()
                        ),
                    ))
                }
                Some(kind) => args.push(kind),
            }
        }
        let ret = match &sig.output {
            syn::ReturnType::Default => ScalarKind::Unit,
            syn::ReturnType::Type(_, ty) => self.kind_of(ty, 0).ok_or_else(|| {
                Skip::new(
                    "signature",
                    format!("non-scalar return type `{}`", ty.to_token_stream()),
                )
            })?,
        };
        Ok(Signature { args, ret })
    }

    /// Whether the function might do floating-point arithmetic.
    pub fn uses_floats(&self) -> bool {
        let mut finder = FloatFinder { found: false };
        for item in self.items() {
            finder.visit_item(&item);
        }
        finder.found
    }

    /// The scalar kind of `ty`, following type aliases among the callees.
    fn kind_of(&self, ty: &syn::Type, depth: usize) -> Option<ScalarKind> {
        if depth > 16 {
            return None;
        }
        match ty {
            syn::Type::Paren(p) => self.kind_of(&p.elem, depth),
            syn::Type::Group(g) => self.kind_of(&g.elem, depth),
            syn::Type::Tuple(t) if t.elems.is_empty() => Some(ScalarKind::Unit),
            syn::Type::Path(p) if p.qself.is_none() => {
                let segs = scalar::idents(&p.path);
                let (last, prefix) = segs.split_last()?;
                if prefix.is_empty() {
                    if let Some(kind) = scalar::primitive(last) {
                        return Some(kind);
                    }
                    if let Some(alias) = self.alias(last) {
                        return self.kind_of(&alias.ty, depth + 1);
                    }
                    return scalar::c_type(last);
                }
                if scalar::is_ffi_module(prefix) {
                    return scalar::c_type(last);
                }
                None
            }
            _ => None,
        }
    }

    fn alias(&self, name: &str) -> Option<&syn::ItemType> {
        self.callees.iter().find_map(|item| match item {
            syn::Item::Type(t) if t.ident == name && t.generics.params.is_empty() => Some(t),
            _ => None,
        })
    }
}

/// What a macro invocation is allowed to be.
pub(crate) enum MacroPolicy {
    /// Its arguments are comma-separated expressions that we can analyze.
    Exprs,
    /// It performs I/O.
    Io,
    /// Anything else.
    Unknown,
}

pub(crate) fn macro_policy(mac: &syn::Macro) -> MacroPolicy {
    let name = mac
        .path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_default();
    match name.as_str() {
        "assert" | "assert_eq" | "assert_ne" | "debug_assert" | "debug_assert_eq"
        | "debug_assert_ne" | "panic" | "unreachable" | "unimplemented" | "todo" | "format" => {
            MacroPolicy::Exprs
        }
        "print" | "println" | "eprint" | "eprintln" | "dbg" | "write" | "writeln" => {
            MacroPolicy::Io
        }
        _ => MacroPolicy::Unknown,
    }
}

pub(crate) fn macro_args(
    mac: &syn::Macro,
) -> syn::Result<syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>> {
    use syn::parse::Parser;
    syn::punctuated::Punctuated::parse_terminated.parse2(mac.tokens.clone())
}

pub(crate) fn macro_skip(mac: &syn::Macro) -> Option<Skip> {
    let name = mac.path.to_token_stream().to_string().replace(' ', "");
    match macro_policy(mac) {
        MacroPolicy::Exprs => match macro_args(mac) {
            Ok(_) => None,
            Err(_) => Some(Skip::new(
                "macro",
                format!("could not analyze the arguments of `{name}!`"),
            )),
        },
        MacroPolicy::Io => Some(Skip::new("io", format!("uses `{name}!`"))),
        MacroPolicy::Unknown => Some(Skip::new("macro", format!("uses macro `{name}!`"))),
    }
}

/// Why a path into the standard library is out of scope, if it is.
pub(crate) fn std_path_skip(segs: &[String]) -> Option<Skip> {
    let [root, module, rest @ ..] = segs else {
        return None;
    };
    if !matches!(root.as_str(), "std" | "core" | "alloc") {
        return None;
    }
    let shown = segs.join("::");
    match module.as_str() {
        "ptr" => Some(Skip::new("raw pointer", format!("uses `{shown}`"))),
        "os" if rest.first().map(String::as_str) == Some("raw") => None,
        // Fences and atomics on locals; globals are excluded separately.
        "sync" if rest.first().map(String::as_str) == Some("atomic") => None,
        "io" | "fs" | "net" | "process" | "env" | "thread" | "time" | "sync" | "os" | "alloc"
        | "arch" => Some(Skip::new("io", format!("uses `{shown}`"))),
        _ => None,
    }
}

/// Finds constructs that are out of scope in a self-contained unit.
struct BodyChecker {
    skip: Option<Skip>,
}

impl BodyChecker {
    fn set(&mut self, skip: Skip) {
        self.skip.get_or_insert(skip);
    }
}

impl<'ast> Visit<'ast> for BodyChecker {
    fn visit_type_ptr(&mut self, _: &'ast syn::TypePtr) {
        self.set(Skip::new("raw pointer", "uses raw pointers"));
    }

    fn visit_item_static(&mut self, s: &'ast syn::ItemStatic) {
        self.set(Skip::new(
            "global",
            format!("declares static `{}`", s.ident),
        ));
    }

    fn visit_item_foreign_mod(&mut self, _: &'ast syn::ItemForeignMod) {
        self.set(Skip::new("foreign call", "declares foreign items"));
    }

    fn visit_path(&mut self, path: &'ast syn::Path) {
        let segs = scalar::idents(path);
        if segs.first().map(String::as_str) == Some("libc") {
            self.set(Skip::new(
                "foreign call",
                format!("uses `{}`", segs.join("::")),
            ));
        } else if let Some(skip) = std_path_skip(&segs) {
            self.set(skip);
        }
        syn::visit::visit_path(self, path);
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        if let Some(skip) = macro_skip(mac) {
            self.set(skip);
        } else if let Ok(args) = macro_args(mac) {
            for arg in &args {
                self.visit_expr(arg);
            }
        }
    }
}

struct FloatFinder {
    found: bool,
}

impl<'ast> Visit<'ast> for FloatFinder {
    fn visit_lit_float(&mut self, _: &'ast syn::LitFloat) {
        self.found = true;
    }

    fn visit_ident(&mut self, ident: &'ast proc_macro2::Ident) {
        if matches!(
            ident.to_string().as_str(),
            "f32" | "f64" | "c_float" | "c_double"
        ) {
            self.found = true;
        }
    }
}
