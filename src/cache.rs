//! A results cache, so unchanged functions aren't checked again.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

use crate::check::{Options, Outcome, Status};
use crate::unit::FnUnit;

pub struct Cache {
    path: PathBuf,
    entries: BTreeMap<String, Outcome>,
}

/// The cache key: both versions with their callee closures, the options and the tool version.
pub fn key(old: &FnUnit, new: &FnUnit, opts: &Options) -> String {
    let mut hasher = Sha256::new();
    for part in [
        env!("CARGO_PKG_VERSION").to_owned(),
        opts.fingerprint(),
        old.source(),
        new.source(),
    ] {
        hasher.update(part.as_bytes());
        hasher.update([0]);
    }
    hasher
        .finalize()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

impl Cache {
    /// Load the cache at `path`, or start an empty one if it doesn't exist.
    pub fn open(path: &Path) -> io::Result<Self> {
        let entries = match fs::read_to_string(path) {
            Ok(s) => serde_json::from_str(&s).map_err(io::Error::other)?,
            Err(e) if e.kind() == io::ErrorKind::NotFound => BTreeMap::new(),
            Err(e) => return Err(e),
        };
        Ok(Self {
            path: path.to_path_buf(),
            entries,
        })
    }

    pub fn get(&self, key: &str) -> Option<&Outcome> {
        self.entries.get(key)
    }

    /// Store a result. Errors aren't stored, since they may be transient.
    pub fn insert(&mut self, key: String, outcome: &Outcome) {
        if !matches!(outcome.status, Status::Error { .. }) {
            self.entries.insert(key, outcome.clone());
        }
    }

    pub fn save(&self) -> io::Result<()> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(
            &self.path,
            serde_json::to_string_pretty(&self.entries).map_err(io::Error::other)?,
        )
    }
}
