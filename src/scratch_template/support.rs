// Input generation, comparison and the native runner for a scratch crate.
// This file is copied verbatim into every scratch crate.

use core::fmt::Debug;

/// A splitmix64 generator, so runs are reproducible from a seed.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn next_u128(&mut self) -> u128 {
        ((self.next_u64() as u128) << 64) | self.next_u64() as u128
    }
}

pub trait Scalar: Copy + Debug {
    /// Decode from little-endian bytes, as in Kani's concrete playback.
    fn from_le(bytes: &[u8]) -> Self;
    /// An encoding that is equal exactly when the values are identical
    /// (floats by bit pattern, so identical NaNs are equal).
    fn bits(&self) -> u128;
    fn edge_cases() -> Vec<Self>;
    fn random(rng: &mut Rng) -> Self;
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}

macro_rules! int_scalar {
    ($($t:ty),*) => {$(
        impl Scalar for $t {
            fn from_le(bytes: &[u8]) -> Self {
                let mut buf = [0u8; core::mem::size_of::<$t>()];
                let n = bytes.len().min(buf.len());
                buf[..n].copy_from_slice(&bytes[..n]);
                <$t>::from_le_bytes(buf)
            }
            fn bits(&self) -> u128 {
                *self as u128
            }
            fn edge_cases() -> Vec<Self> {
                let mut v: Vec<$t> = vec![
                    0, 1, 2, 7, 8,
                    <$t>::MAX, <$t>::MIN, <$t>::MAX - 1, <$t>::MIN.wrapping_add(1),
                    <$t>::MAX / 2, <$t>::MIN / 2,
                    (0 as $t).wrapping_sub(1), (0 as $t).wrapping_sub(2),
                ];
                v.sort();
                v.dedup();
                v
            }
            fn random(rng: &mut Rng) -> Self {
                match rng.next_u64() % 4 {
                    0 | 1 => rng.next_u128() as $t,
                    2 => ((rng.next_u64() % 33) as i64 - 16) as $t,
                    _ => {
                        let width = 8 * core::mem::size_of::<$t>() as u32;
                        let shift = (rng.next_u64() % width as u64) as u32;
                        let base = 1u128.wrapping_shl(shift) as $t;
                        base.wrapping_add(((rng.next_u64() % 3) as $t).wrapping_sub(1))
                    }
                }
            }
        }
    )*};
}

int_scalar!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

macro_rules! float_scalar {
    ($t:ty, $bits:ty) => {
        impl Scalar for $t {
            fn from_le(bytes: &[u8]) -> Self {
                <$t>::from_bits(<$bits as Scalar>::from_le(bytes))
            }
            fn bits(&self) -> u128 {
                self.to_bits() as u128
            }
            fn edge_cases() -> Vec<Self> {
                vec![
                    0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, 3.0, 10.0, -10.0,
                    <$t>::NAN, -<$t>::NAN, <$t>::INFINITY, <$t>::NEG_INFINITY,
                    <$t>::MIN_POSITIVE, -<$t>::MIN_POSITIVE,
                    // The smallest and largest subnormals.
                    <$t>::from_bits(1), -<$t>::from_bits(1),
                    <$t>::from_bits(<$t>::MIN_POSITIVE.to_bits() - 1),
                    <$t>::MAX, <$t>::MIN, <$t>::EPSILON, 1.0 + <$t>::EPSILON,
                ]
            }
            fn random(rng: &mut Rng) -> Self {
                match rng.next_u64() % 3 {
                    0 => <$t>::from_bits(rng.next_u128() as $bits),
                    1 => ((rng.next_u64() as f64 / u64::MAX as f64) * 200.0 - 100.0) as $t,
                    _ => ((rng.next_u64() % 2001) as i64 - 1000) as $t,
                }
            }
            fn describe(&self) -> String {
                format!("{:?} (bits {:#x})", self, self.to_bits())
            }
        }
    };
}

float_scalar!(f32, u32);
float_scalar!(f64, u64);

impl Scalar for bool {
    fn from_le(bytes: &[u8]) -> Self {
        bytes.first().map_or(false, |&b| b != 0)
    }
    fn bits(&self) -> u128 {
        *self as u128
    }
    fn edge_cases() -> Vec<Self> {
        vec![false, true]
    }
    fn random(rng: &mut Rng) -> Self {
        rng.next_u64() & 1 == 1
    }
}

impl Scalar for char {
    fn from_le(bytes: &[u8]) -> Self {
        char::from_u32(<u32 as Scalar>::from_le(bytes)).unwrap_or('\0')
    }
    fn bits(&self) -> u128 {
        *self as u128
    }
    fn edge_cases() -> Vec<Self> {
        vec!['\0', 'a', 'Z', '0', ' ', '\x7f', '\u{80}', 'é', '\u{D7FF}', '\u{E000}', '\u{10FFFF}']
    }
    fn random(rng: &mut Rng) -> Self {
        loop {
            if let Some(c) = char::from_u32((rng.next_u64() % 0x11_0000) as u32) {
                return c;
            }
        }
    }
}

impl Scalar for () {
    fn from_le(_: &[u8]) -> Self {}
    fn bits(&self) -> u128 {
        0
    }
    fn edge_cases() -> Vec<Self> {
        vec![()]
    }
    fn random(_: &mut Rng) -> Self {}
}

/// A tuple of arguments.
pub trait Inputs: Copy + Debug {
    fn from_le(fields: &[Vec<u8>]) -> Self;
    fn random(rng: &mut Rng) -> Self;
    /// Combinations of each argument's edge cases: all of them if there are at
    /// most `limit`, otherwise `limit` of them chosen at random.
    fn edge_cases(limit: usize) -> Vec<Self>;
    fn describe(&self) -> String;
}

macro_rules! tuple_inputs {
    ($($T:ident $i:tt),*) => {
        impl<$($T: Scalar),*> Inputs for ($($T,)*) {
            fn from_le(fields: &[Vec<u8>]) -> Self {
                let _ = fields;
                ($($T::from_le(fields.get($i).map_or(&[][..], |v| v.as_slice())),)*)
            }
            fn random(rng: &mut Rng) -> Self {
                let _ = &rng;
                ($($T::random(rng),)*)
            }
            fn edge_cases(limit: usize) -> Vec<Self> {
                let edges = ($($T::edge_cases(),)*);
                let lens: &[usize] = &[$(edges.$i.len()),*];
                let total = lens.iter().fold(1usize, |a, &b| a.saturating_mul(b));
                let mut rng = Rng::new(0xED6E);
                let mut out = Vec::new();
                for k in 0..total.min(limit) {
                    let mut idx = if total <= limit { k } else { rng.next_u64() as usize % total };
                    let _ = &mut idx;
                    out.push(($({
                        let j = idx % lens[$i];
                        idx /= lens[$i];
                        edges.$i[j]
                    },)*));
                }
                out
            }
            fn describe(&self) -> String {
                let parts: Vec<String> = vec![$(Scalar::describe(&self.$i)),*];
                format!("({})", parts.join(", "))
            }
        }
    };
}

tuple_inputs!();
tuple_inputs!(A 0);
tuple_inputs!(A 0, B 1);
tuple_inputs!(A 0, B 1, C 2);
tuple_inputs!(A 0, B 1, C 2, D 3);
tuple_inputs!(A 0, B 1, C 2, D 3, E 4);
tuple_inputs!(A 0, B 1, C 2, D 3, E 4, F 5);
tuple_inputs!(A 0, B 1, C 2, D 3, E 4, F 5, G 6);
tuple_inputs!(A 0, B 1, C 2, D 3, E 4, F 5, G 6, H 7);

/// What one call did.
pub enum Outcome {
    Returned(u128, String),
    Panicked(String),
}

impl Outcome {
    /// Equivalent: the same value, or both panicked.
    pub fn same(&self, other: &Outcome) -> bool {
        match (self, other) {
            (Outcome::Returned(a, _), Outcome::Returned(b, _)) => a == b,
            (Outcome::Panicked(_), Outcome::Panicked(_)) => true,
            _ => false,
        }
    }
}

impl core::fmt::Display for Outcome {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Outcome::Returned(_, d) => write!(f, "returned {}", clean(d)),
            Outcome::Panicked(m) => write!(f, "panicked: {}", clean(m)),
        }
    }
}

fn clean(s: &str) -> String {
    s.replace(['\t', '\n', '\r'], " ")
}

#[cfg(not(kani))]
pub fn run(f: fn(crate::Args) -> crate::Ret, a: crate::Args) -> Outcome {
    match std::panic::catch_unwind(move || f(a)) {
        // `()` is both a `Scalar` and an `Inputs`, so name the trait.
        Ok(r) => Outcome::Returned(Scalar::bits(&r), Scalar::describe(&r)),
        Err(e) => Outcome::Panicked(
            e.downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| e.downcast_ref::<String>().cloned())
                .unwrap_or_default(),
        ),
    }
}

/// `runner test SEED N EDGE_LIMIT`: edge cases, then N random inputs; stop at
/// the first difference.
/// `runner replay`: one input per stdin line, as comma-separated hex byte strings.
#[cfg(not(kani))]
pub fn run_main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().collect();
    let compare = |a: crate::Args| -> (bool, String) {
        let o = run(crate::call_old, a);
        let n = run(crate::call_new, a);
        (o.same(&n), format!("{}\t{}\t{}", clean(&Inputs::describe(&a)), o, n))
    };
    match args.get(1).map(String::as_str) {
        Some("test") => {
            let seed: u64 = args[2].parse().unwrap();
            let n: u64 = args[3].parse().unwrap();
            let limit: usize = args[4].parse().unwrap();
            let mut cases = 0u64;
            let mut rng = Rng::new(seed);
            let edges = <crate::Args as Inputs>::edge_cases(limit);
            let randoms = (0..n).map(|_| <crate::Args as Inputs>::random(&mut rng));
            for a in edges.into_iter().chain(randoms) {
                cases += 1;
                let (same, line) = compare(a);
                if !same {
                    println!("MISMATCH\t{line}");
                    return;
                }
            }
            println!("OK\t{cases}");
        }
        Some("replay") => {
            use std::io::BufRead;
            for line in std::io::stdin().lock().lines() {
                let line = line.unwrap();
                let fields: Vec<Vec<u8>> = line
                    .split(',')
                    .filter(|f| !f.is_empty())
                    .map(|f| {
                        (0..f.len())
                            .step_by(2)
                            .map(|i| u8::from_str_radix(&f[i..i + 2], 16).unwrap())
                            .collect()
                    })
                    .collect();
                let (same, line) = compare(<crate::Args as Inputs>::from_le(&fields));
                println!("{}\t{line}", if same { "SAME" } else { "DIFF" });
            }
        }
        _ => {
            eprintln!("usage: runner test SEED N EDGE_LIMIT | runner replay");
            std::process::exit(2);
        }
    }
}

// --- Symbolic-heap support (used by generated `gen_`/`clone_`/`same_` code) ---

/// The result of linking a pair into the correspondence map.
pub enum Link {
    /// A new pair; keep comparing the pointees.
    New,
    /// This exact pair was already linked; the pointees already matched.
    Seen,
    /// One side is already linked to a different partner, which breaks the
    /// map's functionality or injectivity: the heaps differ.
    Conflict,
}

/// A correspondence between the two heaps' objects, kept functional (each `a`
/// maps to one `b`) and injective (each `b` from one `a`). `specs/Heap.als`
/// shows both directions are needed: without injectivity, two distinct objects
/// on one side sharing a partner on the other would wrongly compare equal.
#[derive(Default)]
pub struct Corr {
    pairs: Vec<(*const (), *const ())>,
}

impl Corr {
    pub fn link(&mut self, a: *const (), b: *const ()) -> Link {
        for &(x, y) in &self.pairs {
            if x == a && y == b {
                return Link::Seen;
            }
            if x == a || y == b {
                return Link::Conflict;
            }
        }
        self.pairs.push((a, b));
        Link::New
    }
}

/// A map from each cloned source object to its copy, so that a deep copy
/// preserves sharing (two fields pointing at one object stay shared) and
/// terminates on cycles (a back-edge resolves to the registered copy).
#[derive(Default)]
pub struct CloneMap {
    pairs: Vec<(*const (), *const ())>,
}

impl CloneMap {
    pub fn get(&self, a: *const ()) -> Option<*const ()> {
        self.pairs.iter().find(|&&(x, _)| x == a).map(|&(_, y)| y)
    }
    pub fn insert(&mut self, a: *const (), b: *const ()) {
        self.pairs.push((a, b));
    }
}
