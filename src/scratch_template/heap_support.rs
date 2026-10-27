// Support for the heap path's scratch crate. Unlike the scalar runner's
// `support.rs`, this pulls in no `Vec`, `String` or allocation-error handling
// -- Kani cannot model the allocation-error handler, and the heap harness
// needs none of it. It provides only bit-equality for scalar return values
// and the correspondence maps for comparing and cloning heaps. It is injected
// as the scratch crate's `support` module, and inlined whole by some tests, so
// it starts with plain comments rather than an inner doc comment.

/// An encoding of a scalar that is equal exactly when the values are identical
/// (floats by bit pattern, so identical NaNs compare equal).
pub trait Bits: Copy {
    fn bits(&self) -> u128;
}

macro_rules! int_bits {
    ($($t:ty),*) => {$(
        impl Bits for $t {
            fn bits(&self) -> u128 { *self as u128 }
        }
    )*};
}
int_bits!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, bool, char);

impl Bits for f32 {
    fn bits(&self) -> u128 {
        self.to_bits() as u128
    }
}
impl Bits for f64 {
    fn bits(&self) -> u128 {
        self.to_bits() as u128
    }
}
impl Bits for () {
    fn bits(&self) -> u128 {
        0
    }
}

/// The most objects either heap can hold. Symbolic heaps are bounded by the
/// builder's depth, so a fixed capacity avoids `Vec`, whose allocation makes
/// Kani far slower. Overflowing it is a bug in the bound, so it panics.
pub const HEAP_CAP: usize = 128;

/// The longest C string, including the NUL terminator, a symbolic buffer holds.
/// Kept small: a symbolic string length explodes Kani's search quickly.
pub const CSTR_CAP: usize = 6;

/// A bounded, NUL-terminated symbolic C string on the heap. The last byte is
/// always NUL, so any read that stops at a NUL stays in bounds whatever the
/// interior bytes are; interior bytes are symbolic and may themselves be NUL.
/// Returned as a raw pointer the callee treats as `*const c_char`.
pub unsafe fn gen_cstr() -> *mut core::ffi::c_char {
    let mut buf = Box::new([0 as core::ffi::c_char; CSTR_CAP]);
    for b in buf.iter_mut().take(CSTR_CAP - 1) {
        *b = kani::any();
    }
    buf[CSTR_CAP - 1] = 0;
    Box::into_raw(buf) as *mut core::ffi::c_char
}

/// A byte-for-byte copy of a `gen_cstr` buffer into a fresh allocation, so both
/// versions receive identical strings. `src` must be null or a `gen_cstr`
/// buffer, so reading `CSTR_CAP` bytes from it is in bounds.
pub unsafe fn clone_cstr(src: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    if src.is_null() {
        return core::ptr::null_mut();
    }
    let mut buf = Box::new([0 as core::ffi::c_char; CSTR_CAP]);
    for (i, b) in buf.iter_mut().enumerate() {
        *b = *src.add(i);
    }
    Box::into_raw(buf) as *mut core::ffi::c_char
}

/// The most distinct oracle calls a run records. A pure external function is
/// modelled as an uninterpreted function: the same `(id, key)` always yields
/// the same symbolic value, so both versions agree for equal arguments.
pub const ORACLE_CAP: usize = 64;

/// A shared memo of oracle results, keyed by `(function id, argument bits)`.
/// Both versions consult the same table, so a pure external call returns the
/// same value for the same arguments in each -- and a divergence in arguments
/// surfaces as differing results. Sound only for deterministic, side-effect
/// free functions.
pub struct Oracle {
    keys: [(u64, u128); ORACLE_CAP],
    vals: [u128; ORACLE_CAP],
    len: usize,
}

impl Default for Oracle {
    fn default() -> Self {
        Oracle {
            keys: [(0, 0); ORACLE_CAP],
            vals: [0; ORACLE_CAP],
            len: 0,
        }
    }
}

impl Oracle {
    pub fn get(&mut self, id: u64, key: u128) -> u128 {
        for i in 0..self.len {
            if self.keys[i] == (id, key) {
                return self.vals[i];
            }
        }
        assert!(self.len < ORACLE_CAP, "oracle exceeds ORACLE_CAP");
        let v: u128 = kani::any();
        self.keys[self.len] = (id, key);
        self.vals[self.len] = v;
        self.len += 1;
        v
    }
}

/// The one shared oracle for a run. Both versions' modelled external calls go
/// through it, so equal arguments give equal results across versions.
pub static mut ORACLE: Oracle = Oracle {
    keys: [(0, 0); ORACLE_CAP],
    vals: [0; ORACLE_CAP],
    len: 0,
};

/// The most external calls a run records. Observable-behaviour equivalence
/// (VOC / CoVaC): the first version records its external-call trace, the second
/// must replay it exactly, so both make the same calls in the same order.
pub const TRACE_CAP: usize = 256;

/// One recorded external call: its function id, up to three argument words
/// (scalars by value, pointers by address, floats by bit pattern), and the
/// symbolic result handed back (shared, so both versions see the same result).
#[derive(Clone, Copy, Default)]
pub struct Call {
    pub id: u64,
    pub args: [u128; 3],
    pub ret: u128,
}

/// The shared external-call trace and its record/replay state.
pub struct Trace {
    pub calls: [Call; TRACE_CAP],
    pub len: usize,
    pub cursor: usize,
    pub recording: bool,
}

pub static mut TRACE: Trace = Trace {
    calls: [Call {
        id: 0,
        args: [0; 3],
        ret: 0,
    }; TRACE_CAP],
    len: 0,
    cursor: 0,
    recording: true,
};

impl Trace {
    /// Begin recording the first version's external calls.
    pub fn record(&mut self) {
        self.len = 0;
        self.cursor = 0;
        self.recording = true;
    }
    /// Begin replaying them against the second version.
    pub fn replay(&mut self) {
        self.cursor = 0;
        self.recording = false;
    }
    /// After the second version, require it consumed the whole trace (it made
    /// exactly the same number of external calls).
    pub fn finish(&self) {
        if !self.recording {
            assert!(self.cursor == self.len, "external-call count differs");
        }
    }
    /// One external call. While recording, append it with a fresh symbolic
    /// result; while replaying, require it matches the recorded call and return
    /// that call's result, so both versions make identical observable calls.
    pub fn step(&mut self, id: u64, args: [u128; 3]) -> u128 {
        if self.recording {
            assert!(self.len < TRACE_CAP, "trace exceeds TRACE_CAP");
            let ret: u128 = kani::any();
            self.calls[self.len] = Call { id, args, ret };
            self.len += 1;
            ret
        } else {
            assert!(self.cursor < self.len, "second version makes more external calls");
            let c = self.calls[self.cursor];
            // Compare element-wise: `[u128; 3]` equality lowers to `memcmp`,
            // whose byte loop would need a large unwind bound.
            let same = c.id == id
                && c.args[0] == args[0]
                && c.args[1] == args[1]
                && c.args[2] == args[2];
            assert!(same, "external call sequence differs");
            self.cursor += 1;
            c.ret
        }
    }
}

/// A pointer to a single symbolic scalar on the heap, or null. Models a
/// `*mut T`/`*const T` argument or field that points at one value (a scalar
/// out-parameter, say). A function that instead indexes it as an array past
/// element 0 reads out of bounds, which Kani reports as a failure, so such a
/// function is left unproved rather than being called equivalent unsoundly.
pub unsafe fn gen_cell<T: kani::Arbitrary>() -> *mut T {
    if kani::any() {
        core::ptr::null_mut()
    } else {
        Box::into_raw(Box::new(kani::any()))
    }
}

/// A copy of a `gen_cell` pointer's value into a fresh allocation, so both
/// versions get the same scalar. `src` must be null or a `gen_cell` pointer.
pub unsafe fn clone_cell<T: Copy>(src: *const T) -> *mut T {
    if src.is_null() {
        core::ptr::null_mut()
    } else {
        Box::into_raw(Box::new(*src))
    }
}

/// Whether two `gen_cell` pointers' values are identical (matching null-ness).
/// Compares the post-state, catching a divergent write through a `*mut T`.
pub unsafe fn same_cell<T: Bits>(a: *const T, b: *const T) -> bool {
    if a.is_null() || b.is_null() {
        return a.is_null() == b.is_null();
    }
    Bits::bits(&*a) == Bits::bits(&*b)
}

/// Whether two `gen_cstr` buffers hold the same bytes up to and including the
/// first NUL. Both must be null or `gen_cstr` buffers.
pub unsafe fn same_cstr(a: *const core::ffi::c_char, b: *const core::ffi::c_char) -> bool {
    if a.is_null() || b.is_null() {
        return a.is_null() == b.is_null();
    }
    for i in 0..CSTR_CAP {
        let x = *a.add(i);
        if x != *b.add(i) {
            return false;
        }
        if x == 0 {
            break;
        }
    }
    true
}

/// The result of linking a pair into the correspondence map.
pub enum Link {
    New,
    Seen,
    Conflict,
}

/// A correspondence between the two heaps' objects, kept functional and
/// injective (see `specs/Heap.als`).
pub struct Corr {
    pairs: [(*const (), *const ()); HEAP_CAP],
    len: usize,
}

impl Default for Corr {
    fn default() -> Self {
        Corr {
            pairs: [(core::ptr::null(), core::ptr::null()); HEAP_CAP],
            len: 0,
        }
    }
}

impl Corr {
    pub fn link(&mut self, a: *const (), b: *const ()) -> Link {
        for i in 0..self.len {
            let (x, y) = self.pairs[i];
            if x == a && y == b {
                return Link::Seen;
            }
            if x == a || y == b {
                return Link::Conflict;
            }
        }
        assert!(self.len < HEAP_CAP, "heap exceeds HEAP_CAP");
        self.pairs[self.len] = (a, b);
        self.len += 1;
        Link::New
    }
}

/// A map from each cloned source object to its copy, so a deep copy preserves
/// sharing and terminates on cycles.
pub struct CloneMap {
    pairs: [(*const (), *const ()); HEAP_CAP],
    len: usize,
}

impl Default for CloneMap {
    fn default() -> Self {
        CloneMap {
            pairs: [(core::ptr::null(), core::ptr::null()); HEAP_CAP],
            len: 0,
        }
    }
}

impl CloneMap {
    pub fn get(&self, a: *const ()) -> Option<*const ()> {
        for i in 0..self.len {
            if self.pairs[i].0 == a {
                return Some(self.pairs[i].1);
            }
        }
        None
    }
    pub fn insert(&mut self, a: *const (), b: *const ()) {
        assert!(self.len < HEAP_CAP, "heap exceeds HEAP_CAP");
        self.pairs[self.len] = (a, b);
        self.len += 1;
    }
}
