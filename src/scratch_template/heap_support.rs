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

/// The largest modelled `malloc`-style allocation, in bytes (see
/// [`Trace::alloc_bytes`]). Matches `CSTR_CAP`: the per-byte seeding loop then
/// unwinds within the same bound a symbolic C string already needs, so no proof
/// has to raise its unwind for an allocation. Large enough for a scalar or a
/// small `#[repr(C)]` record; a request past it yields an undersized buffer, so
/// any out-of-bound access fails verification rather than being proved.
pub const ALLOC_CAP: usize = CSTR_CAP;

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

/// One argument of a variadic external call, recorded into the trace: its bits
/// and kind (0 scalar/float by value, 1 NUL-terminated string by content).
/// Implemented only for the types a format call actually passes, so an
/// unsupported argument type is a compile error (the function is then skipped,
/// never modelled unsoundly).
pub trait TraceArg {
    fn bits(&self) -> u128;
    fn kind(&self) -> u8;
}

macro_rules! trace_arg_scalar {
    ($($t:ty),*) => {$(
        impl TraceArg for $t {
            fn bits(&self) -> u128 { *self as u128 }
            fn kind(&self) -> u8 { 0 }
        }
    )*};
}
trace_arg_scalar!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, bool, char);

impl TraceArg for f32 {
    fn bits(&self) -> u128 { self.to_bits() as u128 }
    fn kind(&self) -> u8 { 0 }
}
impl TraceArg for f64 {
    fn bits(&self) -> u128 { self.to_bits() as u128 }
    fn kind(&self) -> u8 { 0 }
}

// `c_char`/`c_uchar` pointers are strings: recorded by content (kind 1). Other
// pointer types have no impl on purpose, so a `%p` of some struct pointer makes
// the shim fail to compile and the function is left unmodelled.
macro_rules! trace_arg_cstr {
    ($($t:ty),*) => {$(
        impl TraceArg for $t {
            fn bits(&self) -> u128 { *self as usize as u128 }
            fn kind(&self) -> u8 { 1 }
        }
    )*};
}
trace_arg_cstr!(*const i8, *mut i8, *const u8, *mut u8);

// Non-string scalar pointers (e.g. `sscanf`'s output targets `*mut i32`):
// recorded by identity (kind 2), compared through the heap bijection, so two
// corresponding objects compare equal regardless of their concrete addresses.
// Pointer types without an impl (a struct pointer, say) still fail to compile,
// leaving that call unmodelled rather than modelled unsoundly.
macro_rules! trace_arg_ptr {
    ($($t:ty),*) => {$(
        impl TraceArg for $t {
            fn bits(&self) -> u128 { *self as usize as u128 }
            fn kind(&self) -> u8 { 2 }
        }
    )*};
}
trace_arg_ptr!(
    *const i16, *mut i16, *const u16, *mut u16,
    *const i32, *mut i32, *const u32, *mut u32,
    *const i64, *mut i64, *const u64, *mut u64,
    *const isize, *mut isize, *const usize, *mut usize,
    *const f32, *mut f32, *const f64, *mut f64,
    *const core::ffi::c_void, *mut core::ffi::c_void
);

/// The most external calls a run records. Observable-behaviour equivalence
/// (VOC / CoVaC): the first version records its external-call trace, the second
/// must replay it exactly, so both make the same calls in the same order.
pub const TRACE_CAP: usize = 256;

/// One recorded external call: its function id, up to three argument words,
/// each argument's kind (0 scalar/float by value, 1 NUL-terminated string by
/// content, 2 pointer by heap bijection, 3 unused), and the symbolic result
/// handed back (shared, so both versions see the same result).
#[derive(Clone, Copy, Default)]
pub struct Call {
    pub id: u64,
    pub args: [u128; 3],
    pub kinds: [u8; 3],
    pub ret: u128,
}

/// The shared external-call trace, its record/replay state, and a partial
/// bijection between the two versions' pointer arguments (the SimuLiris/WhyRel
/// approach: equal pointers are those that correspond, not those with equal
/// addresses).
pub struct Trace {
    pub calls: [Call; TRACE_CAP],
    pub len: usize,
    pub cursor: usize,
    pub recording: bool,
    pub bij: [(u128, u128); TRACE_CAP],
    pub blen: usize,
}

pub static mut TRACE: Trace = Trace {
    calls: [Call {
        id: 0,
        args: [0; 3],
        kinds: [0; 3],
        ret: 0,
    }; TRACE_CAP],
    len: 0,
    cursor: 0,
    recording: true,
    bij: [(0, 0); TRACE_CAP],
    blen: 0,
};

impl Trace {
    /// Begin recording the first version's external calls.
    pub fn record(&mut self) {
        self.len = 0;
        self.cursor = 0;
        self.blen = 0;
        self.recording = true;
    }
    /// Link a recorded (first-version) pointer to a replayed (second-version)
    /// one, keeping the correspondence functional and injective. Returns false
    /// on a conflict (the pointers don't correspond), i.e. a divergence.
    fn link(&mut self, a: u128, b: u128) -> bool {
        for i in 0..self.blen {
            let (x, y) = self.bij[i];
            if x == a && y == b {
                return true;
            }
            if x == a || y == b {
                return false;
            }
        }
        if self.blen < TRACE_CAP {
            self.bij[self.blen] = (a, b);
            self.blen += 1;
        }
        true
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
    /// Model a formatting function's output: write a shared, bounded,
    /// NUL-terminated symbolic string into `dst`. The bytes come from the trace
    /// (keyed by position), so both versions produce the same output -- the
    /// formatted result modelled as a deterministic function of the call. `dst`
    /// must have room for `CSTR_CAP` bytes, else the write is out of bounds and
    /// Kani reports a failure (the function is then not proved).
    pub unsafe fn fill_cstr(&mut self, id: u64, dst: *mut core::ffi::c_char) {
        if dst.is_null() {
            return;
        }
        let mut i = 0usize;
        while i < CSTR_CAP - 1 {
            let b = self.step(id, [i as u128, 0, 0], [0, 3, 3]) as u8;
            *dst.add(i) = b as core::ffi::c_char;
            i += 1;
        }
        *dst.add(CSTR_CAP - 1) = 0;
    }

    /// Model a `malloc`-style allocator returning `n` bytes, as an observable
    /// result. A single recorded word decides null-ness, shared across the two
    /// versions (so the caller's `is_null()` failure branch is explored, and
    /// identically in both), then on success each version gets its *own* fresh
    /// buffer -- never a shared one, which would be unsound because the second
    /// run would see the first's writes.
    ///
    /// The buffer's bytes are independent symbolic values, not shared across the
    /// versions. That is sound for a *proof*: distinct symbolic contents can
    /// only make the two versions look more different, never falsely equal, so a
    /// divergent write is still caught and a genuine equivalence is never
    /// over-claimed. It is also what the usual case needs: a function that
    /// writes its result before reading it overwrites the bytes, so the two
    /// versions compare their own writes exactly. (A function that returns
    /// *unwritten* bytes compares two independent symbols and so is left
    /// unproved rather than wrongly proved.) The whole buffer is one symbolic
    /// value (`kani::any()` over the fixed array), so there is no seeding loop
    /// to unwind -- routing bytes through `step` would nest a loop inside
    /// `step`'s own and need the unwind bound raised.
    ///
    /// Bounded by `ALLOC_CAP` bytes: a larger request gives a buffer that is too
    /// small, so any access past the bound is out of bounds and Kani reports a
    /// failure (the function is left unproved, never falsely proved).
    pub unsafe fn alloc_bytes(&mut self, id: u64, _n: usize) -> *mut core::ffi::c_void {
        // A distinct arg shape (`u128::MAX`) keeps the null-decision event out
        // of the ordinary argument namespace.
        let want_null = (self.step(id, [u128::MAX, 0, 0], [0, 3, 3]) & 1) == 0;
        if want_null {
            return core::ptr::null_mut();
        }
        // A fixed-size box (no `Vec`, which slows Kani); the pointer stays valid
        // for the whole run (leaked -- freeing modelled objects is unnecessary
        // and the count is bounded).
        let arr: Box<[u8; ALLOC_CAP]> = Box::new(kani::any());
        Box::into_raw(arr) as *mut core::ffi::c_void
    }

    pub fn step(&mut self, id: u64, args: [u128; 3], kinds: [u8; 3]) -> u128 {
        if self.recording {
            assert!(self.len < TRACE_CAP, "trace exceeds TRACE_CAP");
            let ret: u128 = kani::any();
            self.calls[self.len] = Call { id, args, kinds, ret };
            self.len += 1;
            ret
        } else {
            assert!(self.cursor < self.len, "second version makes more external calls");
            let c = self.calls[self.cursor];
            assert!(c.id == id, "external call sequence differs");
            let mut i = 0;
            while i < 3 {
                let (a, b) = (c.args[i], args[i]);
                let ok = match kinds[i] {
                    // Scalar/float: equal by value.
                    0 => a == b,
                    // NUL-terminated string: equal by content (first version's
                    // buffer is still live during replay).
                    1 => unsafe {
                        same_cstr(
                            a as usize as *const core::ffi::c_char,
                            b as usize as *const core::ffi::c_char,
                        )
                    },
                    // Pointer: equal iff it corresponds in the heap bijection.
                    2 => self.link(a, b),
                    // Unused argument slot.
                    _ => true,
                };
                assert!(ok, "external call arguments differ");
                i += 1;
            }
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

/// A union built as symbolic raw bytes -- every bit pattern, over-approximating
/// all variants at once, so no discriminant is needed. Sound for differential
/// equivalence: both versions get byte-identical unions (see `clone_union`), so
/// reading any scalar variant agrees across them; reading a *pointer* variant
/// and dereferencing it hits an arbitrary address, which Kani reports as an
/// invalid access ("not proved"), never a false proof.
pub unsafe fn gen_union<T: Copy>() -> T {
    let mut u: T = core::mem::zeroed();
    let p = &mut u as *mut T as *mut u8;
    for i in 0..core::mem::size_of::<T>() {
        *p.add(i) = kani::any();
    }
    u
}

/// A byte copy of a union from the old layout `A` into the new layout `B`. Both
/// are the same `#[repr(C)]` union from the two crates, so their size and layout
/// match; copying the bytes gives the new version the identical union value.
pub unsafe fn clone_union<A: Copy, B: Copy>(src: *const A) -> B {
    let mut dst: B = core::mem::zeroed();
    core::ptr::copy_nonoverlapping(
        src as *const u8,
        &mut dst as *mut B as *mut u8,
        core::mem::size_of::<B>().min(core::mem::size_of::<A>()),
    );
    dst
}

/// Whether two unions hold identical bytes (same `#[repr(C)]` layout in both
/// crates). Compares the post-state, catching a divergent write to the union.
pub unsafe fn same_union<A: Copy, B: Copy>(a: *const A, b: *const B) -> bool {
    if core::mem::size_of::<A>() != core::mem::size_of::<B>() {
        return false;
    }
    let pa = a as *const u8;
    let pb = b as *const u8;
    for i in 0..core::mem::size_of::<A>() {
        if *pa.add(i) != *pb.add(i) {
            return false;
        }
    }
    true
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
