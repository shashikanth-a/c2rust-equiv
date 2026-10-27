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
