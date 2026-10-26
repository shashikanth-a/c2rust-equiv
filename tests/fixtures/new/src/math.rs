pub fn larger(a: i32, b: i32) -> i32 {
    a.max(b)
}

pub fn half(x: i32) -> i32 {
    x >> 1
}

pub unsafe fn read(p: *const i32) -> i32 {
    p.read()
}
