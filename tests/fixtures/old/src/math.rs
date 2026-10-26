pub fn larger(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

pub fn half(x: i32) -> i32 {
    x / 2
}

pub unsafe fn read(p: *const i32) -> i32 {
    *p
}
