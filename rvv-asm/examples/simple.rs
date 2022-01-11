#![feature(asm)]
#![feature(asm_const)]

use rvv_asm::rvv_asm;

fn main() {
    let a: u64 = 3;
    let b: u64 = 4;
    let lo: u64;
    let hi: u64;

    unsafe {
        rvv_asm!(
            "vsetvl x5, s3, t6",
            "mov {a}, 3",
            "vle256.v v3, (a0), vm",
            "1:",
            "mov {hi}, 4",
            "vse64.v v3, (a0)",
            a = in(reg) a,
            hi = out(reg) hi,
        );
    }
}
