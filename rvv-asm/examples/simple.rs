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

    // inline label
    unsafe {
        rvv_asm!(
            "vsetvl x5, s3, t6",
            "1: vle256.v v3, (a0), vm",
            "2: mov {lo}, 4",
            lo = out(reg) lo,
        );
    }

    // multiple line asm string literal
    unsafe {
        rvv_asm!(
            "vsetvl x5, s3, t6 \n mov {0}, 3",
            in(reg) a,
        );
    }
}
