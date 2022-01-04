#![feature(asm)]

use rvv_encoder::rvv_asm;

fn main() {
    unsafe {
        rvv_asm!("xx");
    }
}
