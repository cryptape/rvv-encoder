
# RVV encoder
* `rvv-encode` - A Library to encode RISC-V V extension instruction
* `rvv-asm` - A procedure macro to encode RISC-V V extension instructions
* `rvv-as` - A command line tool to encode RISC-V V extension instructions


## `rvv-asm` example
```rust
unsafe {
    rvv_asm::rvv_asm!(
        "vsetvl x5, s3, t6",
        "1: vle256.v v3, (a0), vm",
        "2:",
        "li {lo}, 4",
        lo = out(reg) lo,
    );
}
```

## `rvv-as` usage
```
USAGE:
    rvv-as [OPTIONS] <ASM_FILE>

ARGS:
    <ASM_FILE>    The original assembly source file path

OPTIONS:
    -c, --comment-origin                     Use original instruction and its code as comment
    -p, --comment-prefix <COMMENT_PREFIX>    The comment prefix [default: #]
    -r, --reserved-only                      Only translate reserved rvv instructions
```
