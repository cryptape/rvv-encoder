
## Example usage

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
