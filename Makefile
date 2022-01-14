
test:
	cd rvv-encode && cargo test
	cd rvv-asm && cargo test --tests
	cd rvv-as && cargo test

clippy:
	cargo clippy --all

fmt:
	cargo fmt --all -- --check
