# verus-cad

## Install

### 1. Build Verus from source

```bash
cd verus/source
./tools/get-z3.sh
source ../tools/activate
vargo build --release
cd ../..
```

If you don't have the required Rust toolchain, `activate` will tell you. Run `rustup toolchain install` to install it, then re-run `source ../tools/activate`.

See [verus/BUILD.md](verus/BUILD.md) for more details (Windows instructions, IDE support, etc.).

### 2. Verify individual repos

Once Verus is built, you can run `./scripts/check.sh` in any repo to verify it:

```bash
cd verus-bigint && ./scripts/check.sh
cd verus-rational && ./scripts/check.sh
cd verus-algebra && ./scripts/check.sh
cd verus-geometry && ./scripts/check.sh
cd verus-linalg && ./scripts/check.sh
cd verus-interval-arithmetic && ./scripts/check.sh
cd verus-topology && ./scripts/check.sh
```
