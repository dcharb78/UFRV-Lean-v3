# UFRF-Lean-v3

Modular Lean4 formalization of UFRF Core and Moonshine domain logic.

![Tracking](https://muddy-frog-30d2.daniel-208.workers.dev/test.png)

## Structure

- **UFRF Core** (`lean/UFRF/`) - Shared bookkeeping, charts, seam/REST conventions, context tags, moduli lemmas
- **Moonshine** (`lean/Moonshine/`) - Domain-specific modular forms, j-invariant, McKay-Thompson series

## Quick Start

```bash
# Install dependencies
lake update

# Build
lake build

# Verify (check for sorry statements)
./scripts/verify.sh
```

## Requirements

- Lean 4 (see `lean-toolchain`)
- Mathlib (managed via Lake)

## License

This project is released into the public domain under [CC0 1.0 Universal](LICENSE).
