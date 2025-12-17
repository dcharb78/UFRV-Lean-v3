# UFRF-Lean-v3

Modular Lean4 formalization of UFRF Core and Moonshine domain logic.

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

[Add your license here]
