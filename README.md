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

## Current Status

**UFRF Core Status:**
- ✅ Mod14 helper module: Stable with reusable mod-14 lemmas
- ✅ SeamChart: 13 manifest positions + 14-state seam chart (VOID=0, REST=10)
- ✅ ContextTags: Proofs use explicit step-by-step rewrites for geometric transparency
- ✅ ModuliCore, ModuliLogs, RamanujanFunctional, Projection: All building

**Proof Strategy:**
- Uses `simp only` with specific lemmas to preserve geometric structure
- Manual `rw` chains for explicit cancellation (e.g., `Nat.add_sub_cancel_left`)
- `norm_num` for final numeric goals (e.g., `10 % 14 = 10` for REST)
- Avoids broad `simp` that collapses expressions prematurely

**Next Steps:**
- Add projection composition (Axiom 2) for observer-relative scales
- Extend to MetaMerge14 hypothesis (sum mod 14 = 0 for VOID events)
- Formalize infinite pattern validators

## License

This project is released into the public domain under [CC0 1.0 Universal](LICENSE).
