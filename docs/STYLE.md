# STYLE / ARCHITECTURE RULES (UFRF × Moonshine Lean)

This file encodes the project rules we follow to keep the development **modular, testable,
and honest about assumptions**.

## 1) Layer separation

We maintain three layers:

1. **Bookkeeping layer (Lean, provable):** finite charts, moduli lemmas, indexing, seams.
   - Example: `UFRF/SeamChart.lean`, `UFRF/ModuliCore.lean`.

2. **Mathematical infrastructure (Lean, classical):** modular forms, q-series, complex analysis,
   group actions, Hecke operators.

3. **Interpretation / UFRF lens (Docs, optional):** mapping math objects to UFRF narrative.
   - This must never be required to compile the Lean proof.

## 2) “Lean-first minimal assumptions” principle

Start with what Lean can validate *without* heavy analytic machinery:

- Prefer algebraic identities over limits.
- Prefer finite-case proofs (e.g. `fin_cases` on `ZMod m`) for small moduli.
- Keep definitions total; avoid partial constructs (e.g. base-1 logarithm). Use `Lin(x)=x`.

## 3) Chart vs claim guardrail

Every new modulus/base must be tagged as either:

- **Chart (representation choice)** or
- **Gate (testable selection rule)**.

No “new modulus” should silently drift into the axioms.

## 4) Namespaces and file boundaries

- Put UFRF bookkeeping in namespace `UFRF`.
- Put Moonshine formalization in namespace `Moonshine`.
- Avoid cross-imports from Moonshine → UFRF unless the dependency is purely formal (e.g. `Fin 14` helper).

## 5) Module boundaries: avoid “mega files”

Each file should have:

- clear *public API* (definitions and theorems intended to be imported),
- internal lemmas local to that file, and
- a short “TODO / NEXT” section.

