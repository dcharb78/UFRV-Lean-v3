# ARCHITECTURE — UFRF Core as a shared Lean library + modular project packages

This starter is designed around a single guiding idea:

> **UFRF Core is a shared “bookkeeping + axioms” library.**
> Each research track (Moonshine, Euler, Navier–Stokes, RH, constants, …) is a *separate module/package*
> that imports UFRF Core and then adds domain-specific structures and theorems.

## Why a layered architecture

The `UFRF-MonsterMoonshinev1` repo already demonstrated a clean 3-layer organization:

1. **Geometry / Axioms** (global parameters, no-free-params uniqueness)
2. **Moonshine mapping** (Monster primes → coefficients; parametric invariance)
3. **Analytic / q-series** (partition function, j = Z + 744, modular T-invariance)

The updated UFRF v0.5.2 docs add a *critical formalization upgrade*:

- Distinguish **13 manifest positions** from a **14-state seam chart** for recursion bookkeeping.
- Treat extra moduli (12, 26, …) as **context gates** / testable selection rules, not as new fundamentals.

So the modern architecture becomes:

## Package split

### Package A: `ufrf-core`

Lean namespace: `UFRF.*`

Purpose: definitions and lemmas that are reused everywhere.

Core deliverables:
- `UFRF.SeamChart` — 13 positions + 14-state seam chart
- `UFRF.ContextTags` — (SL, g, s) context tags + overlap lemma
- `UFRF.ModuliCore` — provable residue constraints (e.g., mod 3/4/13/14 patterns)
- `UFRF.ModuliLogs` — chart helpers (Lin, logB, mod0)
- `UFRF.RamanujanFunctional` — recursion → closed form, minimal assumptions

### Package B: `ufrf-moonshine`

Lean namespaces:
- `UFRF.Moonshine.*` for the UFRF-derived path
- `Moonshine.*` for classical modular-form infrastructure (if you choose to build it)

Purpose: the Moonshine-specific proof stack.

Suggested layering:
- `UFRF.Moonshine.Params` — global parameters and “no free parameters” theorem
- `UFRF.Moonshine.Monster` — prime/position constraints and 196884 emergence
- `UFRF.Moonshine.ZPartition` — q-series partition function Z(τ)
- `UFRF.Moonshine.JInvariant` — j = Z + 744; coefficient statements; modular invariance

### Package C: `ufrf-validation`

Lean namespace: `UFRF.Validation.*`

Purpose: cross-domain aggregator theorems and “single import” summaries.
This is where the old “unified proofs” style belongs (e.g. combine Moonshine + constants + RH),
but without forcing all domains to live in one codebase.

## Principle: charts vs claims

UFRF’s “moduli” should be expressed as either:
- **charts** (representation choice), or
- **contextual gates** (testable selection rules at REST crossings).

That keeps the Lean development honest:
- theorems about charts are *pure math*
- hypotheses about gates are *explicit assumptions* with downstream test protocols
