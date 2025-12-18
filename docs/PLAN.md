# PLAN — Next-gen modular Moonshine proof (Lean4), built on UFRF Core

This plan assumes two inputs:

1) **The updated UFRF v0.5.2 formalization conventions**
   - 13 manifest positions (1..13) remain canonical
   - an optional 14-state seam chart (0..13) is used for recursion / boundary bookkeeping
   - contextual gates (e.g. mod 12, mod 26) are testable selection rules at REST crossings

2) **Lessons from the earlier Lean repos**
   - `UFRF-MonsterMoonshinev1`: good 3-layer architecture (Params → Monster mapping → q-series)
   - `UFRF-Lean-Validation`: good “single import” summary goal, but better as an aggregator package

The goal is to build a Moonshine development that is **modular**, **auditable**, and **reusable** by other UFRF projects.

---

## Milestone 0 — Freeze conventions and repo scaffold

**Deliverables**
- [ ] Decide package split:
  - `ufrf-core` (shared)
  - `ufrf-moonshine` (domain)
  - optional `ufrf-validation` (aggregator)
- [ ] Enforce project hygiene:
  - `./scripts/verify.sh` fails if any `sorry` exists
  - CI builds with pinned `lean-toolchain` + pinned Mathlib commit
- [ ] Add doc guardrails:
  - “charts vs claims”
  - “mod 13 vs mod 14”
  - “gates are hypotheses”

**Why this matters**
Your docs explicitly distinguish “positions vs states” and introduce seam + gate formalization. Those distinctions must be *baked into the codebase first*, otherwise Moonshine work drifts into untraceable residue-pattern arguments.

---

## Milestone 1 — UFRF Core: seam chart + overlap + context tags

**Lean files (core)**
- [x] `UFRF/SeamChart.lean` (already present)
- [x] `UFRF/ContextTags.lean` (added in this starter)

**Theorems to lock in**
- [ ] Bridge→Seed overlap lemma in a form you can reuse everywhere:
  - baseline birth rule (`birth g = 10*g`)
  - generalized theorem “if births are REST-anchored, overlap holds”

**Exit criteria**
- theorems compile with no additional axioms
- you can import these files from any downstream package without circular dependencies

---

## Milestone 2 — UFRF Core: moduli and chart utilities

**Lean files (core)**
- [x] `UFRF/ModuliLogs.lean`
  - `Lin(x)=x` replaces informal “log₁”
  - explicit `mod0 : n % 14 = 0` as VOID reset
- [x] `UFRF/ModuliCore.lean`
  - provable constraints for `p(n)=n(n+2)` in mod 3/4/13/14
- [x] `UFRF/RamanujanFunctional.lean`
  - validates the functional-equation core with minimal assumptions

**Exit criteria**
- moduli lemmas are purely algebraic and do not smuggle physics claims
- the “seam chart” integration is explicit (VOID is not silently conflated with 13)

---

## Milestone 3 — Moonshine Layer 1: Params and “no free parameters”

**Target (from MonsterMoonshinev1)**
- a `Params` layer that encodes the global UFRF geometry relevant to Moonshine and proves uniqueness (“no free params”).

**Files to create**
- `lean/UFRF/Moonshine/Params.lean`
  - `structure Params` (phi, cycleLen, REST index, etc.)
  - theorem `params_unique : …` (or: `Subsingleton Params` if appropriate)

**Design rule**
- Keep *charts* (moduli decompositions, seam bookkeeping) separate from *claims*.
- If you add contextual gates, they should be their own `structure Gate` with explicit hypotheses.

---

## Milestone 4 — Moonshine Layer 2: Monster primes → 196884

**Target theorems (from MonsterMoonshinev1)**
- `monster_dimension_emergence : 71 × 59 × 47 + 1 = 196884`
- `monster_primes_unique_minimal : …` (uniqueness under mod 13 constraints)

**Files to create**
- `lean/UFRF/Moonshine/Monster.lean`
  - define the “position → prime” constraint mechanism
  - prove uniqueness, not just the arithmetic identity

**Practical approach**
- Isolate *search/finite check* sublemmas behind decidable propositions.
  - You can prove “only these primes satisfy the constraints” using `fin_cases` / bounded search,
    but the constraints must be cleanly stated first.

---

## Milestone 5 — Moonshine Layer 3: q-series partition function and j = Z + 744

**Target theorems (from MonsterMoonshinev1)**
- `Z_T_invariant : Z(τ+1) = Z(τ)`
- `jCoeff_param_invariant : jCoeff(A,n) independent of Params choice`

**Two implementation routes**
1) **UFRF-derived route (recommended first):**
   - define `Z(τ)` as a q-series with coefficients from the Monster layer
   - define `j(τ) = Z(τ) + 744`
   - prove the invariance properties you need

2) **Classical modular-forms route (later):**
   - define `j = E4^3/Δ` using Mathlib modular forms
   - prove equivalence to the UFRF-derived q-series route

**Files to create**
- `lean/UFRF/Moonshine/ZPartition.lean`
- `lean/UFRF/Moonshine/JInvariant.lean`

---

## Milestone 6 — Replicability and McKay–Thompson interface

Once the base q-series/j pipeline is in place, you can move toward:
- Faber polynomials
- Hecke operators
- replicability equations
- abstract McKay–Thompson series structure

This can live either in:
- `lean/Moonshine/*` (classical) and/or
- `lean/UFRF/Moonshine/*` (UFRF-derived)

---

## Milestone 7 — Make it reusable: Euler / Navier–Stokes / RH / constants

After `ufrf-core` is stable, every new project should follow the same pattern:

1) import `UFRF.Core` (seam chart, context tags, gates)
2) define a domain-specific “state extractor” that maps the domain to a seam state
3) state the domain-specific theorems as:
   - chart-level lemmas (pure math)
   - gate hypotheses (explicit assumptions)
   - validation protocols (replicable tests)

