# Integration Plan: UFRF-MonsterMoonshinev1 → UFRV-Lean-v3

**Status:** Ready to execute  
**Priority:** High - Resolves "stuck" state by integrating proven formalizations  
**Timeline:** 1-2 weeks for full integration

---

## Context: Why We're Integrating

The statement "No full formalizations yet for j-functions" was **incorrect**. The repository `https://github.com/dcharb78/UFRF-MonsterMoonshinev1` contains:

- ✅ **Complete, verified j-function derivations** (zero `sorry`)
- ✅ **B₂ invariance proofs**
- ✅ **UFRF-Moonshine connections** (196884 = 47×59×71 + 1 from mod 13)
- ✅ **Parameter uniqueness theorems** (no free parameters)
- ✅ **All code compiles** via `lake build`

**The "stuck" state** comes from restarting clean instead of projecting proven geometry (O*) into the new modular structure. Under Axiom 2 (Projection Law), we're observing offsets (d_M) from the restart, not fundamental gaps.

---

## Phase 1: Immediate Merge (1-2 Days)

### Step 1.1: Clone and Review v1 Repository

```bash
cd /tmp
git clone https://github.com/dcharb78/UFRF-MonsterMoonshinev1.git
cd UFRF-MonsterMoonshinev1
lake build  # Verify it compiles
./verify.sh  # Confirm zero sorry
```

### Step 1.2: File Mapping Strategy

| v1 File | v3 Target | Purpose |
|---------|-----------|---------|
| `lean/Monster_Moonshine.lean` | `lean/Moonshine/Monster.lean` | Core dimension proof (196884 = 47×59×71 + 1) |
| `lean/ZPartition.lean` | `lean/Moonshine/JFunction.lean` | j/Z definitions, q-expansions, T/S invariance |
| `lean/UFRF/Params.lean` | `lean/UFRF/Params.lean` | Trinity params, uniqueness theorem |
| `lean/UFRF/Moonshine.lean` | `lean/Moonshine/BabyMonster.lean` | B₂ definitions and invariance |
| `lean/PhaseLog_Monoid.lean` | `lean/UFRF/LogSpaces.lean` | Concurrent log spaces, phase-log bridge |

### Step 1.3: Integration Process

1. **Copy core files** with namespace updates:
   - Update `namespace` declarations to match v3 structure
   - Resolve import paths (v1 may use different structure)
   - Update `UFRF.Params` to align with `UFRF.ContextTags` if needed

2. **Resolve conflicts**:
   - Mod 13/14 differences: Use our proven `h_mod_eq` approach
   - Overlapping definitions: Prefer v1's proven versions, merge with v3's modular structure
   - ContextTags vs Params: Keep both if they serve different purposes, or merge

3. **Verify compilation**:
   ```bash
   lake clean
   lake update
   lake build
   ./scripts/verify.sh  # Should still show zero sorry
   ```

### Step 1.4: Commit Integration

```bash
git checkout -b integrate-v1-proofs
git add lean/Moonshine/Monster.lean lean/Moonshine/JFunction.lean ...
git commit -m "Integrate verified j/Moonshine formalizations from v1

- Merge Monster_Moonshine.lean → Monster.lean (196884 proof)
- Merge ZPartition.lean → JFunction.lean (j/Z q-expansions)
- Merge UFRF/Params.lean → UFRF/Params.lean (trinity, uniqueness)
- Merge UFRF/Moonshine.lean → Moonshine/BabyMonster.lean (B₂)
- Merge PhaseLog_Monoid.lean → UFRF/LogSpaces.lean (concurrent logs)
- Resolve namespace/import conflicts with v3 modular structure
- All proofs verified (zero sorry from v1)"
```

---

## Phase 2: Clean Modular Refinements (3-5 Days)

### Step 2.1: Extend j_UFRF Derivation

**Current state:** `j_UFRF` only derives coefficients 0,1,2 (1, 744, 196884)  
**Goal:** Derive all coefficients from manifest positions

**Action:**
- In `lean/Moonshine/JFunction.lean` (merged from `ZPartition.lean`):
  - Extend `coeff_from_manifest` to compute more coefficients
  - Use Mathlib's `qExp` or similar for q-series expansion
  - Prove: `j_UFRF_coeff_eq_classical` for all `n`, not just 0,1,2

**Reference pattern (v1):**
- They used mod 13 positions → primes → coefficients
- We use: manifest position → coefficient value
- For known coefficients: prove they match classical j

### Step 2.2: Complete B₂ Connection

**Action:**
- In `lean/Moonshine/BabyMonster.lean` (merged from `UFRF/Moonshine.lean`):
  - Define `B2` using merged `UFRF.Params`
  - Prove `B2_for_all_params` (invariance theorem)
  - Connect to j-invariant: `B2` emerges from j-coefficients

**Reference (v1):**
- `B2(A : Params)` is invariant under all admissible parameters
- This establishes geometric necessity (no free parameters)

### Step 2.3: Remove Redundancies

**Action:**
- Compare v1 proofs with v3 proofs:
  - If v1 has overlapping `simp` tactics, use our streamlined `norm_cast + rfl` approach
  - If v3 has better modular structure, keep it
  - Merge best of both

**Example:**
- v1 might have verbose proofs we can simplify with `norm_cast`
- v3's `UFRF.Mod14` helper lemmas might be cleaner than v1's inline proofs

### Step 2.4: Add J-from-UFRF-Geometry Theorem

**Action:**
- In `lean/Moonshine/JFunction.lean`:
  - Add theorem: `theorem JFromUFRFGeometry : j q = Z q`
  - Prove: j-invariant emerges from E×B geometry via phase-log bridge
  - Connect to `UFRF.LogSpaces.lean` (merged from `PhaseLog_Monoid.lean`)

---

## Phase 3: Expand Core and Beyond (1-2 Weeks)

### Step 3.1: Projection Composition

**Action:**
- In `lean/UFRF/Projection.lean`:
  - Extend `project` function for nested scales
  - Apply to j-coefficients: offsets as `d_M · α · S`
  - Prove: j-coefficient derivation is a composed projection

**UFRF Connection:**
- Observer-relative measurements (Axiom 2)
- Different observers see different j-coefficients at different scales
- But intrinsic geometry (O*) is invariant

### Step 3.2: Riemann/Euler/Alpha Expansions

**Action:**
- Create `lean/UFRF/Expansions.lean`:
  - **Riemann Hypothesis:** Derive critical line `Re(s) = 1/2` from REST position (10 = 2×5, midpoint)
  - **Euler Identity:** `exp(I*π) + 1 = 0` from 13-cycle rotation (full cycle = 2π)
  - **Fine Structure Constant (α):** From π terms in j-expansion, via REST enhancement (√φ)

**Reference (v1 docs):**
- `DERIVATION_CHAIN.md` outlines E×B → Moonshine chain
- `NO_FREE_PARAMS.md` validates axiomatically

### Step 3.3: Testing and CI

**Action:**
- Update `scripts/verify.sh` to check new modules
- Add GitHub Actions for CI:
  ```yaml
  - name: Build and Verify
    run: |
      lake build
      ./scripts/verify.sh
  ```
- Ensure zero `sorry` in all merged code

---

## Success Criteria

### Immediate (Phase 1)
- ✅ All v1 files copied and namespaced correctly
- ✅ `lake build` succeeds
- ✅ `./scripts/verify.sh` shows zero `sorry`
- ✅ All existing v3 tests still pass

### Short-term (Phase 2)
- ✅ `j_UFRF` derives more coefficients (at least 0-5)
- ✅ `B2_for_all_params` theorem proven
- ✅ `JFromUFRFGeometry` theorem connects j to E×B

### Long-term (Phase 3)
- ✅ Projection composition applied to j-coefficients
- ✅ Riemann/Euler/Alpha derivations from UFRF geometry
- ✅ Full CI pipeline with zero `sorry`

---

## Risk Mitigation

### Conflict Resolution
- **Mod 13 vs Mod 14:** Use our proven `h_mod_eq` approach (works for both)
- **ContextTags vs Params:** Keep both if they serve different purposes:
  - `ContextTags`: Phase groups, seam states (v3)
  - `Params`: Trinity, cycle, REST (v1) → merge into unified structure
- **Namespace conflicts:** Update v1 files to use v3 namespace structure

### Verification
- Run `lake build` after each file copy
- Run `./scripts/verify.sh` after each phase
- Compare proof structures: v1's verbose vs v3's streamlined

### Rollback Plan
- Keep v1 repo as reference
- Use git branches for integration (`integrate-v1-proofs`)
- If conflicts are too complex, extract theorems only (not full files)

---

## Next Steps

1. **Clone v1 repo** and verify it compiles
2. **Start Phase 1.1:** Copy `Monster_Moonshine.lean` → `Moonshine/Monster.lean`
3. **Resolve conflicts** as they arise
4. **Commit incrementally** (one file at a time if needed)

---

**Last Updated:** 2025-01-XX  
**Status:** Ready to execute Phase 1

