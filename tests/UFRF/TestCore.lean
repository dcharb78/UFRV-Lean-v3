/-!
# UFRF Core Validation Tests

This file validates that UFRF Core compiles and key theorems work correctly.
It serves as both a test suite and a usage example.

## Test Categories

1. **Seam Chart**: 13/14 state conversions and transitions
2. **Context Tags**: Birth functions and overlap lemmas
3. **Moduli Patterns**: Residue constraints and phase spaces
4. **Chart Helpers**: Lin, logB, mod0 functions
5. **Ramanujan Functional**: Functional equation validation
-/

import UFRF.Core

namespace UFRF.Test

/-!
## Seam Chart Tests
-/

/-- Test: VOID projects to nothing. -/
example : seamToManifest VOID = none := by
  exact seamToManifest_VOID

/-- Test: Manifest positions embed correctly. -/
example (m : Manifest13) : seamToManifest (manifestToSeam m) = some m := by
  exact seamToManifest_manifestToSeam m

/-- Test: REST state is at index 10. -/
example : REST = ⟨10, by decide⟩ := by
  rfl

/-- Test: VOID state is at index 0. -/
example : VOID = ⟨0, by decide⟩ := by
  rfl

/-- Test: Next seam wraps 13 → 0. -/
example : nextSeam (⟨13, by decide⟩ : Seam14) = VOID := by
  exact nextSeam_13

/-!
## Context Tags Tests
-/

/-- Test: Birth function is REST-anchored. -/
example (g : Nat) : birth g = 10 * g := by
  rfl

/-- Test: At birth time, seam state is VOID. -/
example (g : Nat) : seamState g (birth g) = VOID := by
  exact seamState_at_birth g

/-- Test: Bridge→Seed overlap lemma (baseline). -/
example (g : Nat) :
    seamState g (birth (g+1)) = REST ∧ seamState (g+1) (birth (g+1)) = VOID := by
  exact overlap_baseline_rest_void g

/-- Test: REST crossing gives REST state. -/
example (g k : Nat) :
    seamState g (restCrossing (birth g) k) = REST := by
  exact seamState_at_restCrossing g k

/-!
## Moduli Pattern Tests
-/

/-- Test: Mod 3 pattern (Trinity). -/
example (n : Nat) : pZ 3 n = 0 ∨ pZ 3 n = 2 := by
  exact mod3_pattern n

/-- Test: Mod 3 never hits residue 1. -/
example (n : Nat) : pZ 3 n ≠ (1 : ZMod 3) := by
  exact mod3_ne_one n

/-- Test: Mod 4 pattern (Quaternion). -/
example (n : Nat) : pZ 4 n = 0 ∨ pZ 4 n = 3 := by
  exact mod4_pattern n

/-- Test: Mod 13 zero condition. -/
example (n : Nat) :
    pZ 13 n = 0 ↔ (n : ZMod 13) = 0 ∨ (n : ZMod 13) = (-2 : ZMod 13) := by
  exact mod13_zero_iff n

/-- Test: Mod 14 zero condition (seam chart). -/
example (n : Nat) :
    pZ 14 n = 0 ↔ (n : ZMod 14) = 0 ∨ (n : ZMod 14) = (12 : ZMod 14) := by
  exact mod14_zero_iff n

/-- Test: Polynomial identity. -/
example (m n : Nat) :
    pZ m n = ((n : ZMod m) + 1)^2 - 1 := by
  exact pZ_eq_sq_sub_one m n

/-!
## Chart Helper Tests
-/

/-- Test: Lin is identity. -/
example (x : ℝ) : Lin x = x := by
  rfl

/-- Test: mod0 iff divisible by 14. -/
example (n : Nat) : mod0 n ↔ 14 ∣ n := by
  exact mod0_iff n

/-!
## Ramanujan Functional Tests
-/

/-- Test: Functional equation holds. -/
example (n : ℕ) : (ramF n)^2 = 1 + (n : ℝ) * ramF (n + 1) := by
  exact ramF_sq n

/-- Test: Square root form. -/
example (n : ℕ) : ramF n = Real.sqrt (1 + (n : ℝ) * ramF (n + 1)) := by
  exact ramF_sqrt n

/-- Test: Headline value. -/
example : ramF 1 = (2 : ℝ) := by
  exact ramF_one

/-- Test: Polynomial identity. -/
example (n : ℕ) :
    (1 : ℝ) + (n : ℝ) * ((n : ℝ) + 2) = ((n : ℝ) + 1)^2 := by
  exact one_add_mul_mul_add_two_eq_sq n

/-!
## Integration Tests
-/

/-- Test: Seam chart and moduli integration.
    At VOID (mod 14 = 0), we should also have mod0. -/
example (n : Nat) (h : (n : ZMod 14) = 0) : mod0 n := by
  -- n ≡ 0 (mod 14) implies 14 ∣ n
  have h14 : 14 ∣ n := by
    -- Use ZMod characterization: (n : ZMod 14) = 0 ↔ 14 ∣ n
    -- This is a standard Mathlib lemma
    exact ZMod.natCast_zmod_eq_zero_iff_dvd.mp h
  -- Now mod0 follows from mod0_iff
  rw [mod0_iff]
  exact h14

/-- Test: Context tag at REST crossing.
    At REST crossing, seam state should be REST. -/
example (g k : Nat) :
    let t := restCrossing (birth g) k
    seamState g t = REST := by
  intro t
  -- This is exactly the REST crossing lemma
  exact seamState_at_restCrossing g k

end UFRF.Test

