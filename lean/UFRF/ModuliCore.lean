import Mathlib

/-!
# UFRF Moduli Core

A Lean-first, minimal-assumption module capturing the *provable* modular patterns that
show up repeatedly in the UFRF Ramanujan/Vieta discussion.

Key idea: the polynomial

  p(n) = n (n+2) = (n+1)^2 - 1

When you view `p(n)` in different moduli (3,4,13,14,...) the *allowed residues* are
highly constrained (quadratic-residue structure). This gives you the "mod 3 / mod 4 / mod 13"
phase-space skeleton in a way Lean can validate.
-/

namespace UFRF

/-- The basic Ramanujan polynomial. -/
def p (n : ℕ) : ℕ := n * (n + 2)

/-- The same polynomial, interpreted in `ZMod m`. -/
def pZ (m : ℕ) (n : ℕ) : ZMod m := (n : ZMod m) * ((n + 2 : ℕ) : ZMod m)

/-- "mod0" / "VOID" in a modulus `m`: the residue is exactly 0. -/
def isVoid (m : ℕ) (n : ℕ) : Prop := pZ m n = 0

/-- A convenient algebraic identity: `n(n+2) = (n+1)^2 - 1` (in any commutative semiring). -/
theorem pZ_eq_sq_sub_one (m : ℕ) (n : ℕ) :
    pZ m n = ((n : ZMod m) + 1)^2 - 1 := by
  -- Expand and ring-normalize in `ZMod m`.
  --
  -- `ring` works because `ZMod m` is a commutative semiring.
  simp [pZ]
  ring

/-!
## Mod 3 phase space (Trinity)

In ZMod 3 the expression `a*(a+2)` can only be `0` or `2`.
Equivalently: it never hits residue `1`.
-/

theorem zmod3_mul_add_two_values (a : ZMod 3) :
    a * (a + 2) = 0 ∨ a * (a + 2) = 2 := by
  -- Finite proof: ZMod 3 has exactly 3 elements.
  fin_cases a <;> decide

theorem mod3_pattern (n : ℕ) :
    pZ 3 n = 0 ∨ pZ 3 n = 2 := by
  simpa [pZ] using zmod3_mul_add_two_values (a := (n : ZMod 3))

/-- Trinity embedding (values in {-1/2, 0, +1/2}) for a residue in `ZMod 3`.

We use: 0 ↦ 0, 1 ↦ +1/2, 2 (≡ -1) ↦ -1/2.
-/
def trinityHalf : ZMod 3 → ℚ
  | 0 => 0
  | 1 => (1/2 : ℚ)
  | _ => (-1/2 : ℚ)

/-- Under `pZ 3`, the +1/2 state never occurs: `pZ 3 n` is never 1. -/
theorem mod3_ne_one (n : ℕ) : pZ 3 n ≠ (1 : ZMod 3) := by
  -- From the value classification.
  rcases mod3_pattern n with h0 | h2
  · -- `pZ 3 n = 0`
    rw [h0]
    decide
  · -- `pZ 3 n = 2`
    rw [h2]
    decide

/-!
## Mod 4 phase space (Plane / parity)

In ZMod 4 the expression `a*(a+2)` can only be `0` or `3`.
Equivalently: it never hits residues `1` or `2`.
-/

theorem zmod4_mul_add_two_values (a : ZMod 4) :
    a * (a + 2) = 0 ∨ a * (a + 2) = 3 := by
  fin_cases a <;> decide

theorem mod4_pattern (n : ℕ) :
    pZ 4 n = 0 ∨ pZ 4 n = 3 := by
  simpa [pZ] using zmod4_mul_add_two_values (a := (n : ZMod 4))

/-!
## Mod 13 phase space (Cycle)

Because 13 is prime, `ZMod 13` is a field, so we can solve

  a*(a+2) = 0

exactly: a = 0 or a = -2.
-/

theorem zmod13_mul_add_two_eq_zero_iff (a : ZMod 13) :
    a * (a + 2) = 0 ↔ a = 0 ∨ a = (-2 : ZMod 13) := by
  constructor
  · intro h
    -- In ZMod 13 (a field), use field properties directly
    -- Factor: a * (a + 2) = 0 means a = 0 or (a + 2) = 0
    fin_cases a <;> simp at h <;> try { contradiction }
    · left; rfl  -- a = 0 works
    · right; rfl  -- a = 11 = -2 works: 11 + 2 = 13 = 0
  · rintro (rfl | rfl)
    · norm_num  -- 0 * 2 = 0
    · norm_num  -- 11 * 13 = 11 * 0 = 0

/-- Pulled back to naturals: `p(n)` is 0 mod 13 iff `n ≡ 0` or `n ≡ -2` (i.e. 11). -/
theorem mod13_zero_iff (n : ℕ) :
    pZ 13 n = 0 ↔ (n : ZMod 13) = 0 ∨ (n : ZMod 13) = (-2 : ZMod 13) := by
  simpa [pZ] using (zmod13_mul_add_two_eq_zero_iff (a := (n : ZMod 13)))

/-!
## Mod 14 seam chart (13 + VOID)

`ZMod 14` is not a field, but here the equation still has only two solutions.
This lemma is particularly useful if you want a *14-state seam chart* with a
single distinguished VOID state.
-/

theorem zmod14_mul_add_two_eq_zero_iff (a : ZMod 14) :
    a * (a + 2) = 0 ↔ a = 0 ∨ a = (12 : ZMod 14) := by
  -- Finite proof: ZMod 14 has 14 elements.
  -- Use decide for each case
  constructor
  · intro h
    fin_cases a <;> simp at h <;> try { contradiction }
    · left; rfl  -- a = 0 works
    · right; rfl  -- a = 12 works
  · intro h
    rcases h with (rfl | rfl) <;> decide

theorem mod14_zero_iff (n : ℕ) :
    pZ 14 n = 0 ↔ (n : ZMod 14) = 0 ∨ (n : ZMod 14) = (12 : ZMod 14) := by
  simpa [pZ] using (zmod14_mul_add_two_eq_zero_iff (a := (n : ZMod 14)))

/-!
## Log ladders (placeholders)

These are intentionally *minimal* wrappers, because analytic/log theorems quickly
pull in heavier assumptions (positivity, `x ≠ 1`, etc.).

Use these as naming hooks so the rest of the UFRF development can reference
"log1/log2/log3" without committing to extra structure too early.
-/

noncomputable def log1 (x : ℝ) : ℝ := Real.log x

noncomputable def log2 (x : ℝ) : ℝ := Real.log (Real.log x)

noncomputable def log3 (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

end UFRF
