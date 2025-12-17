import Mathlib

namespace UFRF

/-- "VOID reset" predicate for the seam chart: `n ≡ 0 (mod 14)`.

This is what we mean by "mod0" in prose: it marks a *reset to VOID*.
(It is **not** "Nat mod 0" which is undefined.)
-/
def mod0 (n : Nat) : Prop := n % 14 = 0

/-- Trinity residue chart (mod 3). -/
abbrev Mod3 := Fin 3

def mod3 (n : Nat) : Mod3 :=
  ⟨n % 3, Nat.mod_lt _ (by decide)⟩

/-- Quaternion residue chart (mod 4). -/
abbrev Mod4 := Fin 4

def mod4 (n : Nat) : Mod4 :=
  ⟨n % 4, Nat.mod_lt _ (by decide)⟩

/-- Linear chart used in the docs in place of the old informal `log₁` notation.

(Real logarithm base 1 is undefined; using `Lin` keeps the chart family total.)
-/
def Lin (x : ℝ) : ℝ := x

/-- Logarithm chart with arbitrary base `b` (change-of-base).

You normally use this only under side-conditions like `0 < b`, `b ≠ 1`, and `0 < x`.
We keep it definition-only here to minimize assumptions.
-/
noncomputable def logB (b x : ℝ) : ℝ := Real.log x / Real.log b

noncomputable abbrev log2 (x : ℝ) : ℝ := logB 2 x
noncomputable abbrev log3 (x : ℝ) : ℝ := logB 3 x

/-- A tiny lemma you can use as a smoketest: VOID resets happen exactly at multiples of 14. -/
theorem mod0_iff (n : Nat) : mod0 n ↔ 14 ∣ n := by
  -- `Nat.dvd_iff_mod_eq_zero` is in Mathlib
  simp [mod0]
  rw [← Nat.dvd_iff_mod_eq_zero]

end UFRF
