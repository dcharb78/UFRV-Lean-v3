import Mathlib

/-!
# UFRF Ramanujan Functional Equation (Lean Core)

This file focuses on what is easiest to validate in Lean with **minimum extra assumptions**:

* The Ramanujan nested radical can be encoded via a functional equation

    F(n)^2 = 1 + n * F(n+1)

  and the **exact** candidate solution is

    F(n) = n + 1.

* From this, the headline value follows immediately:

    F(1) = 2.

No limits, no floating approximations, no convergence arguments.

This is the cleanest "Lean-validated minimum-assumption" bridge between the
recursive expression and the exact closed form.
-/

namespace UFRF

/-- Candidate closed-form solution to the Ramanujan functional equation. -/
def ramF (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The polynomial identity behind the recursion: `1 + n (n+2) = (n+1)^2` (in ℝ). -/
theorem one_add_mul_mul_add_two_eq_sq (n : ℕ) :
    (1 : ℝ) + (n : ℝ) * ((n : ℝ) + 2) = ((n : ℝ) + 1)^2 := by
  -- `ring` handles this.
  ring

/-- The Ramanujan functional equation is satisfied *exactly* by `ramF`. -/
theorem ramF_sq (n : ℕ) :
    (ramF n)^2 = 1 + (n : ℝ) * ramF (n + 1) := by
  -- Expand the definition and use the polynomial identity.
  simp [ramF]
  -- After simp, goal is purely algebraic.
  ring

/-- Equivalent square-root form: `ramF n = sqrt (1 + n * ramF (n+1))`.

This matches the "nested radical" recurrence directly.
-/
theorem ramF_sqrt (n : ℕ) :
    ramF n = Real.sqrt (1 + (n : ℝ) * ramF (n + 1)) := by
  -- Rewrite the inside as a square, then use `sqrt_sq_eq_abs`.
  have hsq : (1 + (n : ℝ) * ramF (n + 1)) = (ramF n)^2 := by
    -- rearrange `ramF_sq`
    simpa [ramF] using (ramF_sq n).symm
  -- Now reduce to `sqrt ((ramF n)^2) = ramF n`.
  -- `sqrt_sq_eq_abs` gives `|ramF n|`.
  have hn : 0 ≤ ramF n := by
    -- `ramF n = n + 1` is nonnegative.
    simp [ramF]
    -- n + 1 ≥ 1 > 0, so (n : ℝ) + 1 > 0
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  -- Finish
  calc
    ramF n = |ramF n| := by simpa [abs_of_nonneg hn]
    _ = Real.sqrt ((ramF n)^2) := by simpa [Real.sqrt_sq_eq_abs]
    _ = Real.sqrt (1 + (n : ℝ) * ramF (n + 1)) := by simpa [hsq]

/-- The headline value: the infinite radical's value at the "start" is 2. -/
theorem ramF_one : ramF 1 = (2 : ℝ) := by
  simp [ramF]
  norm_num

/-- Convenience: `ramF 1` in the square-root form is also 2. -/
theorem ramF_one_sqrt :
    Real.sqrt (1 + (1 : ℝ) * ramF (1 + 1)) = (2 : ℝ) := by
  -- Use the general lemma at `n=1` and then the closed form.
  calc
    Real.sqrt (1 + (1 : ℝ) * ramF (1 + 1)) = ramF 1 := by
      simpa using (ramF_sqrt 1).symm
    _ = (2 : ℝ) := ramF_one

/-!
## Half-step / flip-point angle chart (minimal)

If you want to represent the special half-step `6.5 = 13/2` *without rationals*,
a clean Lean trick is to work in **26 half-steps** per full cycle.

Then `k = 13` is exactly the half-turn, and the angle is exactly `π`.
-/

/-- Angle for a half-step index `k` when 26 half-steps correspond to a full turn. -/
noncomputable def θ26 (k : ℕ) : ℝ := (2 * Real.pi) * (k : ℝ) / 26

/-- The flip point: half-turn corresponds to `k = 13`, giving exactly `π`. -/
theorem θ26_flip : θ26 13 = Real.pi := by
  -- Multiply both sides by 26 to clear denominators.
  unfold θ26
  have h26 : (26 : ℝ) ≠ 0 := by norm_num
  field_simp [h26]
  -- Now it's purely integer arithmetic with a common `Real.pi` factor.
  ring

end UFRF
