import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq

/-!
# UFRF.Mod14

Workhorse lemmas for mod-14 normalization used throughout UFRF Core.

These lemmas handle the common pattern of simplifying expressions modulo 14,
particularly when dealing with the seam chart (14-state cycle).
-/

namespace UFRF

/-- A multiple of 14 modulo 14 is 0. -/
lemma mod14_mul (k : Nat) : (14 * k) % 14 = 0 := by
  simp [Nat.mul_mod]

/-- Adding a multiple of 14 doesn't change the remainder modulo 14. -/
lemma mod14_add_mul (a k : Nat) : (a + 14 * k) % 14 = a % 14 := by
  -- push mod through addition/multiplication; the 14*k part vanishes
  simp [Nat.add_mod, Nat.mul_mod]

/-- Adding a multiple of 14 (right-multiplied) doesn't change the remainder modulo 14. -/
lemma mod14_add_mul_right (a k : Nat) : (a + k * 14) % 14 = a % 14 := by
  simpa [Nat.mul_comm] using mod14_add_mul a k

end UFRF

