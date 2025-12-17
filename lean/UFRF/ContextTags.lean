import Mathlib
import UFRF.SeamChart
import UFRF.Mod14

/-!
# UFRF.ContextTags

Lean-first bookkeeping for *context tags* (scale level, phase-group index, seam state).

This mirrors the v0.5.2 docs' recommendation:
- keep **13 manifest positions** (1..13) for within-cycle navigation,
- use an explicit **14-state seam chart** (0..13) when cycle boundaries / recursion matter.

The key formal statement we want in Lean is the **Bridge→Seed overlap lemma**:
under REST-anchored births, parent COMPLETE (11..13) overlaps child SEED (1..3) concurrently.

(See UFRF Core Theory §4.4 and Mathematical Framework §10.8 in the docs pack.)
-/

namespace UFRF

/-- Scale-level index `SL` used in `M = 144 × 10^SL`.
We model it as an integer because scales can be above or below the reference.
-/
abbrev ScaleLevel := Int

/-- Phase-group/context index. -/
abbrev PhaseGroup := Nat

/-- A full bookkeeping tag (scale + phase group + seam state). -/
structure ContextTag where
  SL : ScaleLevel
  g  : PhaseGroup
  s  : Seam14

/-- Baseline (ungated) REST-anchored births:

`birth(g) = 10*g`.

This is a **convention** for formalization/testing. If you later introduce contextual gates,
replace this with a gated birth function and re-prove the overlap lemmas from the gated rule.
-/
def birth (g : PhaseGroup) : Nat := 10 * g

/-- Seam state of a phase group `g` at global time `t`.

We use a total definition on `Nat` via truncated subtraction.
If you want the strictly-correct domain restriction `t ≥ birth g`, change this to an `Option`.
-/
def seamState (g t : Nat) : Seam14 :=
  ⟨(t - birth g) % 14, Nat.mod_lt _ (by decide : 0 < 14)⟩

/-- At a phase group's own birth time, it is at VOID (state 0). -/
lemma seamState_at_birth (g : Nat) : seamState g (birth g) = VOID := by
  ext
  simp [seamState, birth, VOID]

/-- REST crossing times for a phase group born at time `b`.

Matches Mathematical Framework §10.8:
`t = b + 10 + 14*k`.
-/
def restCrossing (b : Nat) (k : Nat) : Nat := b + 10 + 14*k

/-- If `t` is a REST crossing of group `g`, then its seam state is REST. -/
lemma seamState_at_restCrossing (g k : Nat) :
    seamState g (restCrossing (birth g) k) = REST := by
  -- compute ((b+10+14k) - b) % 14 = 10
  apply Fin.ext
  simp [seamState, restCrossing, birth, REST]
  -- Goal after simp: (10 * g + 10 + 14 * k - 10 * g) % 14 = 10
  -- Cancel 10*g: (10*g + 10 + 14*k) - 10*g = 10 + 14*k
  simp [Nat.add_assoc]
  rw [Nat.add_sub_cancel_left]
  -- Now: (10 + 14*k) % 14 = 10
  rw [Nat.add_mod]
  simp [mod14_mul]
  -- Now: 10 % 14 = 10
  have : 10 < 14 := by decide
  exact Nat.mod_eq_of_lt this

/-- Bridge→Seed overlap lemma (baseline births):

At the child's birth time `birth (g+1)`,
- parent `g` is at REST (10)
- child `g+1` is at VOID (0)
-/
lemma overlap_baseline_rest_void (g : Nat) :
    seamState g (birth (g+1)) = REST ∧ seamState (g+1) (birth (g+1)) = VOID := by
  constructor
  · -- parent at REST: birth (g+1) = birth g + 10
    have : birth (g+1) = restCrossing (birth g) 0 := by
      simp [birth, restCrossing, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    -- rewrite and use the rest-crossing lemma
    simpa [this] using (seamState_at_restCrossing g 0)
  · -- child at VOID
    simpa using seamState_at_birth (g+1)

/-- Bridge→Seed overlap lemma (baseline births), expressed at the label level:

For k ∈ {1,2,3}:
- parent label = 10+k (COMPLETE band 11..13)
- child label  = k    (SEED band 1..3)
-/
lemma overlap_baseline_complete_seed (g : Nat) (k : Nat)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    seamLabel (seamState g (birth (g+1) + k)) = 10 + k ∧
    seamLabel (seamState (g+1) (birth (g+1) + k)) = k := by
  constructor
  · -- parent label = 10+k
    rcases hk with rfl | rfl | rfl
    · -- k = 1: goal is (1 + 10*(g+1) - 10*g) % 14 = 11
      simp [seamState, birth, seamLabel]
      -- Simplify: 1 + 10*(g+1) - 10*g = 1 + 10*g + 10 - 10*g = 11
      simp [Nat.mul_add, Nat.add_assoc]
      rw [Nat.add_sub_cancel_left]
      have : 11 < 14 := by decide
      exact Nat.mod_eq_of_lt this
    · -- k = 2: goal is (2 + 10*(g+1) - 10*g) % 14 = 12
      simp [seamState, birth, seamLabel]
      simp [Nat.mul_add, Nat.add_assoc]
      rw [Nat.add_sub_cancel_left]
      have : 12 < 14 := by decide
      exact Nat.mod_eq_of_lt this
    · -- k = 3: goal is (3 + 10*(g+1) - 10*g) % 14 = 13
      simp [seamState, birth, seamLabel]
      simp [Nat.mul_add, Nat.add_assoc]
      rw [Nat.add_sub_cancel_left]
      have : 13 < 14 := by decide
      exact Nat.mod_eq_of_lt this
  · -- child label = k
    rcases hk with rfl | rfl | rfl <;>
      simp [seamState, birth, seamLabel]

end UFRF
