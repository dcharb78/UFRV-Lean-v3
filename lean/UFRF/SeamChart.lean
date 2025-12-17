import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq

/-!
# UFRF Seam Chart (Seam14 vs Manifest13)

UFRF seam chart (Z₁₄) vs manifest cycle (13 positions).

This file is intentionally minimal: it introduces only the bookkeeping
needed to keep **VOID** distinct from “position 13”.

Docs basis:
- Z₁₄ minimal cyclic chart: `0 = seam/VOID`, `1..13 = manifest cycle`.
- REST is position `10`.

(Port into your repo as `lean/UFRF/SeamChart.lean` and add it to your
`UFRF.lean` import list.)

Note on Lean syntax:
- `import` commands must appear at the beginning of the file.
- A `/-- ... -/` doc-comment attaches to the *next declaration*, so it cannot
  precede an `import`. For a module-level docstring, use `/-! ... -/`.
-/

namespace UFRF

/-- Canonical manifest positions 1..13.
We store them as `Fin 13 = {0..12}` with label `val+1`.
-/
abbrev Manifest13 := Fin 13

/-- Optional seam/void chart with 14 states: 0..13.
Interpretation: 0 = VOID, 1..13 = manifest positions.
-/
abbrev Seam14 := Fin 14

/-- The visible label of a seam state (0..13). -/
def seamLabel (s : Seam14) : Nat := s.val

/-- The visible label of a manifest state (1..13). -/
def manifestLabel (m : Manifest13) : Nat := m.val.succ

/-- VOID / seam state. -/
def VOID : Seam14 := ⟨0, by decide⟩

/-- REST state (balance gateway) on the seam chart. -/
def REST : Seam14 := ⟨10, by decide⟩

/-- Predicate: seam state is VOID. -/
def isVOID (s : Seam14) : Prop := s = VOID

/-- Embed a manifest position (1..13) into the seam chart (0..13). -/
def manifestToSeam (m : Manifest13) : Seam14 :=
  ⟨m.val.succ, by
    -- m.val < 13 ⇒ m.val+1 < 14
    exact Nat.succ_lt_succ m.isLt⟩

/-- Project a seam state to a manifest position, if it is not VOID.
Returns `none` on VOID.
-/
def seamToManifest (s : Seam14) : Option Manifest13 :=
  if h : s.val = 0 then
    none
  else
    -- s.val ∈ {1..13} ⇒ s.val-1 ∈ {0..12}
    some ⟨s.val - 1, by
      -- since s.val < 14, we have s.val ≤ 13
      have hs_le : s.val ≤ 13 := Nat.le_of_lt_succ s.isLt
      have hs_sub_le : s.val - 1 ≤ 12 := by
        -- subtract 1 on both sides
        have := Nat.sub_le_sub_right hs_le 1
        -- 13 - 1 = 12
        simpa using this
      -- 12 < 13
      exact lt_of_le_of_lt hs_sub_le (by decide : 12 < 13)⟩

/-- `VOID` projects to nothing. -/
lemma seamToManifest_VOID : seamToManifest VOID = none := by
  simp [VOID, seamToManifest]

/-- Any embedded manifest position projects back to itself. -/
lemma seamToManifest_manifestToSeam (m : Manifest13) :
    seamToManifest (manifestToSeam m) = some m := by
  unfold seamToManifest manifestToSeam
  -- the `if` branch is false because (m.val+1) ≠ 0
  have h0 : (m.val.succ) ≠ 0 := by
    exact Nat.succ_ne_zero _
  -- Simplify: the coercion of a Fin is its val, so ↑⟨m.val.succ, ...⟩ = m.val.succ
  -- Then simplify the if-then-else using h0
  simp only [Fin.val_mk, dite_eq_ite]
  -- Use h0 to simplify the if: since (↑m).succ ≠ 0, we take the `some` branch
  simp only [if_neg h0]
  -- Now prove the Fin values are equal - congr handles the Option wrapper
  congr 1
  -- After congr, the goal is automatically solved by definitional equality

/-- The embedding `manifestToSeam` is injective (so the seam chart doesn't
identify distinct manifest positions).
-/
lemma manifestToSeam_injective : Function.Injective manifestToSeam := by
  intro a b hab
  apply Fin.ext
  -- compare the underlying naturals
  have : a.val.succ = b.val.succ := by
    exact congrArg Fin.val hab
  -- cancel `Nat.succ`
  exact Nat.succ_inj.mp this

/-- A very small, disciplined "forgetful" map from seam chart to a 13-cycle index.
We map:
- `0` (VOID) ↦ `0`
- `k` (1..13) ↦ `k mod 13` as a `Nat` in 1..12 or 0

This is only for quick arithmetic; prefer `seamToManifest` for type safety.
-/
def seamToNatMod13 (s : Seam14) : Nat := s.val % 13

/-- One-step advance in the seam chart (wraps 13 → 0). -/
def stepSeam (s : Seam14) : Seam14 :=
  ⟨(s.val + 1) % 14, by
    exact Nat.mod_lt _ (by decide : 0 < 14)⟩

end UFRF
