import UFRF.ContextTags
import UFRF.Mod14

/-!
# UFRF ContextTags Tests

Quick verification tests for context tag invariants, focusing on:
- REST↔VOID duality (REST=10, VOID=0)
- Bridge→Seed overlap (parent COMPLETE 11-13 concurrent with child SEED 1-3)
- Birth invariants at REST positions
-/

namespace UFRF

/-- Test: At a phase group's birth, it is at VOID (state 0). -/
example (g : Nat) : seamState g (birth g) = VOID := by
  exact seamState_at_birth g

/-- Test: REST crossing times produce REST state (geometric necessity). -/
example (g k : Nat) : seamState g (restCrossing (birth g) k) = REST := by
  exact seamState_at_restCrossing g k

/-- Test: Bridge→Seed overlap at child's birth (parent at REST, child at VOID). -/
example (g : Nat) :
    seamState g (birth (g+1)) = REST ∧ seamState (g+1) (birth (g+1)) = VOID := by
  exact overlap_baseline_rest_void g

/-- Test: Parent COMPLETE (11-13) concurrent with child SEED (1-3) at offset k=1. -/
example (g : Nat) :
    seamLabel (seamState g (birth (g+1) + 1)) = 11 ∧
    seamLabel (seamState (g+1) (birth (g+1) + 1)) = 1 := by
  have h := overlap_baseline_complete_seed g 1 (Or.inl rfl)
  exact ⟨h.left, h.right⟩

/-- Test: REST state is exactly 10 (interior gateway). -/
example : REST.val = 10 := by
  simp [REST]

/-- Test: VOID state is exactly 0 (seam boundary). -/
example : VOID.val = 0 := by
  simp [VOID]

/-- Test: Mod14 helper - multiple of 14 vanishes mod 14. -/
example (k : Nat) : (14 * k) % 14 = 0 := by
  exact mod14_mul k

/-- Test: Adding multiple of 14 doesn't change remainder (concurrent phase preservation). -/
example (a k : Nat) : (a + 14 * k) % 14 = a % 14 := by
  exact mod14_add_mul a k

end UFRF

