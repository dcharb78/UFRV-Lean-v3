import Mathlib

/-!
# UFRF.Projection

This file captures the **projection law** used throughout the UFRF docs.

UFRF axiom (algebraic form):

`ln O = ln O* + Σ_i (d_M(i) · α_i · S_i) + ε`.

Lean design goals:
- Keep the core statement *domain-agnostic*.
- Make "domain-specific parameters" explicit:
  - `dM` = scale distance (a real-valued input)
  - `α`  = technique coupling strength (input; often assumed in [0,1])
  - `S`  = systematic surrogate (input)
  - `ε`  = residual/noise term (input)

Downstream domains should supply these values/assumptions via their own interfaces.
-/

namespace UFRF

/-- One projection layer (observer→target) used in the composed projection law. -/
structure ProjectionLayer where
  dM : ℝ
  α  : ℝ
  S  : ℝ
  ε  : ℝ := 0

/-- The additive contribution of a single projection layer. -/
def layerTerm (L : ProjectionLayer) : ℝ := L.dM * L.α * L.S + L.ε

/-- Apply a list of projection layers to an intrinsic log-value `lnO*`. -/
def project (lnOstar : ℝ) (layers : List ProjectionLayer) : ℝ :=
  lnOstar + (layers.map layerTerm).sum

@[simp] theorem project_nil (lnOstar : ℝ) : project lnOstar [] = lnOstar := by
  simp [project]

@[simp] theorem project_cons (lnOstar : ℝ) (L : ProjectionLayer) (Ls : List ProjectionLayer) :
    project lnOstar (L :: Ls) = project (lnOstar + layerTerm L) Ls := by
  simp [project, List.map_cons, List.sum_cons, add_assoc, add_left_comm, add_comm]

/-- Composition lemma: applying `A ++ B` equals applying `A` then `B`. -/
theorem project_append (lnOstar : ℝ) (A B : List ProjectionLayer) :
    project lnOstar (A ++ B) = project (project lnOstar A) B := by
  -- Expand both sides and use `List.sum_append`.
  simp [project, List.map_append, List.sum_append, add_assoc, add_left_comm, add_comm]

end UFRF

