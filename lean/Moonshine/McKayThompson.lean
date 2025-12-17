import Mathlib

/-!
# Moonshine.McKayThompson

Abstract interface for McKay–Thompson series.

Rather than immediately formalizing the Monster group and VOA machinery, we create an
*abstract structure* whose fields are the inputs a Moonshine proof needs:

- A graded object `V = ⊕ V_n`.
- An action of an element `g` on each grade.
- A trace generating function `T_g` as a q-series.
- Axioms asserting modularity/replicability conditions.

This lets us:
1) prove **generic theorems** ("if a series is replicable + normalized + growth conditions → Hauptmodul"), and
2) later discharge the axioms by constructing the Moonshine module.
-/

namespace Moonshine

-- Placeholder structure. Fill in once representation theory and q-series choices are fixed.
structure McKayThompsonPackage where
  -- TODO: choose types and fields
  dummy : True := True.intro

end Moonshine
