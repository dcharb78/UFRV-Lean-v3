import Mathlib

/-!
# Moonshine.GenusZero

Target statements about modular curves and Hauptmoduln.

Staged goals:
1) Define the modular curve quotient `X(Γ)` (in whatever form is feasible in Mathlib).
2) Define genus, genus-zero, and the notion of a Hauptmodul.
3) Prove: `j` is a Hauptmodul for `SL(2,ℤ)`.
4) Provide a theorem scheme: if a normalized series satisfies replicability + growth,
   then it is the Hauptmodul of a genus-zero group.
-/

namespace Moonshine

-- TODO: fill in once the analytic setup is chosen.

def isHauptmodul (f : ℂ → ℂ) : Prop := True

end Moonshine
