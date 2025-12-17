import Mathlib

/-!
# Moonshine.QSeries

Utilities for q-expansions and formal power series.

Design goal:
- Keep the interface small.
- Make it easy to switch between:
  - formal series (e.g. `PowerSeries ℂ`),
  - Laurent series (for the `q^{-1}` term),
  - analytic functions with `q = exp(2πiτ)`.

TODO:
- Choose a canonical representation for `q`-series used in `j` and McKay–Thompson series.
- Add coefficient extraction helpers and algebra lemmas.
- Add a `O(q^N)` notion for truncations.
-/

namespace Moonshine

-- Placeholder: replace with the chosen series type.
abbrev QSeries (R : Type) := Nat → R

/-- Coefficient extractor (temporary). -/
def coeff {R} (f : QSeries R) (n : Nat) : R := f n

end Moonshine
