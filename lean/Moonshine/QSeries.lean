import Mathlib

/-!
# Moonshine.QSeries

Utilities for q-expansions and formal power series.

Design goal:
- Keep the interface small.
- Use Mathlib's `PowerSeries` as the base representation.
- Support both formal series and future Laurent series (for `q^{-1}` terms).

For the j-invariant with leading `q^{-1}`, we'll use a shift: represent `q^{-1} + a₁q + ...`
as a `PowerSeries` starting at index 0, with the understanding that index 0 corresponds to `q^{-1}`.

This is directionally accurate - we can refine to proper Laurent series later if needed.
-/

namespace Moonshine

/-- A q-series as a formal power series over a commutative semiring.

For series with negative powers (like j-invariant), we use a shift convention:
- Index 0 represents the `q^{-1}` coefficient
- Index n represents the `q^{n-1}` coefficient

This allows us to use `PowerSeries` while handling the `q^{-1}` term naturally.
-/
abbrev QSeries (R : Type) [CommSemiring R] := PowerSeries R

/-- Extract the coefficient of `q^n` from a q-series.

For series with `q^{-1}` leading term:
- `coeff f 0` gives the `q^{-1}` coefficient
- `coeff f (n+1)` gives the `q^n` coefficient
-/
noncomputable def coeff {R} [CommSemiring R] (f : QSeries R) (n : Nat) : R :=
  PowerSeries.coeff n f

/-- The zero q-series. -/
def zero {R} [CommSemiring R] : QSeries R := 0

/-- The one q-series (constant term 1, all others 0). -/
noncomputable def one {R} [CommSemiring R] : QSeries R := 1

/-- Helper: create a q-series from a coefficient function. -/
def mk {R} [CommSemiring R] (coeffs : Nat → R) : QSeries R :=
  PowerSeries.mk coeffs

/-- Truncation: a q-series is `O(q^N)` if all coefficients before N are zero.

For series with `q^{-1}` leading term:
- `isOqN f 0` means no `q^{-1}` term (starts at `q^0`)
- `isOqN f (N+1)` means starts at `q^N`
-/
def isOqN {R} [CommSemiring R] (f : QSeries R) (N : Nat) : Prop :=
  ∀ n < N, coeff f n = 0

/-- A q-series starts at exactly `q^N` if it's `O(q^N)` but not `O(q^(N+1))`. -/
def startsAt {R} [CommSemiring R] (f : QSeries R) (N : Nat) : Prop :=
  isOqN f N ∧ coeff f N ≠ 0

/-- Two q-series are equal if all coefficients agree. -/
theorem ext {R} [CommSemiring R] {f g : QSeries R} :
    f = g ↔ ∀ n, coeff f n = coeff g n := by
  simp [coeff]
  rw [PowerSeries.ext_iff]

end Moonshine
