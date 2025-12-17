import Mathlib

/-!
# Moonshine.Basic

Common namespace conventions and basic objects used across the Moonshine development.

This file is intentionally lightweight: it should compile early, and should only introduce
minimal definitions that later files can extend.

TODO:
- Decide whether to model the upper half-plane as `UpperHalfPlane` (Mathlib) or define an alias.
- Decide the group: `SL(2,ℤ)` vs `SL(2,ℤ)` as `SL(2, ℤ)` from Mathlib.
- Add the Möbius action and basic lemmas once the exact Mathlib modules are selected.
-/

namespace Moonshine

/-- Placeholder: the complex upper half-plane. Replace with the Mathlib definition you prefer. -/
abbrev H := {z : ℂ // 0 < z.im}

end Moonshine
