import Mathlib

/-!
# Moonshine.MonsterDimension

A minimal arithmetic lemma used in many UFRF moonshine narratives:

`196884 = 47 * 59 * 71 + 1`.

This is a *pure arithmetic* fact. The Moonshine work is then to justify why
those primes (or that product form) is the relevant one.

We keep this as its own file to make the dependency structure explicit.
-/

namespace Moonshine

theorem monster_dim_identity : 196884 = 47 * 59 * 71 + 1 := by
  norm_num

end Moonshine

