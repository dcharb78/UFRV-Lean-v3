import Mathlib

import UFRF.SeamChart
import UFRF.ModuliCore

/-!
# Moonshine.UFRFBridge

This file is the *glue layer* between:
- the domain-level Moonshine objects (q-series indices, modular parameters), and
- the UFRF chart/bookkeeping layer (mod 13 manifest, mod 14 seam, contextual gates...).

The key idea is to keep the mapping explicit and configurable:
- different Moonshine normalizations shift indices (e.g. `q^{-1}` in `j`),
- different "chart choices" may tag the same coefficient with different local states.

So: **do not hide index shifts**. Make them explicit parameters.
-/

namespace Moonshine

/-- A configurable index shift, used to align domain indices with UFRF charts.

Example: the classical `j`-invariant has a leading `q^{-1}` term.
If you store coefficients starting at `n = 0` for `q^0`, then a shift of `+1`
aligns "coefficient index" with "power of q".

We keep this as a parameter so we can state invariance theorems like:
"the derived UFRF seam state depends only on `n + shift`".
-/
structure IndexShift where
  shift : Int

/-- Map a (possibly shifted) index to the **manifest** 13-cycle coordinate. -/
def manifest13 (sh : IndexShift) (n : Int) : Fin 13 :=
  let m := (n + sh.shift) % 13
  let m_nat := Int.toNat m
  ⟨m_nat % 13, Nat.mod_lt _ (by decide : 0 < 13)⟩

/-- Map a (possibly shifted) index to the **seam** 14-state coordinate. -/
def seam14 (sh : IndexShift) (n : Int) : UFRF.Seam14 :=
  let m := (n + sh.shift) % 14
  let m_nat := Int.toNat m
  ⟨m_nat % 14, Nat.mod_lt _ (by decide : 0 < 14)⟩

/-- Convenience for natural indices (common for coefficients). -/
def seam14Nat (sh : IndexShift) (n : Nat) : UFRF.Seam14 :=
  seam14 sh (Int.ofNat n)

end Moonshine

