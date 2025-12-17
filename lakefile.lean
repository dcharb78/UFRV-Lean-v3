import Lake
open Lake DSL

/-!
UFRF_Moonshine_Modular_v2

This is a **modular** Lean 4 project intended to:
- host the UFRF core library (chart/bookkeeping + minimal algebra), and
- host a Moonshine domain library that depends on UFRF core.

Toolchain note:
- `lean-toolchain` is pinned (currently: Lean v4.27.0-rc1 to match Mathlib).
- If Mathlib requires a different toolchain, update `lean-toolchain` accordingly.

See: Lean release notes (for current stable versions) and Mathlib docs/toolchain alignment.
-/

package ufrf_moonshine where
  version := v!"2.0.0"
  -- Increase memory if you hit elaboration memory limits.
  moreServerArgs := #[]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

/-- Mathlib dependency.

Using master branch - update lean-toolchain if Mathlib requires newer Lean version.
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib UFRF where
  srcDir := "lean"
  roots := #[`UFRF]

lean_lib Moonshine where
  srcDir := "lean"
  roots := #[`Moonshine]
