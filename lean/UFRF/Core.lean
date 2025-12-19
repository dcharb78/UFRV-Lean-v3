import UFRF.SeamChart
import UFRF.ContextTags
import UFRF.Projection
import UFRF.ModuliCore
import UFRF.ModuliLogs
import UFRF.RamanujanFunctional
import UFRF.Mod14
import UFRF.Axioms
import UFRF.Params
import UFRF.LogSpaces

/-!
# UFRF Core - Unified Import

This file provides a single import point for all UFRF Core modules.
Downstream packages (Moonshine, Euler, etc.) can import this to get
access to the complete UFRF Core library.

## Architecture

UFRF Core is a shared "bookkeeping + axioms" library that provides:
- Seam chart (13 manifest positions + 14-state seam chart)
- Context tags and overlap lemmas
- Moduli patterns (mod 3/4/13/14)
- Chart helpers (Lin, logB, mod0)
- Ramanujan functional equation core

## Usage

```lean
import UFRF.Core
```

This gives you access to all UFRF Core definitions and theorems.

## Module Structure

- `UFRF.SeamChart` - 13/14 state distinction, VOID/REST
- `UFRF.ContextTags` - Context tags, births, overlap lemmas
- `UFRF.ModuliCore` - Residue constraints for p(n)=n(n+2)
- `UFRF.ModuliLogs` - Chart helpers (Lin, logB, mod0)
- `UFRF.RamanujanFunctional` - Functional equation core

## Principles

- **Chart vs Claims**: Charts are representation choices, gates are testable rules
- **13/26 Double-Octave**: 13 manifest positions, 14-state seam chart
- **Lean-First**: Minimal assumptions, finite proofs, total functions
- **Directional Accuracy**: Incomplete but correct work is tagged (see docs/REFINEMENT_PHILOSOPHY.md)
-/

namespace UFRF

/-!
## Re-exports

All definitions and theorems from the core modules are available
through this unified import.
-/

end UFRF
