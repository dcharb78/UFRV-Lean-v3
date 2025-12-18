# Refinement Workflow: Practical Guide

## Quick Reference

### When to Use Tags

| Tag | When to Use | Example |
|-----|-------------|---------|
| `DIRECTIONAL:` | Structure/approach is correct, details incomplete | "This captures tesseract sync pattern correctly. Missing: harmonic corrections" |
| `REFINE:` | Proof strategy correct, needs completion | "Use fin_cases on ZMod 13. Need: complete case analysis" |
| `GAP:` | Known missing connection/theorem | "Missing: connection between Unity Prime and Monster primes" |

### Workflow States

```
1. Directionally Accurate (Tagged)
   ↓
2. Refining (In Progress)
   ↓
3. Complete (Tag Removed)
```

## Common Scenarios

### Scenario 1: New Structure Definition

```lean
-- DIRECTIONAL: This structure captures UFRF-Moonshine bridge correctly
-- GAP: Missing proof of coefficient independence
structure Params where
  phi : ℝ
  cycleLen : Nat := 13
  -- TODO: Add REST index, voidIndex (direction correct, details pending)
```

**Action**: Tag as DIRECTIONAL, proceed to use structure, refine later.

### Scenario 2: Theorem with Incomplete Proof

```lean
-- REFINE: Proof strategy is correct (use fin_cases on ZMod 13)
-- Need to: Add explicit case analysis for all 13 residues
theorem mod13_pattern (n : Nat) : pZ 13 n = 0 ∨ pZ 13 n = 11 := by
  -- Current: Basic structure correct
  -- Refine: Complete case analysis
  sorry
```

**Action**: Tag as REFINE, document strategy, complete in refinement pass.

### Scenario 3: Missing Connection

```lean
-- GAP: Missing connection between Unity Prime and Monster primes
-- Direction: Use SEED phase positions 1-3 as foundation
-- TODO: Prove F(0), F(1), F(2) map to Monster prime constraints
```

**Action**: Tag as GAP, document direction, fill when dependencies ready.

## Refinement Pass Checklist

When doing a refinement pass:

- [ ] Run `./scripts/list_directional.sh` to see all incomplete work
- [ ] Prioritize: Wrong directions first, then core theorems, then edge cases
- [ ] Update tags as work progresses (DIRECTIONAL → REFINING → remove tag)
- [ ] Document what was completed
- [ ] Run `./scripts/verify.sh` after refinement

## Integration with Pipeline

### Phase Exit Criteria (Revised)

**Can exit phase if**:
- ✅ All code is directionally accurate (no wrong approaches)
- ✅ All incomplete work is tagged
- ✅ Core structure compiles
- ⚠️ Some proofs may be incomplete (with documented plan)

**Cannot exit phase if**:
- ❌ Wrong directions exist
- ❌ Undocumented `sorry`
- ❌ Architectural violations

### Between Phases

1. **Refinement Pass** (optional but recommended):
   - Complete high-priority directionally accurate work
   - Fill critical gaps
   - Update tags

2. **Validation**:
   - Run `./scripts/verify.sh`
   - Run `./scripts/list_directional.sh`
   - Document what remains incomplete

3. **Proceed**:
   - If directionally accurate → proceed to next phase
   - If wrong direction → fix before proceeding

---

**Remember**: Directionally accurate work is valuable. Tag it, document it, refine it incrementally.

