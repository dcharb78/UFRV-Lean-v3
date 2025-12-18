# Refinement Philosophy: Quick Summary

## Core Principle

> **"Directionally accurate, not 100% complete" is a valid intermediate state.**

Many times we are directionally accurate but not 100% complete. This doesn't mean wrong - it means missing something.

## Three States

1. ✅ **Directionally Accurate** - Correct structure/approach, incomplete details → **Tag and proceed**
2. ✅ **Complete** - Fully implemented and proven → **No tags needed**
3. ❌ **Wrong Direction** - Fundamentally incorrect → **Must fix immediately**

## Tagging System

Use these tags in your code:

```lean
-- DIRECTIONAL: [what's correct] - Missing: [what's incomplete]
-- REFINE: [strategy] - Need: [what to complete]
-- GAP: [what's missing] - Direction: [how to fill]
```

## Tools

```bash
# List all directionally accurate work
./scripts/list_directional.sh

# Verify (distinguishes documented vs undocumented sorry)
./scripts/verify.sh

# Check rule compliance
./scripts/check_rules.sh
```

## Workflow

1. **Establish Direction** → Tag incomplete work
2. **Document Gaps** → Explain what's correct and what's missing
3. **Proceed** → Can move to next phase if directionally accurate
4. **Refine Incrementally** → Complete details in refinement passes

## Key Insight

**"Not 100% complete" ≠ "Wrong"**

It means: "Correct direction, needs refinement"

---

**Full Details**: See `docs/REFINEMENT_PHILOSOPHY.md` and `docs/REFINEMENT_WORKFLOW.md`

