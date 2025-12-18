# Cursor Rules Documentation

This document explains the `.cursorrules` file and how it helps maintain project consistency.

## Purpose

The `.cursorrules` file provides instructions to AI coding assistants (like Cursor) to:
- **Prevent architectural drift** - Maintain strict separation between UFRF Core and Moonshine
- **Enforce conventions** - Unity convention, 13/26 structure, chart vs claims separation
- **Follow best practices** - Lean-first minimal assumptions, total functions, finite proofs
- **Maintain documentation** - Update planning docs, document public APIs

## Key Rules Enforced

### 1. Architecture Separation

**Rule**: UFRF Core files must NEVER import Moonshine modules.

**Why**: This maintains the modular architecture where UFRF Core is a shared library that can be used by multiple domains (Moonshine, Euler, Navier-Stokes, etc.).

**Enforcement**: The `check_rules.sh` script detects violations.

### 2. UFRF Core Principles

**Rules**:
- Unity convention: 1 prime, 2 not prime
- 13/26 double-octave: Node/void approach
- Chart vs Claims: Separate representation from testable rules
- 13 manifest positions vs 14-state seam chart

**Why**: These are fundamental UFRF principles that must be maintained throughout the codebase.

### 3. Lean-First Minimal Assumptions

**Rules**:
- Prefer algebraic identities over limits
- Use finite-case proofs (`fin_cases`) for small moduli
- Keep definitions total
- Use `Lin(x)=x` instead of base-1 logarithm

**Why**: This keeps proofs verifiable and avoids heavy analytic machinery.

### 4. Proof Architecture

**Rules**:
- Start with weakest hypotheses
- Break into smaller lemmas
- Document public APIs
- Tag new moduli as Chart or Gate

**Why**: Maintains code quality and makes proofs maintainable.

## Validation

### Automated Checks

Run the rule validation script:

```bash
./scripts/check_rules.sh
```

This checks for:
- UFRF Core files importing Moonshine (violation)
- Namespace consistency (warning)
- `sorry` without TODO comments (warning)
- 13/26 structure maintenance
- Unity convention documentation
- Chart vs claims documentation

### Integration with verify.sh

The `verify.sh` script automatically runs `check_rules.sh` as part of the verification process.

## How Cursor Uses These Rules

When you use Cursor AI to edit code:

1. **Cursor reads `.cursorrules`** before making suggestions
2. **Rules are enforced** - Cursor will warn or refuse to make changes that violate rules
3. **Consistency maintained** - All AI-assisted edits follow the same conventions

## Updating Rules

If you need to add or modify rules:

1. Edit `.cursorrules` file
2. Update this documentation if needed
3. Test with `./scripts/check_rules.sh`
4. Commit changes

## Common Violations

### ❌ Violation: Importing Moonshine in UFRF Core

```lean
-- lean/UFRF/SomeFile.lean
import Moonshine.Basic  -- ❌ VIOLATION
```

**Fix**: Remove the import or move the code to the appropriate layer.

### ❌ Violation: Using `sorry` without TODO

```lean
theorem some_theorem : P := by
  sorry  -- ❌ VIOLATION: No TODO comment
```

**Fix**: Add a TODO comment explaining the plan:

```lean
theorem some_theorem : P := by
  -- TODO: Complete proof using fin_cases on ZMod 13
  sorry
```

### ⚠️ Warning: Namespace Mismatch

```lean
-- lean/UFRF/SomeFile.lean
namespace Moonshine  -- ⚠️ WARNING: Should be namespace UFRF
```

**Fix**: Use the correct namespace for the file location.

## Best Practices

1. **Read `.cursorrules`** before making major changes
2. **Run `check_rules.sh`** before committing
3. **Follow the rules** even if they seem restrictive - they prevent architectural drift
4. **Document exceptions** if you must violate a rule (with justification)

## Related Documents

- `.cursorrules` - The actual rules file
- `docs/STYLE.md` - Coding style guidelines
- `docs/ARCHITECTURE.md` - Architecture decisions
- `docs/DEVELOPMENT_PIPELINE.md` - Development phases

---

**Remember**: These rules exist to maintain the integrity of the modular architecture and UFRF principles. Following them ensures the codebase remains maintainable and consistent.

