# Dependency Management & Version Compatibility

This document tracks all dependencies and their versions for the UFRF-Moonshine project.

## Core Dependencies

### Lean 4
- **Version**: `v4.12.0` (pinned in `lean-toolchain`)
- **Source**: [leanprover/lean4](https://github.com/leanprover/lean4)
- **Purpose**: Proof assistant and language

### Mathlib
- **Version**: Latest compatible with Lean 4.12.0
- **Source**: [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)
- **Purpose**: Mathematical library for modular forms, number theory, etc.
- **Update Policy**: Test upgrades in isolated branch before merging

## Build Tools

### Lake
- **Version**: Bundled with Lean 4
- **Purpose**: Build system and package manager

### elan
- **Version**: Latest (for CI)
- **Purpose**: Lean version manager

## Compatibility Matrix

| Lean Version | Mathlib Commit | Status | Notes |
|-------------|----------------|--------|-------|
| v4.12.0     | Latest         | ✅ Current | Primary development version |

## Upgrading Dependencies

### Procedure

1. **Create upgrade branch**: `git checkout -b upgrade/lean-4.x.x`
2. **Update `lean-toolchain`**: Change version number
3. **Update Mathlib** (if needed): Update commit hash in `lakefile.lean`
4. **Test compilation**: Run `lake build` and `./scripts/verify.sh`
5. **Fix any errors**: Address compilation issues
6. **Update this document**: Record new versions and compatibility
7. **Create PR**: Submit for review

### Testing Checklist

- [ ] All UFRF Core files compile
- [ ] All Moonshine files compile
- [ ] `scripts/verify.sh` passes
- [ ] No new `sorry` introduced
- [ ] Existing proofs still work
- [ ] CI pipeline passes

## Known Issues

None currently. Report compatibility issues in project issues.

## Future Dependencies

Potential future dependencies (not yet integrated):

- **Custom UFRF libraries**: May split into separate packages
- **Validation tools**: Additional proof checkers if needed
- **Documentation generators**: For API documentation

---

**Last Updated**: 2024  
**Maintainer**: Development Team

