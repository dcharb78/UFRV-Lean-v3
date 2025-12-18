# Quick Start Guide

This guide will help you get started with the UFRF-Moonshine project.

## Prerequisites

1. **Lean 4**: The project uses Lean 4.12.0 (managed via `lean-toolchain`)
2. **elan**: Lean version manager (install from [elan](https://github.com/leanprover/elan))
3. **Git**: For cloning and version control

## Installation

### Step 1: Clone the Repository

```bash
git clone <repository-url>
cd UFRF_Moonshine_Modular_v2
```

### Step 2: Install elan (if not already installed)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### Step 3: Install Dependencies

Lake will automatically install Lean 4 and Mathlib based on `lean-toolchain` and `lakefile.lean`:

```bash
lake exe cache get
```

### Step 4: Build the Project

```bash
lake build
```

This will:
- Download Lean 4.12.0 (if not already installed)
- Download Mathlib dependencies
- Build all Lean files in `lean/UFRF/` and `lean/Moonshine/`

### Step 5: Verify the Build

Run the verification script to check for `sorry` and compilation errors:

```bash
./scripts/verify.sh
```

This will:
- Check for `sorry` statements in Lean files
- Build the project
- Verify UFRF and Moonshine libraries compile
- Check rule compliance (architecture, namespaces, etc.)

You can also run rule checks separately:

```bash
./scripts/check_rules.sh
```

### Step 7: Track Directionally Accurate Work

If you have incomplete but directionally correct work, track it:

```bash
./scripts/list_directional.sh
```

This shows all DIRECTIONAL/REFINE/GAP tags. See `docs/REFINEMENT_PHILOSOPHY.md` for the philosophy.

## Project Structure

```
UFRF_Moonshine_Modular_v2/
├── lean/
│   ├── UFRF/              # UFRF Core library (shared)
│   │   ├── SeamChart.lean
│   │   ├── ContextTags.lean
│   │   ├── ModuliCore.lean
│   │   ├── ModuliLogs.lean
│   │   └── RamanujanFunctional.lean
│   └── Moonshine/         # Moonshine domain logic
│       ├── Basic.lean
│       ├── QSeries.lean
│       ├── JInvariant.lean
│       └── ...
├── docs/                  # Documentation
│   ├── ARCHITECTURE.md
│   ├── PLAN.md
│   ├── STYLE.md
│   └── DEVELOPMENT_PIPELINE.md
├── scripts/
│   └── verify.sh          # Verification script
├── lakefile.lean          # Lake project configuration
└── lean-toolchain         # Pinned Lean version
```

## Development Workflow

### 1. Making Changes

1. Create a feature branch: `git checkout -b feature/my-feature`
2. Edit Lean files in `lean/`
3. Build: `lake build`
4. Verify: `./scripts/verify.sh`
5. Commit changes

### 2. Adding New Files

When adding new Lean files:

1. **UFRF Core files**: Add to `lean/UFRF/`
   - Import with: `import UFRF.YourFile`
   - Namespace: `namespace UFRF`

2. **Moonshine files**: Add to `lean/Moonshine/`
   - Import with: `import Moonshine.YourFile`
   - Namespace: `namespace Moonshine`

3. **UFRF-Moonshine bridge**: Add to `lean/UFRF/Moonshine/` (to be created)
   - Import UFRF Core: `import UFRF.SeamChart`
   - Namespace: `namespace UFRF.Moonshine`

### 3. Building Specific Libraries

```bash
# Build only UFRF Core
lake build UFRF

# Build only Moonshine
lake build Moonshine

# Build everything
lake build
```

### 4. Checking for Errors

```bash
# Run verification script (checks for sorry + builds)
./scripts/verify.sh

# Or just build
lake build
```

## Common Tasks

### View Documentation

Lean files include documentation comments. View them in your editor or:

```bash
# Build with documentation
lake build

# Documentation is embedded in .olean files
```

### Working with Mathlib

Mathlib is automatically managed by Lake. To update:

1. Edit `lakefile.lean` to point to a new Mathlib commit
2. Run `lake exe cache get`
3. Run `lake build` to verify compatibility

### Troubleshooting

**Problem**: `lake build` fails with dependency errors
- **Solution**: Run `lake exe cache get` to refresh dependencies

**Problem**: Verification script finds `sorry` in files
- **Solution**: Replace `sorry` with complete proofs (see `docs/STYLE.md`)

**Problem**: Import errors
- **Solution**: Check namespace and import paths match file structure

**Problem**: Mathlib compatibility issues
- **Solution**: Check `docs/DEPENDENCIES.md` for compatible versions

## Next Steps

1. **Read the Documentation**:
   - `docs/ARCHITECTURE.md` - Project architecture
   - `docs/PLAN.md` - Development milestones
   - `docs/STYLE.md` - Coding style and conventions
   - `docs/DEVELOPMENT_PIPELINE.md` - Detailed development plan

2. **Explore the Code**:
   - Start with `lean/UFRF/SeamChart.lean` for UFRF Core basics
   - Check `lean/Moonshine/Basic.lean` for Moonshine structure

3. **Follow the Pipeline**:
   - See `docs/DEVELOPMENT_PIPELINE.md` for phased development approach
   - Begin with Phase 0 (Infrastructure) if not complete
   - Proceed to Phase 1 (UFRF Core Completion)

## Getting Help

- **Documentation**: Check `docs/` directory
- **Issues**: Report problems in project issues
- **Code Review**: Submit PRs for review

---

**Happy Proving!** 🎉

