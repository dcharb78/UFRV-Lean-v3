# Build Troubleshooting Guide

## Understanding Build Progress

When `lake build` shows `[162/388]`, this means:
- **162**: Number of jobs completed
- **388**: Total number of jobs to build
- This is **normal** - Lake builds dependencies (Mathlib, etc.) in parallel

### What's Actually Happening

1. **Mathlib Compilation** (most time): Mathlib has ~7000+ files that need compilation
2. **Dependency Building**: Batteries, Qq, Aesop, ProofWidgets, etc.
3. **Your Project**: UFRF and Moonshine libraries (fast, once dependencies are done)

### Is It Stuck?

**Not stuck if you see:**
- Job numbers incrementing: `[162/388]`, `[163/388]`, etc.
- "Building X" messages
- No error messages

**Actually stuck if:**
- Job number doesn't change for >5 minutes
- Error messages appear
- "No goals to be solved" or syntax errors

## Build Scripts

### Detailed Logging
```bash
./scripts/build_with_logging.sh
```
- Shows all progress with colors
- Saves full log to `.lake/build.log`
- Shows build summary at end

### Quick Build (Progress Only)
```bash
./scripts/quick_build.sh
```
- Shows only job progress: `[162/388]`
- Filters out verbose output
- Faster to see if it's progressing

### Plain Lake Build
```bash
lake build
```
- Standard Lake output
- Use `tail -30` to see last 30 lines

## Common Issues

### Issue 1: "No goals to be solved"
**Cause**: Proof error - trying to solve something already solved
**Fix**: Check the proof, remove redundant tactics

### Issue 2: "invalid 'import' command"
**Cause**: Import after docstring or namespace
**Fix**: Move all `import` statements to the very top of the file

### Issue 3: Mathlib Version Mismatch
**Cause**: Lean version doesn't match Mathlib requirements
**Fix**: 
```bash
cat .lake/packages/mathlib/lean-toolchain > lean-toolchain
lake clean
lake build
```

### Issue 4: Build Appears Stuck
**Diagnosis**:
```bash
# Check if Lake is actually running
ps aux | grep lean

# Check last build output
tail -30 .lake/build.log 2>/dev/null || lake build 2>&1 | tail -30
```

**If actually stuck:**
- Kill the process: `pkill -f lean`
- Clean and rebuild: `lake clean && lake build`

## Speed Optimization

### Use Mathlib Cache
```bash
lake exe cache get
```
This downloads precompiled Mathlib instead of compiling from scratch.

### Build Only What You Need
```bash
# Build just UFRF
lake build UFRF

# Build just one file
lake build UFRF.SeamChart
```

### Parallel Building
Lake automatically uses parallel builds. You can see progress with:
```bash
lake build --verbose
```

## Monitoring Build Progress

### Real-time Progress
```bash
# Watch the last 10 lines
watch -n 1 'lake build 2>&1 | tail -10'
```

### Check What's Built
```bash
# Count compiled files
find .lake/build/lib/lean -name "*.olean" | wc -l

# List your project's built files
ls -la .lake/build/lib/lean/UFRF/
ls -la .lake/build/lib/lean/Moonshine/
```

### Check Build Status
```bash
# See if UFRF built successfully
test -f .lake/build/lib/lean/UFRF.olean && echo "✅ UFRF built" || echo "❌ UFRF not built"

# See if Moonshine built successfully  
test -f .lake/build/lib/lean/Moonshine.olean && echo "✅ Moonshine built" || echo "❌ Moonshine not built"
```

## Expected Build Times

- **First build (no cache)**: 10-30 minutes (compiling Mathlib)
- **With cache**: 1-5 minutes
- **Incremental builds**: 10-60 seconds
- **Single file**: <5 seconds

## Getting Help

If build is stuck or failing:

1. **Check the log**: `tail -50 .lake/build.log`
2. **Run with logging**: `./scripts/build_with_logging.sh`
3. **Check for errors**: Look for `error:` or `✖` in output
4. **Verify syntax**: `lake build UFRF.SeamChart` (builds just one file)

---

**Remember**: If you see `[162/388]` and it's incrementing, it's **working** - just compiling Mathlib dependencies. Be patient!

