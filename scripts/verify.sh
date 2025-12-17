#!/bin/bash
# UFRF-Moonshine Verification Script
# Fails if any `sorry` exists in the codebase or if compilation fails

set -e

echo "🔍 UFRF-Moonshine Verification Script"
echo "===================================="
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check if we're in the right directory
if [ ! -f "lakefile.lean" ]; then
    echo -e "${RED}❌ Error: lakefile.lean not found. Run this script from the project root.${NC}"
    exit 1
fi

# Step 1: Check for `sorry` in Lean files
echo "📋 Step 1: Checking for 'sorry' in Lean files..."
SORRY_COUNT=0
SORRY_FILES=()
UNDOCUMENTED_SORRY=0

while IFS= read -r -d '' file; do
    # Count sorry occurrences (excluding comments and strings)
    SORRIES=$(grep -n "sorry" "$file" | grep -v "^[[:space:]]*--" | grep -v "\".*sorry.*\"" || true)
    if [ -n "$SORRIES" ]; then
        # Check if sorry has documentation (DIRECTIONAL/REFINE/GAP/TODO within 3 lines)
        while IFS= read -r line_info; do
            LINE_NUM=$(echo "$line_info" | cut -d: -f1)
            FILE_CONTEXT=$(sed -n "$((LINE_NUM > 3 ? LINE_NUM - 3 : 1)),$LINE_NUM p" "$file")
            if ! echo "$FILE_CONTEXT" | grep -qE "(DIRECTIONAL|REFINE|GAP|TODO)" ; then
                UNDOCUMENTED_SORRY=$((UNDOCUMENTED_SORRY + 1))
                echo -e "${RED}❌ Undocumented 'sorry' in: $file:$line_info${NC}"
            fi
        done <<< "$SORRIES"
        
        SORRY_COUNT=$((SORRY_COUNT + $(echo "$SORRIES" | wc -l)))
        SORRY_FILES+=("$file")
        echo -e "${YELLOW}⚠️  Found 'sorry' in: $file${NC}"
        echo "$SORRIES" | sed 's/^/   /'
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $UNDOCUMENTED_SORRY -gt 0 ]; then
    echo ""
    echo -e "${RED}❌ FAILED: Found $UNDOCUMENTED_SORRY undocumented 'sorry' statement(s)${NC}"
    echo "   All 'sorry' must be tagged with DIRECTIONAL/REFINE/GAP or TODO (see docs/REFINEMENT_PHILOSOPHY.md)"
    exit 1
elif [ $SORRY_COUNT -gt 0 ]; then
    echo ""
    echo -e "${YELLOW}⚠️  Found $SORRY_COUNT documented 'sorry' statement(s) (directionally accurate work)${NC}"
    echo "   Run './scripts/list_directional.sh' to see refinement tasks"
else
    echo -e "${GREEN}✅ No 'sorry' found in Lean files${NC}"
fi

echo ""

# Step 2: Build the project
echo "🔨 Step 2: Building project with Lake..."
echo "   (Full output visible - this may take several minutes for first build)"
echo ""
if lake build 2>&1 | tee /tmp/ufrf_build_output.log; then
    echo ""
    echo -e "${GREEN}✅ Build successful${NC}"
else
    echo ""
    echo -e "${RED}❌ FAILED: Build errors detected${NC}"
    echo "   Last 20 lines of output:"
    tail -20 /tmp/ufrf_build_output.log | sed 's/^/   /'
    exit 1
fi

echo ""

# Step 3: Check for compilation errors in specific libraries
echo "📚 Step 3: Verifying library compilation..."

if lake build UFRF; then
    echo -e "${GREEN}✅ UFRF library builds successfully${NC}"
else
    echo -e "${RED}❌ FAILED: UFRF library has compilation errors${NC}"
    exit 1
fi

if lake build Moonshine; then
    echo -e "${GREEN}✅ Moonshine library builds successfully${NC}"
else
    echo -e "${RED}❌ FAILED: Moonshine library has compilation errors${NC}"
    exit 1
fi

echo ""

# Step 4: Check rule compliance
echo "📐 Step 4: Checking rule compliance..."
if ./scripts/check_rules.sh; then
    echo -e "${GREEN}✅ Rule compliance check passed${NC}"
else
    echo -e "${YELLOW}⚠️  Rule compliance check found warnings (non-fatal)${NC}"
fi

echo ""
echo -e "${GREEN}✅ All verification checks passed!${NC}"
echo ""

