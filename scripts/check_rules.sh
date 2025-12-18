#!/bin/bash
# UFRF-Moonshine Rule Validation Script
# Checks for common rule violations and architectural drift

set -e

echo "🔍 UFRF-Moonshine Rule Validation"
echo "=================================="
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

VIOLATIONS=0

# Check 1: No Moonshine imports in UFRF Core
echo "📋 Check 1: UFRF Core files should not import Moonshine..."
UFRF_IMPORTS_MOONSHINE=0
while IFS= read -r -d '' file; do
    if grep -q "import.*Moonshine" "$file"; then
        echo -e "${RED}❌ VIOLATION: $file imports Moonshine${NC}"
        grep -n "import.*Moonshine" "$file" | sed 's/^/   /'
        UFRF_IMPORTS_MOONSHINE=$((UFRF_IMPORTS_MOONSHINE + 1))
        VIOLATIONS=$((VIOLATIONS + 1))
    fi
done < <(find lean/UFRF -name "*.lean" -type f -print0)

if [ $UFRF_IMPORTS_MOONSHINE -eq 0 ]; then
    echo -e "${GREEN}✅ No UFRF Core files import Moonshine${NC}"
fi

echo ""

# Check 2: Namespace consistency
echo "📋 Check 2: Namespace consistency..."
NAMESPACE_VIOLATIONS=0
while IFS= read -r -d '' file; do
    if [[ "$file" == lean/UFRF/* ]]; then
        if ! grep -q "namespace UFRF" "$file"; then
            echo -e "${YELLOW}⚠️  WARNING: $file is in UFRF/ but doesn't declare 'namespace UFRF'${NC}"
            NAMESPACE_VIOLATIONS=$((NAMESPACE_VIOLATIONS + 1))
        fi
    elif [[ "$file" == lean/Moonshine/* ]]; then
        if ! grep -q "namespace Moonshine" "$file"; then
            echo -e "${YELLOW}⚠️  WARNING: $file is in Moonshine/ but doesn't declare 'namespace Moonshine'${NC}"
            NAMESPACE_VIOLATIONS=$((NAMESPACE_VIOLATIONS + 1))
        fi
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $NAMESPACE_VIOLATIONS -eq 0 ]; then
    echo -e "${GREEN}✅ Namespace declarations are consistent${NC}"
fi

echo ""

# Check 3: Check for sorry without TODO
echo "📋 Check 3: 'sorry' should have TODO comments..."
SORRY_WITHOUT_TODO=0
while IFS= read -r -d '' file; do
    # Find lines with sorry that don't have TODO in nearby context
    SORRIES=$(grep -n "sorry" "$file" | grep -v "^[[:space:]]*--.*TODO" || true)
    if [ -n "$SORRIES" ]; then
        # Check if there's a TODO comment within 3 lines before
        while IFS= read -r line_info; do
            LINE_NUM=$(echo "$line_info" | cut -d: -f1)
            # Check 3 lines before for TODO
            if ! sed -n "$((LINE_NUM > 3 ? LINE_NUM - 3 : 1)),$LINE_NUM p" "$file" | grep -q "TODO"; then
                echo -e "${YELLOW}⚠️  WARNING: $file:$line_info - 'sorry' without nearby TODO${NC}"
                SORRY_WITHOUT_TODO=$((SORRY_WITHOUT_TODO + 1))
            fi
        done <<< "$SORRIES"
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $SORRY_WITHOUT_TODO -eq 0 ]; then
    echo -e "${GREEN}✅ All 'sorry' have TODO comments${NC}"
fi

echo ""

# Check 4: Verify 13/26 structure is maintained
echo "📋 Check 4: 13/26 double-octave structure..."
if grep -q "Manifest13\|Seam14\|Fin 13\|Fin 14" lean/UFRF/SeamChart.lean; then
    echo -e "${GREEN}✅ 13/26 structure maintained in SeamChart${NC}"
else
    echo -e "${RED}❌ VIOLATION: 13/26 structure may be missing${NC}"
    VIOLATIONS=$((VIOLATIONS + 1))
fi

echo ""

# Check 5: Verify Unity convention (1 prime, 2 not prime)
echo "📋 Check 5: Unity convention references..."
# This is more of a documentation check - ensure the convention is mentioned
if grep -qi "unity\|prime.*1\|1.*prime" docs/*.md .cursorrules 2>/dev/null; then
    echo -e "${GREEN}✅ Unity convention documented${NC}"
else
    echo -e "${YELLOW}⚠️  WARNING: Unity convention may not be documented${NC}"
fi

echo ""

# Check 6: Verify chart vs claims separation
echo "📋 Check 6: Chart vs claims documentation..."
if grep -qi "chart.*claim\|representation.*testable" docs/*.md .cursorrules 2>/dev/null; then
    echo -e "${GREEN}✅ Chart vs claims separation documented${NC}"
else
    echo -e "${YELLOW}⚠️  WARNING: Chart vs claims may not be documented${NC}"
fi

echo ""

# Summary
echo "=================================="
if [ $VIOLATIONS -eq 0 ]; then
    echo -e "${GREEN}✅ Rule validation passed!${NC}"
    exit 0
else
    echo -e "${RED}❌ Found $VIOLATIONS rule violation(s)${NC}"
    echo "   Please review and fix violations before proceeding."
    exit 1
fi

