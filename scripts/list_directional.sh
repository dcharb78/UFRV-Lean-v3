#!/bin/bash
# List all directionally accurate work that needs refinement

echo "🔍 Directionally Accurate Work Tracker"
echo "======================================"
echo ""

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}📋 DIRECTIONAL Tags (Correct direction, incomplete details):${NC}"
echo ""

DIRECTIONAL_COUNT=0
while IFS= read -r -d '' file; do
    DIRECTIONAL=$(grep -n "DIRECTIONAL:" "$file" 2>/dev/null || true)
    if [ -n "$DIRECTIONAL" ]; then
        echo -e "${YELLOW}📄 $file${NC}"
        echo "$DIRECTIONAL" | sed 's/^/   /'
        DIRECTIONAL_COUNT=$((DIRECTIONAL_COUNT + $(echo "$DIRECTIONAL" | wc -l)))
        echo ""
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $DIRECTIONAL_COUNT -eq 0 ]; then
    echo -e "${GREEN}✅ No DIRECTIONAL tags found${NC}"
else
    echo -e "${YELLOW}Found $DIRECTIONAL_COUNT DIRECTIONAL tag(s)${NC}"
fi

echo ""
echo -e "${BLUE}🔧 REFINE Tags (Needs refinement):${NC}"
echo ""

REFINE_COUNT=0
while IFS= read -r -d '' file; do
    REFINE=$(grep -n "REFINE:" "$file" 2>/dev/null || true)
    if [ -n "$REFINE" ]; then
        echo -e "${YELLOW}📄 $file${NC}"
        echo "$REFINE" | sed 's/^/   /'
        REFINE_COUNT=$((REFINE_COUNT + $(echo "$REFINE" | wc -l)))
        echo ""
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $REFINE_COUNT -eq 0 ]; then
    echo -e "${GREEN}✅ No REFINE tags found${NC}"
else
    echo -e "${YELLOW}Found $REFINE_COUNT REFINE tag(s)${NC}"
fi

echo ""
echo -e "${BLUE}🕳️  GAP Tags (Known gaps):${NC}"
echo ""

GAP_COUNT=0
while IFS= read -r -d '' file; do
    GAP=$(grep -n "GAP:" "$file" 2>/dev/null || true)
    if [ -n "$GAP" ]; then
        echo -e "${YELLOW}📄 $file${NC}"
        echo "$GAP" | sed 's/^/   /'
        GAP_COUNT=$((GAP_COUNT + $(echo "$GAP" | wc -l)))
        echo ""
    fi
done < <(find lean -name "*.lean" -type f -print0)

if [ $GAP_COUNT -eq 0 ]; then
    echo -e "${GREEN}✅ No GAP tags found${NC}"
else
    echo -e "${YELLOW}Found $GAP_COUNT GAP tag(s)${NC}"
fi

echo ""
echo "======================================"
TOTAL=$((DIRECTIONAL_COUNT + REFINE_COUNT + GAP_COUNT))
if [ $TOTAL -eq 0 ]; then
    echo -e "${GREEN}✅ All work is complete!${NC}"
else
    echo -e "${YELLOW}Total incomplete work: $TOTAL tag(s)${NC}"
    echo "   Use these tags to track refinement progress"
fi
echo ""

