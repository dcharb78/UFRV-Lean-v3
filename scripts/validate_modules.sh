#!/bin/bash
# Validate all modules individually when lake build is not working
# This is a workaround until lakefile.lean syntax is resolved

set -e

echo "🔍 Module Validation (Individual File Check)"
echo "==========================================="
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

ERRORS=0

# Function to check a Lean file
check_file() {
    local file=$1
    echo -n "Checking $file... "
    
    if lake env lean "$file" > /dev/null 2>&1; then
        echo -e "${GREEN}✅${NC}"
        return 0
    else
        echo -e "${RED}❌${NC}"
        lake env lean "$file" 2>&1 | head -10
        return 1
    fi
}

echo "📚 UFRF Core Modules:"
echo ""

# Check UFRF Core files
for file in lean/UFRF/*.lean; do
    if [ -f "$file" ]; then
        if ! check_file "$file"; then
            ERRORS=$((ERRORS + 1))
        fi
    fi
done

echo ""
echo "🌙 Moonshine Modules:"
echo ""

# Check Moonshine files
for file in lean/Moonshine/*.lean; do
    if [ -f "$file" ]; then
        if ! check_file "$file"; then
            ERRORS=$((ERRORS + 1))
        fi
    fi
done

echo ""
echo "🧪 Test Files:"
echo ""

# Check test files
for file in tests/**/*.lean; do
    if [ -f "$file" ]; then
        if ! check_file "$file"; then
            ERRORS=$((ERRORS + 1))
        fi
    fi
done

echo ""
echo "==========================================="
if [ $ERRORS -eq 0 ]; then
    echo -e "${GREEN}✅ All modules validated successfully!${NC}"
    exit 0
else
    echo -e "${RED}❌ Found $ERRORS error(s)${NC}"
    exit 1
fi

