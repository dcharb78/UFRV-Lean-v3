#!/bin/bash
# Build script with detailed logging and progress tracking

set -e

echo "🔨 UFRF-Moonshine Build with Logging"
echo "===================================="
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

# Check if we're in the right directory
if [ ! -f "lakefile.lean" ]; then
    echo -e "${RED}❌ Error: lakefile.lean not found. Run this script from the project root.${NC}"
    exit 1
fi

# Step 1: Check toolchain
echo -e "${BLUE}📋 Step 1: Checking Lean toolchain...${NC}"
if [ -f "lean-toolchain" ]; then
    TOOLCHAIN=$(cat lean-toolchain | tr -d '\n')
    echo -e "${CYAN}   Toolchain: $TOOLCHAIN${NC}"
else
    echo -e "${YELLOW}⚠️  No lean-toolchain file found${NC}"
fi

# Step 2: Check dependencies
echo ""
echo -e "${BLUE}📦 Step 2: Checking dependencies...${NC}"
if [ -d ".lake/packages/mathlib" ]; then
    echo -e "${GREEN}✅ Mathlib found${NC}"
    if [ -f ".lake/packages/mathlib/lean-toolchain" ]; then
        MATHLIB_TOOLCHAIN=$(cat .lake/packages/mathlib/lean-toolchain | tr -d '\n')
        echo -e "${CYAN}   Mathlib toolchain: $MATHLIB_TOOLCHAIN${NC}"
    fi
else
    echo -e "${YELLOW}⚠️  Mathlib not found - will be downloaded${NC}"
fi

# Step 3: Build with progress
echo ""
echo -e "${BLUE}🔨 Step 3: Building project...${NC}"
echo -e "${CYAN}   This may take several minutes if Mathlib needs to compile.${NC}"
echo -e "${CYAN}   Progress will be shown below:${NC}"
echo ""

# Create a log file
LOG_FILE=".lake/build.log"
mkdir -p .lake
> "$LOG_FILE"

# Function to show progress
show_progress() {
    local line="$1"
    # Extract job numbers like [162/388]
    if echo "$line" | grep -qE '\[[0-9]+/[0-9]+\]'; then
        echo -e "${CYAN}$line${NC}"
    # Show errors immediately
    elif echo "$line" | grep -qE '(error|✖|FAILED)'; then
        echo -e "${RED}$line${NC}"
    # Show successes
    elif echo "$line" | grep -qE '(✔|Built|successfully)'; then
        echo -e "${GREEN}$line${NC}"
    # Show warnings
    elif echo "$line" | grep -qE '(warning|⚠)'; then
        echo -e "${YELLOW}$line${NC}"
    # Show info messages
    elif echo "$line" | grep -qE '(info|Building|Running)'; then
        echo -e "${BLUE}$line${NC}"
    fi
    # Always append to log
    echo "$line" >> "$LOG_FILE"
}

# Build with progress tracking
BUILD_START=$(date +%s)
lake build 2>&1 | while IFS= read -r line; do
    show_progress "$line"
done
BUILD_EXIT=${PIPESTATUS[0]}
BUILD_END=$(date +%s)
BUILD_TIME=$((BUILD_END - BUILD_START))

echo ""
echo "===================================="
if [ $BUILD_EXIT -eq 0 ]; then
    echo -e "${GREEN}✅ Build completed successfully!${NC}"
    echo -e "${CYAN}   Build time: ${BUILD_TIME}s${NC}"
    echo ""
    echo -e "${BLUE}📊 Build Summary:${NC}"
    echo -e "${CYAN}   Full log saved to: $LOG_FILE${NC}"
    
    # Count built files
    BUILT_COUNT=$(find .lake/build/lib/lean -name "*.olean" 2>/dev/null | wc -l | tr -d ' ')
    echo -e "${CYAN}   Built files: $BUILT_COUNT${NC}"
    
    # Show what was built
    echo ""
    echo -e "${BLUE}📚 Built Libraries:${NC}"
    if [ -f ".lake/build/lib/lean/UFRF.olean" ]; then
        echo -e "${GREEN}   ✅ UFRF${NC}"
    fi
    if [ -f ".lake/build/lib/lean/Moonshine.olean" ]; then
        echo -e "${GREEN}   ✅ Moonshine${NC}"
    fi
else
    echo -e "${RED}❌ Build failed${NC}"
    echo -e "${CYAN}   Build time: ${BUILD_TIME}s${NC}"
    echo ""
    echo -e "${YELLOW}📋 Last 20 lines of build output:${NC}"
    tail -20 "$LOG_FILE" | sed 's/^/   /'
    echo ""
    echo -e "${CYAN}   Full log: $LOG_FILE${NC}"
    exit 1
fi

