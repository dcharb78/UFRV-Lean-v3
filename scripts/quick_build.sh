#!/bin/bash
# Quick build script that shows only essential progress

set -e

echo "🔨 Building UFRF-Moonshine..."
echo ""

# Build and filter output to show only progress
lake build 2>&1 | grep -E '\[[0-9]+/[0-9]+\]|✔|✖|error|Built|successfully|FAILED' | while IFS= read -r line; do
    if echo "$line" | grep -qE '\[[0-9]+/[0-9]+\]'; then
        # Extract and show progress
        PROGRESS=$(echo "$line" | grep -oE '\[[0-9]+/[0-9]+\]' | head -1)
        echo "   $PROGRESS $line" | sed 's/.*\[\([0-9]*\)\/\([0-9]*\)\].*/[\1\/\2]/' | tr -d '\n'
        echo -n " - "
        echo "$line" | sed 's/.*\[[0-9]*\/[0-9]*\] *//'
    elif echo "$line" | grep -qE '(error|✖|FAILED)'; then
        echo "❌ $line"
    elif echo "$line" | grep -qE '(✔|Built|successfully)'; then
        echo "✅ $line"
    fi
done

EXIT_CODE=${PIPESTATUS[0]}

if [ $EXIT_CODE -eq 0 ]; then
    echo ""
    echo "✅ Build successful!"
else
    echo ""
    echo "❌ Build failed - run './scripts/build_with_logging.sh' for full details"
    exit 1
fi

