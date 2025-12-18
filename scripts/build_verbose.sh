#!/bin/bash
# Build with FULL visible output - no hiding, no filtering

set -e

echo "🔨 Building UFRF-Moonshine (FULL OUTPUT)"
echo "========================================="
echo ""
echo "You will see ALL build output in real-time."
echo "Press Ctrl+C to cancel if needed."
echo ""
echo "Starting build..."
echo ""

# Build with full output - NO filtering, NO hiding
lake build

echo ""
echo "========================================="
echo "Build completed!"

