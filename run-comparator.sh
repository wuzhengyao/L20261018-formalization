#!/usr/bin/env bash
# Build the development and run the comparator check of one chapter.
#
#   ./run-comparator.sh            # chapter 3 (default)
#   ./run-comparator.sh ch4        # once comparator/ch4/ exists
#   SKIP_BUILD=1 ./run-comparator.sh
#
# Prerequisites
#   * Lean toolchain v4.35.0 (see lean-toolchain; elan installs it automatically)
#   * `lake exe cache get` once, to download prebuilt mathlib oleans
#   * the comparator toolchain on PATH:
#         bash scripts/install-comparator-tools.sh && source .tools/env.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
CH=${1:-ch3}

[ -f "comparator/$CH/config.json" ] || { echo "no comparator/$CH/config.json" >&2; exit 1; }

if [ "$CH" = "ch3" ]; then
  python3 scripts/gen-comparator.py
fi

if [ "${SKIP_BUILD:-0}" != "1" ]; then
  echo "== lake build =="
  lake build
fi

echo "== comparator ($CH) =="
exec lake env comparator "comparator/$CH/config.json"
