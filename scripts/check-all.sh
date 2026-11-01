#!/usr/bin/env bash
# Run every gate of this repository in one go, and say PASS/FAIL per gate.
#
#   bash scripts/check-all.sh            # everything (build + comparators + docs)
#   bash scripts/check-all.sh --fast     # the documentation gates only (a few seconds)
#   bash scripts/check-all.sh --no-build # skip `lake build`, keep the comparator runs
#
# Gates
#   1  lake build                      the development compiles (0 error)
#   2  comparator ch3 / ch3u / ch4u    the official tool re-checks the statements
#   3  comparator toolchain self-test   positive + negative controls on the tool itself
#   4  DECLARATIONS.md                 current (gen-declarations.py --check)
#   5  directory indexes               current (gen-directory-index.py --check)
#   6  links in the generated pages    resolve, and `#Lnn` is inside the file
#   7  @source provenance              each label is in the file the annotation names
#                                      (SKIP when the knowledge-base `raw/` is not here)
#
# Exit code 0 iff every gate that ran passed.  A gate that cannot run at all is reported
# as SKIP with the reason -- never silently dropped (a skip is not a pass).
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

FAST=0; BUILD=1
for arg in "$@"; do
  case "$arg" in
    --fast) FAST=1 ;;
    --no-build) BUILD=0 ;;
    -h|--help) sed -n '2,18p' "$0"; exit 0 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

pass=0; fail=0; skip=0
ok()   { pass=$((pass+1)); printf 'PASS  %s\n' "$*"; }
bad()  { fail=$((fail+1)); printf 'FAIL  %s\n' "$*"; }
miss() { skip=$((skip+1)); printf 'SKIP  %s\n' "$*"; }

# ---------------------------------------------------------------- build
if [ "$FAST" = 1 ]; then
  miss "lake build (--fast)"
elif [ "$BUILD" = 1 ]; then
  echo "== gate 1: lake build =="
  if lake build > "$ROOT/.lake/check-all-build.log" 2>&1; then
    ok "lake build (log: .lake/check-all-build.log)"
  else
    bad "lake build -- see .lake/check-all-build.log"
  fi
else
  miss "lake build (--no-build)"
fi

# ---------------------------------------------------------------- comparators
if [ "$FAST" = 1 ]; then
  miss "comparator ch3/ch3u/ch4u (--fast)"
else
  echo "== gate 2: comparator groups =="
  for g in ch3 ch3u ch4u; do
    if [ ! -f "comparator/$g/config.json" ]; then
      miss "comparator $g (no config.json)"
      continue
    fi
    out=$(SKIP_BUILD=1 ./run-comparator.sh "$g" 2>&1)
    if printf '%s' "$out" | grep -q 'Your solution is okay!'; then
      ok "comparator $g"
    else
      bad "comparator $g -- see the output of ./run-comparator.sh $g"
      printf '%s\n' "$out" | tail -5
    fi
  done
fi

# ---------------------------------------------------------------- tool self-test
if [ "$FAST" = 1 ]; then
  miss "comparator toolchain self-test (--fast)"
elif [ -x ".tools/bin/comparator" ] || command -v comparator >/dev/null 2>&1; then
  echo "== gate 3: comparator toolchain self-test =="
  out=$(bash scripts/validate-comparator-tools.sh 2>&1)
  if printf '%s' "$out" | grep -q '10 passed, 0 failed'; then
    ok "toolchain self-test (10 passed, 0 failed)"
  else
    bad "toolchain self-test -- $(printf '%s' "$out" | tail -1)"
  fi
else
  miss "toolchain self-test (comparator not on PATH; source .tools/env.sh first)"
fi

# ---------------------------------------------------------------- documentation
echo "== gate 4-6: generated documentation =="
if python3 scripts/gen-declarations.py --check >/dev/null 2>&1; then
  ok "DECLARATIONS.md is current"
else
  bad "DECLARATIONS.md is stale -- run python3 scripts/gen-declarations.py"
fi
if python3 scripts/gen-directory-index.py --check >/dev/null 2>&1; then
  ok "directory indexes are current"
else
  bad "directory indexes are stale -- run python3 scripts/gen-directory-index.py"
fi
if out=$(python3 scripts/gen-directory-index.py --check-links 2>&1); then
  ok "all internal links resolve"
else
  bad "broken links -- ${out}"
fi

# ---------------------------------------------------------------- provenance
echo "== gate 7: @source provenance =="
out=$(python3 scripts/check-provenance.py --check 2>&1)
case $? in
  0) ok "provenance of the @source annotations" ;;
  3) miss "provenance (needs the knowledge-base raw/ directory, not shipped here)" ;;
  *) bad "provenance -- ${out}" ;;
esac

# ---------------------------------------------------------------- summary
printf '\n%d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
[ "$fail" -eq 0 ]
