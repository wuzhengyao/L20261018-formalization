#!/usr/bin/env bash
# Judgement-power check for the locally built comparator toolchain.
#
#   bash scripts/validate-comparator-tools.sh
#
# A checker is only trustworthy if it also rejects: this runs one positive and
# several negative controls and prints PASS/FAIL per case (KB rule L43 -- a
# reading without a negative control is not evidence).
#
# Requires comparator, landrun, lean4export on PATH (source .tools/env.sh) and
# Lean 4.35.0 via elan.  Exit code 0 iff every case behaves as expected.
set -uo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
CASE=$ROOT/.tools/smoke
BIN=$ROOT/.tools/bin
PROBE=$ROOT/.tools/_probe_should_not_exist
pass=0; fail=0

ok()  { pass=$((pass+1)); printf 'PASS  %s\n' "$*"; }
bad() { fail=$((fail+1)); printf 'FAIL  %s\n' "$*"; }
check() { local name=$1 want=$2 got=$3; if [ "$got" = "$want" ]; then ok "$name"; else bad "$name (want=$want got=$got)"; fi; }

# ---------------------------------------------------------------- landrun
RIGHTS=(--ro / --rw /dev --rox /usr --rox /bin --rox /lib --rw /tmp)

"$BIN/landrun" "${RIGHTS[@]}" -- bash -c 'cat /proc/self/status >/dev/null' >/dev/null 2>&1
check "landrun strict mode starts (no --best-effort)" 0 $?

rm -f "$PROBE"
"$BIN/landrun" "${RIGHTS[@]}" -- bash -c "touch $PROBE" >/dev/null 2>&1
rc=$?
test ! -e "$PROBE" && [ $rc -ne 0 ] && ok "landrun denies writes outside --rw" || bad "landrun denies writes outside --rw (rc=$rc exists=$(test -e "$PROBE" && echo yes || echo no))"
rm -f "$PROBE"

"$BIN/landrun" "${RIGHTS[@]}" -- timeout 8 curl -s -o /dev/null https://example.com >/dev/null 2>&1
rc=$?
{ [ $rc -eq 7 ] || [ $rc -eq 28 ] || [ $rc -eq 1 ]; } && ok "landrun denies outbound network (curl rc=$rc)" || bad "landrun denies outbound network (curl rc=$rc)"

# --unix is an ABI-v9 feature; on an older kernel it must fail loudly instead of
# silently dropping the ruleset.
out=$("$BIN/landrun" "${RIGHTS[@]}" --unix /tmp/nosock -- /bin/true 2>&1); rc=$?
if [ $rc -eq 0 ]; then ok "landrun --unix accepted (kernel ABI >= 9)"
elif grep -q "requires Landlock ABI v9" <<<"$out"; then ok "landrun --unix rejected with a clear ABI message"
else bad "landrun --unix failed for an unexpected reason: $out"; fi

# ------------------------------------------------------------- comparator
mkdir -p "$CASE"
printf 'leanprover/lean4:v4.35.0\n' > "$CASE/lean-toolchain"
cat > "$CASE/lakefile.toml" <<'EOF'
name = "comparatorsmoke"
version = "0.1.0"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Challenge"
EOF
cat > "$CASE/Challenge.lean" <<'EOF'
theorem todo1 : 1 + 1 = 2 := by sorry
EOF
cat > "$CASE/config.json" <<'EOF'
{"challenge_module": "Challenge", "solution_module": "Solution",
 "theorem_names": ["todo1"],
 "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]}
EOF

run_comparator() { # Solution.lean on stdin -> exit code of comparator
  cat > "$CASE/Solution.lean"
  ( cd "$CASE" && timeout 300 lake env comparator config.json >/tmp/cmp_case.log 2>&1 )
  echo $?
}

rc=$(printf 'theorem todo1 : 1 + 1 = 2 := by decide\n' | run_comparator)
check "comparator accepts a correct solution" 0 "$rc"
grep -q "Your solution is okay!" /tmp/cmp_case.log && ok "comparator prints 'Your solution is okay!'"

rc=$(printf 'theorem todo1 : 2 + 1 = 3 := by decide\n' | run_comparator)
check "comparator rejects a different statement" 1 "$rc"
grep -q "do not match" /tmp/cmp_case.log && ok "reason: statement mismatch reported"

rc=$(printf 'axiom cheat : 1 + 1 = 2\ntheorem todo1 : 1 + 1 = 2 := cheat\n' | run_comparator)
check "comparator rejects a non-permitted axiom" 1 "$rc"
grep -q "Illegal axiom" /tmp/cmp_case.log && ok "reason: illegal axiom reported"

printf '\n%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ]
