#!/usr/bin/env bash
# Build the comparator toolchain (comparator + lean4export + landrun) locally.
#
#   bash scripts/install-comparator-tools.sh
#
# Pins
#   comparator   v4.35.0  (leanprover/comparator)          -- Lean 4.35.0
#   lean4export  v4.35.0  (leanprover/lean4export)         -- Lean 4.35.0
#   landrun      v0.1.17  (Zouuup/landrun) + ABI patch     -- patched build
#
# Why the patch: landrun >= v0.1.17 links go-landlock v0.9, whose handled
# access set includes the ABI-v9 right resolve_unix.  On any kernel older than
# Linux 7.1 (this host: 6.17, Landlock ABI v7) upstream landrun refuses to
# start with
#     missing kernel Landlock support. Got Landlock ABI v7, wanted {Landlock V9; ...}
# comparator happens to pass --best-effort, which downgrades silently, but a
# plain `landrun` invocation does not work and `--unix` would silently disable
# the whole ruleset.  scripts/patches/landrun-v0.1.17-abi-adaptive.patch makes
# landrun probe the kernel ABI and handle exactly the rights it supports, and
# reject --unix with a clear error below ABI v9.
#
# Prerequisites: elan/lake with the project's toolchain (v4.35.0), Go >= 1.24,
# git, curl.  Internet access to github.com (and a reachable Go module proxy:
# this host cannot reach proxy.golang.org, so goproxy.cn is used; override with
# GOPROXY=...).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TOOLS=$ROOT/.tools
SRC=$TOOLS/src
BIN=$TOOLS/bin
COMPARATOR_REV=${COMPARATOR_REV:-v4.35.0}
LEAN4EXPORT_REV=${LEAN4EXPORT_REV:-v4.35.0}
LANDRUN_REV=${LANDRUN_REV:-v0.1.17}
GO_BIN=${GO_BIN:-$TOOLS/go/bin/go}
export GOMODCACHE=${GOMODCACHE:-$TOOLS/gomodcache}
export GOPATH=${GOPATH:-$TOOLS/gopath}
export GOCACHE=${GOCACHE:-$TOOLS/gocache}
export CGO_ENABLED=0
export GOPROXY=${GOPROXY:-https://goproxy.cn,direct}

log() { printf '[%s] %s\n' "$(date -u +%H:%M:%SZ)" "$*"; }
mkdir -p "$SRC" "$BIN"

# ---------------------------------------------------------------- lean4export
if [ ! -d "$SRC/lean4export/.git" ]; then
  git clone --depth 1 --branch "$LEAN4EXPORT_REV" \
    https://github.com/leanprover/lean4export "$SRC/lean4export"
fi
log "building lean4export $LEAN4EXPORT_REV"
( cd "$SRC/lean4export" && lake build lean4export )

# ------------------------------------------------------------------ comparator
if [ ! -d "$SRC/comparator/.git" ]; then
  git clone --depth 1 --branch "$COMPARATOR_REV" \
    https://github.com/leanprover/comparator "$SRC/comparator"
fi
# Depend on the local lean4export checkout instead of fetching `master`.
python3 - "$SRC/comparator/lakefile.toml" "$SRC/lean4export" <<'PY'
import re, sys
path, exp = sys.argv[1], sys.argv[2]
t = open(path).read()
blocks = re.split(r'(?m)^(?=\[\[)', t)
keep = [b for b in blocks
        if not (b.startswith('[[require]]') and re.search(r'name\s*=\s*"lean4export"', b))]
if 'path = "%s"' % exp not in t:
    t = ''.join(keep).rstrip('\n') + '\n\n[[require]]\nname = "lean4export"\npath = "%s"\n' % exp
    open(path, 'w').write(t)
PY
log "building comparator $COMPARATOR_REV"
( cd "$SRC/comparator" && rm -f lake-manifest.json && lake build comparator )

# --------------------------------------------------------------------- landrun
if [ ! -d "$SRC/landrun-src/.git" ]; then
  git clone https://github.com/Zouuup/landrun "$SRC/landrun-src"
fi
( cd "$SRC/landrun-src"
  git checkout -q "$LANDRUN_REV"
  if ! git diff --quiet; then git checkout -q -- .; fi
  patch -p1 --forward < "$ROOT/scripts/patches/landrun-v0.1.17-abi-adaptive.patch" >/dev/null
)
log "building landrun $LANDRUN_REV + ABI patch (go: $("$GO_BIN" version | awk '{print $3}'))"
( cd "$SRC/landrun-src" && "$GO_BIN" build -trimpath -o "$BIN/landrun-abi" ./cmd/landrun )

# ------------------------------------------------------------------- install
ln -sfn ../src/comparator/.lake/build/bin/comparator  "$BIN/comparator"
ln -sfn ../src/lean4export/.lake/build/bin/lean4export "$BIN/lean4export"
ln -sfn landrun-abi                                    "$BIN/landrun"

log "installed:"
"$BIN/comparator" 2>&1 | head -1 || true
"$BIN/lean4export" 2>&1 | head -1 || true
"$BIN/landrun" --version
( cd "$BIN" && sha256sum comparator landrun-abi lean4export > SHA256SUMS.tmp && mv SHA256SUMS.tmp SHA256SUMS )
log "sha256: $(tr '\n' ' ' < "$BIN/SHA256SUMS")"
log "done -- source .tools/env.sh for PATH"
