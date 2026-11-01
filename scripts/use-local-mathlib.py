#!/usr/bin/env python3
"""Point the build at a local mathlib4 checkout, or put the committed lakefile back.

    python3 scripts/use-local-mathlib.py on [/path/to/mathlib4]
    python3 scripts/use-local-mathlib.py off
    python3 scripts/use-local-mathlib.py status

Why this exists: `lakefile.toml` fetches mathlib from GitHub at the pinned commit, which
needs the network and, from cold, a long build.  If that exact commit is already built
locally, the whole repository compiles offline -- but only after two fiddly edits (the
`require` stanza *and* a hand-written `lake-manifest.json`, because `lake build` rejects a
git manifest that no longer matches the lakefile).  Those two edits are what this script
does, with the two checks that make them safe:

* the local checkout's `lean-toolchain` must equal this repository's;
* the local checkout's git HEAD must start with the pinned `rev`.

`lakefile.toml` is a tracked file: `on` overwrites it, so do not commit the result.  `off`
restores it from git and deletes the local manifest.  `status` says which state you are in.
"""
import io
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKEFILE = os.path.join(ROOT, "lakefile.toml")
MANIFEST = os.path.join(ROOT, "lake-manifest.json")

REQ = re.compile(
    r'git = "https://github\.com/leanprover-community/mathlib4"\nrev = "([0-9a-f]{40})"')
# anchored at column 0: the comment block above the stanza also contains `path = ...`
PATH_REQ = re.compile(r'^path = "([^"]+)"', re.M)


def read(path):
    return io.open(path, encoding="utf-8").read()


def write(path, text):
    """Encode first, then replace -- never truncate a file we might fail on."""
    tmp = path + ".tmp"
    with io.open(tmp, "wb") as fh:
        fh.write(text.encode("utf-8"))
    os.replace(tmp, path)


def git_out(cwd, *args):
    return subprocess.run(["git"] + list(args), cwd=cwd, check=True,
                          capture_output=True).stdout.decode().strip()


def fallback_mathlib4():
    for cand in (os.environ.get("MATHLIB4"), os.path.expanduser("~/mathlib4")):
        if cand and os.path.isdir(cand):
            return os.path.abspath(cand)
    return None


def status():
    text = read(LAKEFILE)
    m = PATH_REQ.search(text)
    if m:
        print(f"lakefile.toml: local mathlib at {m.group(1)}")
        print(f"lake-manifest.json: {'present' if os.path.exists(MANIFEST) else 'MISSING'}")
        print("revert with: python3 scripts/use-local-mathlib.py off")
    else:
        m = REQ.search(text)
        pin = m.group(1) if m else "?"
        print(f"lakefile.toml: git mathlib at {pin} (the committed state)")
    return 0


def turn_on(argv):
    m = REQ.search(read(LAKEFILE))
    if not m:
        print("lakefile.toml is not in the committed (git) form -- run `off` first",
              file=sys.stderr)
        return 1
    pin = m.group(1)
    local = os.path.abspath(argv[0]) if argv else fallback_mathlib4()
    if not local or not os.path.isdir(local):
        print("give the path to a mathlib4 checkout: "
              "python3 scripts/use-local-mathlib.py on /path/to/mathlib4", file=sys.stderr)
        return 1

    for needed in ("lean-toolchain", "lake-manifest.json"):
        if not os.path.exists(os.path.join(local, needed)):
            print(f"{local} is not a mathlib4 checkout: it has no {needed}", file=sys.stderr)
            return 1

    # check 1: toolchain
    here = read(os.path.join(ROOT, "lean-toolchain")).strip()
    there = read(os.path.join(local, "lean-toolchain")).strip()
    if here != there:
        print(f"toolchain mismatch: this repository is on {here}, {local} is on {there}",
              file=sys.stderr)
        return 1

    # check 2: the checkout is the pinned commit
    head = git_out(local, "rev-parse", "HEAD")
    if not head.startswith(pin[:12]):
        print(f"{local} is at {head[:12]}, but the lakefile pins {pin[:12]}",
              file=sys.stderr)
        print("refusing to build against a different mathlib than the one the statements "
              "were checked with", file=sys.stderr)
        return 1

    # rewrite the require stanza
    text = read(LAKEFILE)
    new = REQ.sub(f'path = "{local}"', text)
    if new == text:
        print("could not rewrite the mathlib requirement", file=sys.stderr)
        return 1
    write(LAKEFILE, new)

    # hand-write a path manifest
    pkgs = os.path.join(local, ".lake", "packages")

    def config_file(d):
        return "lakefile.lean" if os.path.exists(os.path.join(d, "lakefile.lean")) \
            else "lakefile.toml"

    manifest = json.load(io.open(os.path.join(local, "lake-manifest.json"),
                                 encoding="utf-8"))
    out = []
    for q in manifest["packages"]:
        d = os.path.join(pkgs, q["name"])
        q = dict(q)
        q.update(url=d, type="path", dir=d, subDir=None, scope="", rev="",
                 inputRev="", configFile=config_file(d))
        out.append(q)
    out.append({"url": local, "type": "path", "subDir": None, "scope": "", "rev": "HEAD",
                "name": "mathlib", "manifestFile": "lake-manifest.json", "inputRev": "",
                "inherited": False, "configFile": config_file(local), "dir": local})
    write(MANIFEST, json.dumps({"version": "1.3.0", "packages": out}, indent=1))

    print(f"offline build ready: mathlib at {local} ({head[:12]}, {here})")
    print("lakefile.toml is now modified -- do not commit it; revert with")
    print("    python3 scripts/use-local-mathlib.py off")
    return 0


def turn_off():
    if not REQ.search(read(LAKEFILE)):
        subprocess.run(["git", "checkout", "--", "lakefile.toml"], cwd=ROOT, check=True)
    if os.path.exists(MANIFEST):
        os.remove(MANIFEST)
    print("restored the committed lakefile.toml; removed lake-manifest.json")
    return 0


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    cmd = argv[0]
    if cmd == "status":
        return status()
    if cmd == "on":
        return turn_on(argv[1:])
    if cmd == "off":
        return turn_off()
    print(f"unknown command: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
