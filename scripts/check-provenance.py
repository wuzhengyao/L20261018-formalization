#!/usr/bin/env python3
"""Check every `@source file=… locator=label:X` annotation against the sources in `raw/`.

    python3 scripts/check-provenance.py            # rewrite PROVENANCE.tsv
    python3 scripts/check-provenance.py --check    # self-test, then compare (exit 1 on drift)
    python3 scripts/check-provenance.py --report   # print the report only
    python3 scripts/check-provenance.py --selftest # just the discriminating-power check

An annotation says "this module formalises the item labelled `X` of file `F`".  This script
checks the second half of that claim: does `F` really contain `\\label{X}`?  If not, it looks
for any other `raw/*.tex` that does, and records where the label actually lives.  That is
how a *provenance* error shows up instead of being inherited: the first version of the
repository index dropped the `file=` field and printed only the label, which made seven
labels look "wrong" because they had been compared against `raw/L20261018.tex` -- they were
in fact pointing at `raw/GilleSzamuely2017.tex` all along.  Losing a field is enough to
manufacture a phantom incident.

`raw/` is not shipped with the repository (only `scratch/…/export-…` is), so the verdict is
committed as `PROVENANCE.tsv`; without `raw/` the script says so and exits 3 rather than
reporting "all good" on data it could not look at.
"""
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb_meta as K

KB_ROOT = os.path.normpath(os.path.join(K.ROOT, "..", ".."))
RAW = os.path.join(KB_ROOT, "raw")
OUT = os.path.join(K.ROOT, "PROVENANCE.tsv")

SOURCE = re.compile(r"@source\s+file=(\S+)\s+locator=(label:(\S+)|line:(\d+))")

# Self-test fixtures: one label that is in a source, one that is nowhere.
KNOWN_LABEL = "lemma-additive-hilbert90"      # raw/GilleSzamuely2017.tex
KNOWN_FILE = "raw/GilleSzamuely2017.tex"
BOGUS_LABEL = "no-such-label-zzz"


def annotations():
    """{(annotated file, locator): set of modules} for every @source annotation."""
    out = {}
    for mod in K.modules().values():
        text = io.open(mod["path"], encoding="utf-8").read()
        for m in SOURCE.finditer(text):
            f = m.group(1)
            loc = m.group(3) if m.group(3) else "line:" + m.group(4)
            out.setdefault((f, loc), set()).add(mod["module"])
    return out


def scan_raw(labels):
    """{label: sorted [raw/*.tex that contain \\label{label}]} -- one pass over the sources."""
    labels = [l for l in labels if l and not l.startswith("line:")]
    if not labels:
        return {}
    pattern = re.compile(r"\\label\{(" + "|".join(re.escape(l) for l in labels) + r")\}")
    found = {}
    for fn in sorted(os.listdir(RAW)):
        if not fn.endswith(".tex"):
            continue
        try:
            text = io.open(os.path.join(RAW, fn), encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        for m in pattern.finditer(text):
            found.setdefault(m.group(1), set()).add(fn)
    return {k: sorted(v) for k, v in found.items()}


def classify(annotated_file, label, found):
    """('annotated-file'|'elsewhere'|'not-found', [other files]) for one annotation."""
    here = os.path.basename(annotated_file)
    hits = found.get(label, [])
    if here in hits:
        return "annotated-file", []
    if hits:
        return "elsewhere", hits
    return "not-found", []


def file_exists(annotated_file):
    """Is the annotated file actually present?  (`raw/…` and `scratch/…` both count.)"""
    return os.path.exists(os.path.join(KB_ROOT, annotated_file))


def build():
    ann = annotations()
    labels = sorted({loc for _f, loc in ann if not loc.startswith("line:")})
    found = scan_raw(labels)
    rows = []
    for (f, loc), mods in sorted(ann.items()):
        exists = "yes" if file_exists(f) else "MISSING"
        if loc.startswith("line:"):
            rows.append((loc, f, exists, "line-anchor", "", str(len(mods))))
            continue
        status, other = classify(f, loc, found)
        rows.append((loc, f, exists, status, ",".join(other), str(len(mods))))
    head = ["locator", "annotated_file", "file_exists", "label_status", "found_in", "modules"]
    text = "\t".join(head) + "\n" + "".join("\t".join(r) + "\n" for r in rows)
    return rows, text


def selftest():
    """The checker must accept a true provenance and reject a false one."""
    found = scan_raw([KNOWN_LABEL, BOGUS_LABEL])
    checks = [
        ("positive: the labelled item is found in its source",
         os.path.basename(KNOWN_FILE) in found.get(KNOWN_LABEL, [])),
        ("negative: an invented label is found nowhere",
         BOGUS_LABEL not in found),
        ("forged provenance is rejected: same label, wrong file",
         classify("raw/L20261018.tex", KNOWN_LABEL, found)
         == ("elsewhere", [os.path.basename(KNOWN_FILE)])),
    ]
    ok = True
    for name, passed in checks:
        print(f"  {'PASS' if passed else 'FAIL'}  {name}")
        ok = ok and passed
    return ok


def main(argv):
    if not os.path.isdir(RAW):
        print(f"{RAW} is not here: this check needs the knowledge-base `raw/` directory "
              f"(the repository does not ship it)", file=sys.stderr)
        return 3
    if "--selftest" in argv:
        ok = selftest()
        print("self-test passed" if ok else "SELF-TEST FAILED -- readings must not be used")
        return 0 if ok else 2
    if "--check" in argv or "--report" in argv:
        if not selftest():
            print("SELF-TEST FAILED -- readings must not be used", file=sys.stderr)
            return 2
    rows, text = build()
    ok = sum(1 for r in rows if r[3] == "annotated-file")
    elsewhere = [r for r in rows if r[3] == "elsewhere"]
    missing = [r for r in rows if r[3] == "not-found"]
    anchors = sum(1 for r in rows if r[3] == "line-anchor")
    gone = [r for r in rows if r[2] == "MISSING"]

    if "--check" in argv:
        old = io.open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if old != text:
            print("PROVENANCE.tsv is STALE", file=sys.stderr)
            return 1
        print(f"PROVENANCE.tsv is up to date ({ok} labels verified in their annotated file, "
              f"{len(elsewhere)} found elsewhere, {len(missing)} not found, {anchors} line "
              f"anchors, {len(gone)} annotations on a file that is absent)")
        return 0
    if "--report" in argv:
        print(f"{ok} labels verified in their annotated file")
        for r in elsewhere:
            print(f"  ELSEWHERE  {r[0]}  claimed {r[1]}  found in {r[3]}")
        for r in missing:
            print(f"  NOT FOUND  {r[0]}  claimed {r[1]}")
        for r in gone:
            print(f"  FILE ABSENT  {r[1]}  ({r[0]}, {r[5]} modules)")
        print(f"{anchors} line anchors (not checkable by label)")
        return 0
    K.write(OUT, text)
    print(f"wrote PROVENANCE.tsv: {ok} verified, {len(elsewhere)} elsewhere, "
          f"{len(missing)} not found, {anchors} line anchors, {len(gone)} on an absent file")
    for r in gone:
        print(f"  FILE ABSENT  {r[1]}  ({r[0]}, {r[5]} modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
