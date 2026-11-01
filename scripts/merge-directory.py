#!/usr/bin/env python3
"""Merge the `StepNNN_*.lean` modules of one directory into a single module.

    python3 scripts/merge-directory.py Ch2/Rost        # merge one directory
    python3 scripts/merge-directory.py --list          # show the directories and sizes
    python3 scripts/merge-directory.py --all           # merge everything (see below)

Why the merge is structured the way it is
-----------------------------------------
A naive concatenation of the parts does not compile: `open`, `set_option`, `variable` and
`local` are *scoped* commands, so in one file the `open` of part 1 keeps applying to part 2,
and a name like `GaloBase.cup` then resolves somewhere else ("Unknown identifier", not a
missing definition).  So every part is wrapped in its own `section … end`, which reproduces
exactly the scope it had as a standalone file, and every part's `import` lines are hoisted to
the top (Lean only allows imports there).  Parts that rely on Lean closing a namespace at
end-of-file are re-balanced explicitly, otherwise the *next* part would be nested inside the
previous part's namespace and its declarations would be called `L20261018.L20261018.foo`.

Each part keeps its `/-! … -/` docstring, so the mathematical record is untouched; a
`/- === <original module> === -/` marker plus a section index in the file header make the
merged module navigable.

The old files are removed with `git rm`, so the history follows the rename.

**What this tool cannot do.**  It merges one directory.  Merging *every* topic directory
does not work: Lean rejects an import cycle, and the quotient of the module graph by the
topic directories is strongly connected (19 of the 20 directories form one component; see
`scripts/dependency-layers.py`).  A one-directory trial (`Ch2/Rost`, whose two parts do not
depend on each other) compiles; the full attempt was reverted.  Cycle-free options are
"merge nothing" or "merge the whole strongly connected component", and the second one is a
single ~68k-line module.
"""
import io
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb_meta as K

STEP = re.compile(r"^Step(\d+)_")
OPEN = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)?(namespace|section|mutual)\b")
CLOSE = re.compile(r"^end\b")


def step_key(path):
    m = STEP.match(os.path.basename(path))
    return (int(m.group(1)) if m else 10 ** 6, os.path.basename(path))


def strip_comments(text):
    """Replace comments by spaces, keeping newlines, so a line scan sees only code.

    Lean block comments nest (`/- … /- … -/ … -/`), and a block can open and close on the
    same line; the earlier line-by-line version got both cases wrong and invented three
    `end`s for a part that was perfectly balanced.
    """
    out = []
    depth = 0
    i, n = 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif depth > 0 and two == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif depth > 0 and two == "-/":
            depth -= 1
            out.append("  ")
            i += 2
        elif depth == 0 and two == "--":
            j = text.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def balance(body_lines):
    """Net number of scopes left open by these lines."""
    depth = 0
    for line in strip_comments("\n".join(body_lines)).splitlines():
        s = line.strip()
        if not s:
            continue
        if OPEN.match(s):
            depth += 1
        elif CLOSE.match(s):
            depth -= 1
    return depth


def split_imports(text):
    lines = text.splitlines()
    imports = [l for l in lines if l.startswith("import ")]
    body = [l for l in lines if not l.startswith("import ")]
    while body and not body[0].strip():
        body.pop(0)
    return imports, body


def merge_one(directory, dry_run=False):
    src = os.path.join(K.DEV, *directory.split("/"))
    parts = sorted((os.path.join(src, fn) for fn in os.listdir(src) if fn.endswith(".lean")),
                   key=step_key)
    if not parts:
        print(f"{directory}: no .lean files", file=sys.stderr)
        return 1
    if len(parts) == 1:
        print(f"{directory}: already a single module -- skipped")
        return 0

    imported, chunks, meta = [], [], []
    for path in parts:
        name = os.path.basename(path)[:-5]
        imports, body = split_imports(io.open(path, encoding="utf-8").read())
        for imp in imports:
            if imp.startswith("import L20261018." + directory.replace("/", ".")):
                continue                      # internal: same file now
            if imp not in imported:
                imported.append(imp)
        net = balance(body)
        chunks.append((name, body, net))
        meta.append((name, len(body), net))

    # header with a section index; the table has one row per part, so its line count does
    # not depend on the numbers and the offsets can be computed before filling them in
    def header(offsets):
        h = ["/-!",
             f"# `L20261018/{directory}` — {K.THEMES.get(directory, '')}",
             "",
             f"Merged from the {len(chunks)} proof-step modules that used to live in",
             f"`L20261018/{directory}/`, in their original order.  Each part is marked",
             "`/- === <original module> === -/` and wrapped in its own `section … end`, which",
             "reproduces exactly the `open` / `set_option` / `variable` scope it had as a",
             "standalone file (a plain concatenation would leak `open` across parts and change",
             "name resolution).",
             "",
             "Section index (line numbers are into this file):",
             "",
             "| part | lines |",
             "|---|---|"]
        for (name, _n, _net), (start, end) in zip(chunks, offsets):
            h.append(f"| `{name}` | {start}–{end} |")
        h += ["-/", ""]
        return h

    body_lines = []
    for name, body, net in chunks:
        body_lines.append(f"/- === {name} === -/")
        body_lines.append("section")
        body_lines.extend(body)
        body_lines.extend(["end"] * max(net, 0))
        body_lines.append("end")
        body_lines.append("")

    # offsets: imports, blank, header, then the parts
    header_lines = header([(0, 0)] * len(chunks))
    base = len(imported) + 1 + len(header_lines)
    offsets, cursor = [], base + 1
    for name, body, net in chunks:
        start = cursor
        cursor += 2 + len(body) + max(net, 0) + 1 + 1   # end markers + blank line
        offsets.append((start, cursor - 3))

    out = list(imported) + [""] + header(offsets) + body_lines
    text = "\n".join(out).rstrip("\n") + "\n"

    target = os.path.join(K.DEV, *directory.split("/")) + ".lean"
    print(f"{directory}: {len(parts)} modules -> {os.path.relpath(target, K.ROOT)} "
          f"({len(text.splitlines())} lines)")
    if dry_run:
        return 0
    K.write(target, text)
    for path in parts:
        subprocess.run(["git", "rm", "-q", "-f", os.path.relpath(path, K.ROOT)],
                       cwd=K.ROOT, check=True)
    old_dir = os.path.join(K.DEV, *directory.split("/"))
    if os.path.isdir(old_dir) and not os.listdir(old_dir):
        os.rmdir(old_dir)
    return 0


def fix_imports(directory):
    """Point every importer of a part at the merged module."""
    prefix = "import L20261018." + directory.replace("/", ".") + "."
    merged = "import L20261018." + directory.replace("/", ".")
    changed = 0
    for dirpath, _dirs, files in os.walk(K.ROOT):
        if "/.lake" in dirpath or "/.git" in dirpath:
            continue
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            text = io.open(path, encoding="utf-8").read()
            lines = text.splitlines()
            # only *direct* children: `…Infra.Cohomology.` must not swallow
            # `…Infra.Cohomology.Boundary.Step001`, which is a different module
            def is_child(l):
                return l.startswith(prefix) and "." not in l[len(prefix):]
            if not any(is_child(l) for l in lines):
                continue
            out, added = [], False
            for l in lines:
                if is_child(l):
                    if not added:
                        out.append(merged)
                        added = True
                    continue
                out.append(l)
            K.write(path, "\n".join(out) + "\n")
            changed += 1
    return changed


def directories():
    out = {}
    for dirpath, _dirs, files in os.walk(K.DEV):
        n = sum(1 for f in files if f.endswith(".lean"))
        if n:
            out[os.path.relpath(dirpath, K.DEV).replace(os.sep, "/")] = n
    return out


def main(argv):
    if "--list" in argv:
        for d, n in sorted(directories().items()):
            print(f"{n:4d}  {d}")
        return 0
    dry = "--dry-run" in argv
    args = [a for a in argv if not a.startswith("--")]
    if "--all" in argv:
        # smallest first: a mistake costs the least
        targets = [d for d, _n in sorted(directories().items(), key=lambda kv: kv[1])]
    elif args:
        targets = args
    else:
        print(__doc__)
        return 2
    rc = 0
    for d in targets:
        rc |= merge_one(d, dry_run=dry)
        if not dry:
            n = fix_imports(d)
            if n:
                print(f"  importers updated: {n}")
    if not dry:
        print("run `lake build` next")
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
