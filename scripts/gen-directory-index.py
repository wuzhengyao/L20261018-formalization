#!/usr/bin/env python3
"""Generate the navigation layer: one `README.md` per directory, plus `L20261018/README.md`.

    python3 scripts/gen-directory-index.py            # write the 21 files
    python3 scripts/gen-directory-index.py --check    # compare, exit 1 on drift
    python3 scripts/gen-directory-index.py --report   # print counts only

What the files contain:

* `L20261018/<dir>/README.md` -- the modules of that directory in `StepNNN` order, with the
  paper item each one formalises and the declarations it contributes.  This is the answer to
  "what is in this directory", which a bare file listing does not give.
* `L20261018/README.md` -- the paper -> module map (one row per `@source` locator, in the
  paper's own order), the comparator targets with the module that proves each one, and the
  locators that do not occur in `raw/L20261018.tex` at all.

The comparator table is also a check, not just documentation: every declaration named in a
`comparator/*/Solution.lean` `specs` list must be findable in the development, otherwise
this script fails.  (It matches on the last component of the qualified name and, when the
bare name is ambiguous, on the namespace prefix.)

`--check` makes the whole layer idempotent, so `git status` stays clean after a run.
"""
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb_meta as K

SPEC = re.compile(r"\(`(\w+),\s*``([\w.']+)\)")
STEP = re.compile(r"^Step(\d+)_")


def step_key(rel_file):
    m = STEP.match(os.path.basename(rel_file))
    return (int(m.group(1)) if m else 10 ** 6, rel_file)


def rel_up(directory):
    """`../` repeated enough times to reach the repository root from that directory."""
    return "../" * (directory.count("/") + 2)


def render_dir(directory, mods, depth):
    up = rel_up(directory)
    theme = K.THEMES.get(directory, "")
    files = sorted((m for m in mods if m["directory"] == directory),
                   key=lambda m: step_key(m["module"]))
    shown = sorted({K.display_locator(src) for m in files for src in m["sources"]})
    labels = [p for p in shown if not p.startswith("line:") and "/line:" not in p]
    anchors = [p for p in shown if p not in labels]
    title = f"# `L20261018/{directory}`"
    out = [title + (f" — {theme}" if theme else "") + "\n",
           "\n",
           f"{len(files)} modules.  Part of the development's "
           f"[index](../{'../' * (directory.count('/'))}README.md); see also "
           f"[`DECLARATIONS.md`]({up}DECLARATIONS.md) and "
           f"[`RENAME-MAP.tsv`]({up}RENAME-MAP.tsv).\n",
           "\n"]
    if labels or anchors:
        bits = ", ".join(f"`{p}`" for p in labels)
        if anchors:
            bits += ("; " if bits else "") + f"{len(anchors)} line anchor" \
                    f"{'s' if len(anchors) != 1 else ''}"
        out.append("Source items formalised here: " + bits + ".\n")
        out.append("\n")
    out.append("| module | source item | declarations | lines |\n")
    out.append("|---|---|---|---|\n")
    for m in files:
        base = os.path.basename(m["path"])
        names = [d[0] for d in m["decls"]]
        cell = ", ".join(f"`{n}`" for n in names[:4])
        if len(names) > 4:
            cell += f" (+{len(names) - 4} more)"
        if not names:
            cell = "—"
        src = ", ".join(f"`{K.display_locator(x)}`" for x in m["sources"])
        out.append(f"| [`{base[:-5]}`]({base}) | {src} | {cell} | {m['lines']} |\n")
    return "".join(out)


def provenance_summary():
    """One paragraph from PROVENANCE.tsv, or an honest note that it is not here."""
    path = os.path.join(K.ROOT, "PROVENANCE.tsv")
    if not os.path.exists(path):
        return ("*`PROVENANCE.tsv` is not present*, so the provenance of the `@source` "
                "annotations has not been checked in this checkout.\n")
    rows = [l.split("\t") for l in
            io.open(path, encoding="utf-8").read().splitlines()[1:] if l]
    ok = sum(1 for r in rows if r[3] == "annotated-file")
    elsewhere = [r for r in rows if r[3] == "elsewhere"]
    missing = [r for r in rows if r[3] == "not-found"]
    anchors = sum(1 for r in rows if r[3] == "line-anchor")
    gone = [r for r in rows if r[2] == "MISSING"]
    bits = [f"{ok} labelled items are present in the file their annotation names",
            f"{len(elsewhere)} labelled elsewhere", f"{len(missing)} not found",
            f"{anchors} line anchors (which a label search cannot check)",
            f"{len(gone)} annotation whose file is absent"]
    return ("Every `@source` annotation is checked against the sources in `raw/` by "
            "`scripts/check-provenance.py`, whose verdict is `PROVENANCE.tsv`: " +
            "; ".join(bits) + ".\n")


def render_dev(recs):
    dirs = {}
    for m in recs:
        dirs.setdefault(m["directory"], []).append(m)
    out = ["# `L20261018/` — the development, organised by the paper\n", "\n",
           f"{len(recs)} modules in {len(dirs)} directories.  "
           "[Root README](../README.md) · [`DECLARATIONS.md`](../DECLARATIONS.md) · "
           "[`RENAME-MAP.tsv`](../RENAME-MAP.tsv) · [`PROVENANCE.tsv`](../PROVENANCE.tsv) · "
           "[`WORKFLOW.md`](../WORKFLOW.md)\n", "\n",
           "Every module is a `StepNNN_<slug>` whose number is order preserving inside its\n"
           "directory (so reading upwards reads the proof in the order it was built) and whose\n"
           "slug says what the step proves.  `import L20261018` pulls in everything.\n", "\n",
           "## Directories\n", "\n",
           "| directory | modules | declarations | what is there |\n",
           "|---|---|---|---|\n"]
    for d in sorted(dirs):
        n = len(dirs[d])
        nd = sum(len(m["decls"]) for m in dirs[d])
        out.append(f"| [`{d}/`]({d}/README.md) | {n} | {nd} | {K.THEMES.get(d, '')} |\n")

    # group the annotations by the file they name
    by_file = {}
    for m in recs:
        for src in m["sources"]:
            by_file.setdefault(src[0], {}).setdefault(src[1], []).append(m)

    def links(items):
        return ", ".join(
            f"[`{os.path.basename(mm['path'])[:-5]}`]"
            f"({mm['directory']}/{os.path.basename(mm['path'])})"
            for mm in sorted(items, key=lambda x: step_key(x["module"])))

    def label_table(file, order=None):
        labels = by_file.get(file, {})
        ordered = [l for l in (order or []) if l in labels]
        ordered += sorted(l for l in labels if l not in ordered)
        rows = []
        for label in ordered:
            if label.startswith("line:"):
                rows.append(f"| `{label}` | {links(labels[label])} |\n")
            else:
                rows.append(f"| `{label}` | {links(labels[label])} |\n")
        return "".join(rows), labels

    out.append("\n## Items of `raw/L20261018.tex`\n")
    out.append("\n")
    out.append("The paper's own statements, in the paper's order (the section is the one the\n"
               "label lives in).  A module appears here when its `@source` annotation names\n"
               "that label.  Raw `line:` anchors come last -- statements the paper leaves\n"
               "unnumbered.\n")
    out.append("\n")
    out.append("| paper label | modules |\n")
    out.append("|---|---|\n")
    order = [l for _s, ls in K.PAPER_ORDER for l in ls]
    table, labels = label_table(K.PAPER, order)
    out.append(table)
    section_of = {l: s for s, ls in K.PAPER_ORDER for l in ls}
    # the section column would be useful; emit it as a separate ordered list instead
    out.append("\nSection of each labelled item: " +
               "; ".join(f"`{l}` ({section_of[l]})"
                         for l in order if l in labels and l in section_of) + ".\n")

    for file in sorted(by_file):
        if file == K.PAPER:
            continue
        out.append(f"\n## Items of `{file}`\n")
        out.append("\n")
        alias = K.SOURCE_ALIASES.get(file)
        out.append("Statements the development quotes from this source rather than from the\n"
                   "paper.  The label is shown bare here; in `DECLARATIONS.md` and in the\n"
                   "per-directory tables it is prefixed with the source"
                   + (f", `{alias}/<label>`," if alias else "") +
                   " so that it cannot be\nconfused with a paper label.\n")
        out.append("\n")
        out.append("| label | modules |\n")
        out.append("|---|---|\n")
        table, labels = label_table(file)
        out.append(table)

    out.append("\n## Provenance of the annotations\n")
    out.append("\n")
    out.append(provenance_summary())

    out.append("\n## What the comparators check, and where it lives\n")
    out.append("\n")
    out.append("Taken from the `specs` list of each `comparator/*/Solution.lean`, so this table\n"
               "cannot drift from what the official tool actually re-checks.  The build of this\n"
               "page fails if a target is not a declaration of the development.\n")
    out.append("\n")
    for group, blurb in K.COMPARATOR_GROUPS:
        out.append(f"**`{group}`** — {blurb}\n")
        out.append("\n")
        out.append("| target | declaration | module |\n")
        out.append("|---|---|---|\n")
        for alias, decl, m, line in specs_of(group, recs):
            link = f"[`{os.path.basename(m['path'])[:-5]}`]({m['directory']}/" \
                   f"{os.path.basename(m['path'])})"
            out.append(f"| `{alias}` | `{decl}` (line {line}) | {link} |\n")
        out.append("\n")
    return "".join(out)


BY_SHORT = {}


def specs_of(group, recs):
    """[(alias, qualified declaration, module record, line)] for one comparator group."""
    path = os.path.join(K.ROOT, "comparator", group, "Solution.lean")
    text = io.open(path, encoding="utf-8").read()
    found = SPEC.findall(text)
    if not found:
        raise SystemExit(f"no specs found in {path}")
    rows = []
    for alias, decl in found:
        short = decl.rsplit(".", 1)[-1]
        prefix = decl.rsplit(".", 1)[0] if "." in decl else ""
        cands = BY_SHORT.get(short, [])
        if len(cands) > 1 and prefix and prefix != "L20261018":
            narrow = [c for c in cands if prefix in c[0]["ns"]]
            if narrow:
                cands = narrow
        # the same short name can occur twice in one module (two namespaces): the link is
        # the same, so that is not an ambiguity as far as this table is concerned
        if len({c[0]["module"] for c in cands}) == 1:
            cands = cands[:1]
        if not cands:
            raise SystemExit(f"comparator {group}: declaration {decl} is not in the "
                             f"development (no module declares `{short}`)")
        if len(cands) > 1:
            raise SystemExit(f"comparator {group}: `{decl}` is ambiguous: " +
                             ", ".join(c[0]["module"] for c in cands))
        m, line = cands[0]
        rows.append((alias, decl, m, line))
    return rows


def build_short_index(recs):
    BY_SHORT.clear()
    for m in recs:
        for name, line, _kind in m["decls"]:
            BY_SHORT.setdefault(name, []).append((m, line))


LINK = re.compile(r"\]\(([^)#\s]+)(#[^)]*)?\)")


def check_links(paths):
    bad = []
    for path in paths:
        text = io.open(path, encoding="utf-8").read()
        base = os.path.dirname(path)
        for m in LINK.finditer(text):
            target = m.group(1)
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            full = os.path.normpath(os.path.join(base, target))
            if not os.path.exists(full):
                bad.append(f"{os.path.relpath(path, K.ROOT)}: {target} (no such file)")
                continue
            anchor = m.group(2) or ""
            if anchor.startswith("#L") and anchor[2:].isdigit():
                want = int(anchor[2:])
                got = len(io.open(full, encoding="utf-8").read().splitlines())
                if want < 1 or want > got:
                    bad.append(f"{os.path.relpath(path, K.ROOT)}: {target}{anchor} "
                               f"(file has {got} lines)")
    return bad


def main(argv):
    recs = list(K.modules().values())
    build_short_index(recs)
    dirs = sorted({m["directory"] for m in recs})
    files = {}
    for d in dirs:
        files[os.path.join(K.DEV, d, "README.md")] = render_dir(d, recs, d.count("/") + 1)
    files[os.path.join(K.DEV, "README.md")] = render_dev(recs)

    if "--check-links" in argv:
        bad = check_links(list(files) + [os.path.join(K.ROOT, "DECLARATIONS.md"),
                                         os.path.join(K.ROOT, "README.md"),
                                         os.path.join(K.ROOT, "WORKFLOW.md")])
        if bad:
            print("broken links:\n  " + "\n  ".join(bad), file=sys.stderr)
            return 1
        print("all internal links resolve")
        return 0
    if "--report" in argv:
        print(f"{len(recs)} modules in {len(dirs)} directories; {len(files)} README files")
        return 0
    if "--check" in argv:
        stale = []
        for path, text in files.items():
            old = io.open(path, encoding="utf-8").read() if os.path.exists(path) else ""
            if old != text:
                stale.append(os.path.relpath(path, K.ROOT))
        if stale:
            print("stale: " + ", ".join(sorted(stale)), file=sys.stderr)
            return 1
        print(f"{len(files)} README files are up to date")
        return 0
    for path, text in files.items():
        os.makedirs(os.path.dirname(path), exist_ok=True)
        K.write(path, text)
    print(f"wrote {len(files)} README files ({len(recs)} modules in {len(dirs)} directories)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
