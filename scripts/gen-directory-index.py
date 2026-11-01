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
    papers = sorted({p for m in files for p in m["paper"]})
    title = f"# `L20261018/{directory}`"
    out = [title + (f" — {theme}" if theme else "") + "\n",
           "\n",
           f"{len(files)} modules.  Part of the development's "
           f"[index](../{'../' * (directory.count('/'))}README.md); see also "
           f"[`DECLARATIONS.md`]({up}DECLARATIONS.md) and "
           f"[`RENAME-MAP.tsv`]({up}RENAME-MAP.tsv).\n",
           "\n"]
    labels = [p for p in papers if not p.startswith("line:")]
    anchors = [p for p in papers if p.startswith("line:")]
    if labels or anchors:
        bits = ", ".join(f"`{p}`" for p in labels)
        if anchors:
            bits += ("; " if bits else "") + f"{len(anchors)} raw line anchor" \
                    f"{'s' if len(anchors) != 1 else ''}"
        out.append("Paper items formalised here: " + bits + ".\n")
        out.append("\n")
    out.append("| module | paper | declarations | lines |\n")
    out.append("|---|---|---|---|\n")
    for m in files:
        base = os.path.basename(m["path"])
        names = [d[0] for d in m["decls"]]
        shown = ", ".join(f"`{n}`" for n in names[:4])
        if len(names) > 4:
            shown += f" (+{len(names) - 4} more)"
        if not names:
            shown = "—"
        paper = ", ".join(f"`{p}`" for p in m["paper"]) or ""
        out.append(f"| [`{base[:-5]}`]({base}) | {paper} | {shown} | {m['lines']} |\n")
    return "".join(out)


def render_dev(recs):
    dirs = {}
    for m in recs:
        dirs.setdefault(m["directory"], []).append(m)
    out = ["# `L20261018/` — the development, organised by the paper\n", "\n",
           f"{len(recs)} modules in {len(dirs)} directories.  "
           "[Root README](../README.md) · [`DECLARATIONS.md`](../DECLARATIONS.md) · "
           "[`RENAME-MAP.tsv`](../RENAME-MAP.tsv) · "
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

    # paper locator -> modules
    by_label = {}
    for m in recs:
        for p in m["paper"]:
            by_label.setdefault(p, []).append(m)

    def links(label):
        return ", ".join(
            f"[`{os.path.basename(mm['path'])[:-5]}`]"
            f"({mm['directory']}/{os.path.basename(mm['path'])})"
            for mm in sorted(by_label[label], key=lambda x: step_key(x["module"])))

    section_of = {}
    for section, labels in K.PAPER_ORDER:
        for label in labels:
            section_of[label] = section
    named = [p for p in by_label if not p.startswith("line:")]
    if not by_label:
        raise SystemExit("no @source locator found at all -- refusing to write empty tables")
    if not named:
        raise SystemExit("no labelled paper item found -- the `label:` prefix is probably "
                         "not being stripped (an empty table must not pass silently)")
    ordered = [l for _s, ls in K.PAPER_ORDER for l in ls if l in by_label]
    ordered += sorted(p for p in named if p not in ordered)

    out.append("\n## Paper items -> modules\n")
    out.append("\n")
    out.append("The locator is the label of the statement in `raw/L20261018.tex`; a module\n"
               "carries it when it formalises that statement.  Rows for labelled statements\n"
               "come in the paper's own order, then the raw line anchors (statements the paper\n"
               "leaves unnumbered or that a module picks up mid-paragraph).\n")
    out.append("\n")
    out.append("### Labelled statements\n")
    out.append("\n")
    out.append("| paper | section | modules |\n")
    out.append("|---|---|---|\n")
    for label in ordered:
        sec = section_of.get(label, "")
        out.append(f"| `{label}` | {sec} | {links(label)} |\n")
    anchors = sorted((p for p in by_label if p.startswith("line:")),
                     key=lambda p: int(p.split(":")[1]))
    if anchors:
        out.append("\n### Line anchors into `raw/L20261018.tex`\n")
        out.append("\n")
        out.append("| anchor | modules |\n")
        out.append("|---|---|\n")
        for label in anchors:
            out.append(f"| `{label}` | {links(label)} |\n")

    out.append("\n## Locators that are not in `raw/L20261018.tex`\n")
    out.append("\n")
    out.append("`grep` over the whole of `raw/L20261018.tex` gives 0 hits for each of these,\n"
               "while the docstrings of the modules below name them as Gille-Soule (`GS`) items:\n"
               "the `file=` field of those `@source` annotations is wrong, not the label.  They\n"
               "are recorded here rather than edited away (`∅-citation-needed`).\n")
    out.append("\n")
    out.append("| locator | modules |\n")
    out.append("|---|---|\n")
    for label in K.NOT_IN_PAPER:
        if label in by_label:
            out.append(f"| `{label}` | {links(label)} |\n")

    # comparator targets
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
