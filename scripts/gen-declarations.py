#!/usr/bin/env python3
"""Regenerate `DECLARATIONS.md` from the sources under `L20261018/`.

The index is the entry point for readers: Ctrl-F a declaration (or a keyword) here,
read off its module and line, then open the module.

    python3 scripts/gen-declarations.py            # rewrite DECLARATIONS.md
    python3 scripts/gen-declarations.py --check    # compare, exit 1 on drift
    python3 scripts/gen-declarations.py --report   # print counts only

The index is a *lookup table*: renaming a module moves a declaration's `module` column and
nothing else.  `--check` therefore compares the whole file; the rename invariant used while
restructuring (`git mv` batches) is the set of `(declaration, line)` pairs, which the module
column cannot perturb.

History of the count: the first version of this index was built by an anchored scan
(`^theorem` / `^lemma` / ...), which silently lost every declaration preceded by an
attribute -- 29 of them, overwhelmingly `@[simp] lemma Foo_apply`, i.e. exactly the lemmas
one greps for.  The scan now allows a leading attribute list, so the count is 2636 rather
than the historical 2607.  Both numbers are printed, so the change is visible rather than
silent.
"""
import io
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "L20261018")
OUT = os.path.join(ROOT, "DECLARATIONS.md")

# An optional attribute list, optional modifiers, one of the six declaration keywords, the
# name.  `(?<![\w'.])` keeps `...Cochains.d_def A` from matching on the `def` inside the
# identifier (a real false positive of the first, unanchored version).
DECL = re.compile(
    r"^(?:\s*@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?<![\w'.])(theorem|lemma|def|abbrev|structure|instance)\s+"
    r"([\w'.]+)"
)

# The anchored scan the index was historically built with, kept for the count line.
DECL_HISTORICAL = re.compile(
    r"^(?:noncomputable )?(theorem|lemma|def|abbrev|structure|instance)\s+([\w'.]+)"
)

THEMES = {
    "Core": "carriers of the paper's objects; the master abstract statements",
    "Ch2/Brauer": "sec. 2.1 -- central simple algebras, Brauer group, crossed and symbol algebras",
    "Ch2/Kummer": "sec. 2.2 -- Kummer theory, cup products, the cyclic norm criterion",
    "Ch2/Hensel/Valuation": "sec. 2.4 -- valuations, integrality, the uniformizer, Hensel",
    "Ch2/Hensel/ResidueMap": "sec. 2.4 -- the residue map, its exact sequence, (R1) and (R2)",
    "Ch2/Hensel/TameSymbol": "sec. 2.4 -- the tame symbol and the Merkurjev-Suslin closure",
    "Ch2/Hensel/Inertia": "sec. 2.4 -- inertia, K_nr, the cohomological dimension of I",
    "Ch2/Hensel/UnitsCupVanish": "sec. 2.4 -- the named hypothesis `UnitsCupVanish` and its discharge",
    "Ch2/Rost": "sec. 2.5 -- Rost invariant, Suslin groups, cohomological dimension",
    "Ch3/BiKummer": "sec. 3.1 -- the bi-Kummer structure, the rank barrier, the norm image",
    "Ch3/NormImage": "sec. 3.2 -- the short exact sequence of the norm image, the dimension formula",
    "Ch4": "sec. 4 -- Hensel valuations and ramification in the first slot",
    "Witness": "concrete witnesses (Q_7, F_7((t)), ...) for the nonemptiness obligations",
    "Infra/Cohomology": "general cohomology infrastructure; no single paper statement owns it",
    "Infra/Cohomology/Boundary": "sec. 2.3 -- the Hochschild-Serre boundary map, assembled",
    "Infra/Cohomology/Conjugation": "sec. 2.3/2.4 -- conjugation invariance of H^1(I, mu_p)",
    "Infra/Cohomology/Coinduced": "sec. 2.3 -- coinduced modules, invariants, GS (6.17)",
    "Infra/Cohomology/ResidueLES": "sec. 2.4 -- the continuous residue long exact sequence",
    "Infra/Galois": "absolute Galois group carriers and subgroup plumbing",
    "Infra/Algebra": "general algebra: linear algebra, group theory, adjoin-root tooling",
}


ANON = re.compile(r"^instance\s*:", re.M)

SRC = re.compile(r"@source\s+file=(\S+)\s+locator=(label:\S+|line:\d+)")


def paper_locators(text):
    """The `@source` locators attached to a module, e.g. `lem:ramified-vanishing`."""
    return sorted({m.group(2) for m in SRC.finditer(text)})


def scan():
    """(rows, modules_by_dir, anon) -- one row per *named* declaration.

    Anonymous instances (`instance : Foo`) carry no name to look up, so they are only
    counted: the count is printed in the header instead of being dropped silently.
    """
    rows = []
    modules_by_dir = {}
    anon = 0
    for dirpath, _dirnames, filenames in os.walk(DEV):
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, DEV)[:-len(".lean")]
            module = rel.replace(os.sep, ".")
            directory = os.path.dirname(rel).replace(os.sep, "/") or "."
            text = io.open(path, encoding="utf-8").read()
            modules_by_dir.setdefault(directory, set()).add(module)
            anon += len(ANON.findall(text))
            paper = "; ".join(paper_locators(text))
            for lineno, line in enumerate(text.splitlines(), 1):
                m = DECL.search(line)
                if m:
                    rows.append((m.group(2), module, lineno, directory, m.group(1), paper))
    return rows, modules_by_dir, anon


def scan_historical_count():
    n = 0
    for dirpath, _dirnames, filenames in os.walk(DEV):
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            with io.open(os.path.join(dirpath, fn), encoding="utf-8") as fh:
                for line in fh:
                    if DECL_HISTORICAL.search(line):
                        n += 1
    return n


def render(rows, historical=None, modules_by_dir=None, anon=0):
    modules = sorted({r[1] for r in rows})
    all_modules = sorted({m for ms in (modules_by_dir or {}).values() for m in ms})
    dirs = {}
    for name, module, _line, directory, _kind, _paper in rows:
        d = dirs.setdefault(directory, [0, set()])
        d[0] += 1
        d[1].add(module)
    for directory, mods in (modules_by_dir or {}).items():
        dirs.setdefault(directory, [0, set()])
        dirs[directory][1] = set(mods)

    with_paper = len({r[1] for r in rows if r[5]})
    out = []
    out.append("# Declaration index — every declaration, its module and line\n")
    out.append("\n")
    out.append("Generated from the sources by `scripts/gen-declarations.py`.  Use this page to "
               "locate a result: `Ctrl-F` the declaration name (or a keyword) here, then open "
               "the module named in the second column.\n")
    out.append("\n")
    out.append(f"**{len(rows)} declarations in {len(all_modules)} modules.**\n")
    out.append("\n")
    notes = []
    if anon:
        notes.append(f"{anon} further declarations are anonymous instances "
                     f"(`instance : Foo`), which have no name to look up and so are only "
                     f"counted")
    if historical is not None and historical != len(rows):
        notes.append(f"the historical anchored scan of 2026-11-08 indexed {historical} of "
                     f"them, losing the {len(rows) - historical} that are preceded by an "
                     f"attribute such as `@[simp]`")
    if notes:
        out.append("Notes: " + "; ".join(notes) + ".\n")
        out.append("\n")
    out.append("## Where to look\n")
    out.append("\n")
    out.append("The module names carry the theme; the directory part follows the paper's own "
               "structure (`Ch2` = preliminaries, `Ch3`, `Ch4`), with `Infra/` for the general "
               "tooling that no single paper statement owns.  The `paper` column of the "
               "index gives the `@source` locator attached to the module, when the module "
               f"carries one ({with_paper} modules do).\n")
    out.append("\n")
    out.append("| directory | modules | declarations | theme |\n")
    out.append("|---|---|---|---|\n")
    for directory in sorted(dirs):
        count, mods = dirs[directory]
        theme = THEMES.get(directory, "")
        out.append(f"| `{directory}/` | {len(mods)} | {count} | {theme} |\n")
    out.append("\n")
    out.append("## Index\n")
    out.append("\n")
    out.append("| declaration | module | line | paper |\n")
    out.append("|---|---|---|---|\n")
    for name, module, line, _directory, _kind, paper in sorted(
            rows, key=lambda r: (r[0], r[1], r[2])):
        cell = "" if not paper else "`" + paper + "`"
        out.append(f"| `{name}` | `L20261018.{module}` | {line} | {cell} |\n")
    return "".join(out)


def main(argv):
    rows, modules_by_dir, anon = scan()
    historical = scan_historical_count()
    text = render(rows, historical, modules_by_dir, anon)
    if "--report" in argv:
        print(f"{len(rows)} declarations in "
              f"{len({m for ms in modules_by_dir.values() for m in ms})} modules, "
              f"{anon} anonymous instances, {historical} at the historical column-0 scan")
        return 0
    if "--pairs" in argv:
        for name, module, line, _directory, _kind, _paper in sorted(rows):
            print(f"{name}\t{line}\t{module}")
        return 0
    if "--check" in argv:
        old = io.open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if old == text:
            print("DECLARATIONS.md is up to date")
            return 0
        print("DECLARATIONS.md is STALE", file=sys.stderr)
        return 1
    # write to a temp file first, then replace (never truncate the target)
    tmp = OUT + ".tmp"
    data = text.encode("utf-8")
    with io.open(tmp, "wb") as fh:
        fh.write(data)
    os.replace(tmp, OUT)
    print(f"wrote DECLARATIONS.md: {len(rows)} declarations, {anon} anonymous instances, "
          f"{len({m for ms in modules_by_dir.values() for m in ms})} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
