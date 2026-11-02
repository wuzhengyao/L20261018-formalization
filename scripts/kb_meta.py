#!/usr/bin/env python3
"""Shared metadata for the generated indexes (`DECLARATIONS.md`, per-directory READMEs).

Single source of truth for: where the development lives, what a declaration line looks
like, what each directory is about, and how a module declares which paper item it
formalises.  Both `gen-declarations.py` and `gen-directory-index.py` import this, so the
two indexes cannot drift apart.
"""
import io
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEV = os.path.join(ROOT, "L20261018")

# An optional attribute list, optional modifiers, one of the six declaration keywords, the
# name.  `(?<![\w'.])` keeps `...Cochains.d_def A` from matching on the `def` inside the
# identifier (a real false positive of the first, unanchored version).
DECL = re.compile(
    r"^(?:\s*@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?<![\w'.])(theorem|lemma|def|abbrev|structure|instance)\s+"
    r"([\w'.]+)"
)

# The anchored scan `DECLARATIONS.md` was historically built with, kept for the count line.
DECL_HISTORICAL = re.compile(
    r"^(?:noncomputable )?(theorem|lemma|def|abbrev|structure|instance)\s+([\w'.]+)"
)

# Anonymous instances (`instance : Foo`) have no name to index; they are counted.
ANON = re.compile(r"^instance\s*:", re.M)

SRC = re.compile(r"@source\s+file=(\S+)\s+locator=(label:\S+|line:\d+)")

DOC = re.compile(r"/-!\s*\n(.*?)-/", re.S)

NS = re.compile(r"^namespace\s+([\w.]+)", re.M)

# What each directory is about.  Keyed by the path below `L20261018/`.
THEMES = {
    "Core": "carriers of the paper's objects; the master abstract statements",
    "Ch2/Brauer": "sec. 2.1 · central simple algebras, Brauer group, crossed and symbol algebras",
    "Ch2/Kummer": "sec. 2.2 · Kummer theory, cup products, the cyclic norm criterion",
    "Ch2/Hensel/Valuation": "sec. 2.4 · valuations, integrality, the uniformizer, Hensel",
    "Ch2/Hensel/ResidueMap": "sec. 2.4 · the residue map, its exact sequence, (R1) and (R2)",
    "Ch2/Hensel/TameSymbol": "sec. 2.4 · the tame symbol and the Merkurjev-Suslin closure",
    "Ch2/Hensel/Inertia": "sec. 2.4 · inertia, K_nr, the cohomological dimension of I",
    "Ch2/Hensel/UnitsCupVanish": "sec. 2.4 · the named hypothesis `UnitsCupVanish` and its discharge",
    "Ch2/Rost": "sec. 2.5 · Rost invariant, Suslin groups, cohomological dimension",
    "Ch3/BiKummer": "sec. 3.1 · the bi-Kummer structure, the rank barrier, the norm image",
    "Ch3/NormImage": "sec. 3.2 · the short exact sequence of the norm image, the dimension formula",
    "Ch4": "sec. 4 · Hensel valuations and ramification in the first slot",
    "Witness": "concrete witnesses (Q_7, F_7((t)), ...) for the nonemptiness obligations",
    "Infra/Cohomology": "general cohomology infrastructure; no single paper statement owns it",
    "Infra/Cohomology/Boundary": "sec. 2.3 · the Hochschild-Serre boundary map, assembled",
    "Infra/Cohomology/Conjugation": "sec. 2.3/2.4 · conjugation invariance of H^1(I, mu_p)",
    "Infra/Cohomology/Coinduced": "sec. 2.3 · coinduced modules, invariants, GS (6.17)",
    "Infra/Cohomology/ResidueLES": "sec. 2.4 · the continuous residue long exact sequence",
    "Infra/Galois": "absolute Galois group carriers and subgroup plumbing",
    "Infra/Algebra": "general algebra: linear algebra, group theory, adjoin-root tooling",
}

# The paper's own structure, for the "paper locator -> modules" table.  Section labels and
# the order of the items inside a section follow `raw/L20261018.tex` (line numbers in the
# comment).  Locators that do *not* occur in `raw/L20261018.tex` are listed separately --
# see note in gen-directory-index.py.
PAPER_ORDER = [
    ("sec. 2.2", ["cor:symbol-cup"]),                                    # tex:753
    ("sec. 2.4", ["prop:prelim-kummer-valuation", "prop:prelim-residue",
                  "eq:prelim-tame"]),                                    # tex:988 1014 1031
    ("sec. 3.1", ["lem:orthogonal", "thm:rank-barrier", "lem:basic-inclusions"]),
    ("sec. 3.2", ["prop:hs-special", "thm:hs-tate-exact-sequences",
                  "thm:dimension"]),                                     # tex:1409 1426 1500
    ("sec. 4", ["lem:basis-change", "lem:ramified-vanishing", "thm:ramified"]),
    ("sec. 4.4 (unnumbered)", ["line:1646"]),
]

# Comparator groups: which paper items the official tool actually re-checks.
COMPARATOR_GROUPS = [
    ("ch3u", "chapter 3, 8 declarations, unconditional at the paper's hypothesis level"),
    ("ch4u", "chapter 4, 7 declarations, unconditional (`d` is constructed)"),
]


PAPER = "raw/L20261018.tex"


def sources(text):
    """[(annotated file, locator)] -- the `file=` field is kept, it is part of the claim."""
    out = set()
    for m in SRC.finditer(text):
        loc = m.group(2)
        out.add((m.group(1), loc[len("label:"):] if loc.startswith("label:") else loc))
    return sorted(out)


# Short names for the sources the development quotes besides the paper itself.  The full
# path is always in `PROVENANCE.tsv`; these are for the tables.
SOURCE_ALIASES = {
    "raw/GilleSzamuely2017.tex": "GS2017",
}


def source_stem(file):
    """`raw/GilleSzamuely2017.tex` -> `GilleSzamuely2017`;  the paper stays implicit."""
    base = os.path.basename(file)
    return base[:-4] if base.endswith(".tex") else base


def display_locator(src):
    """How a locator is shown: bare for the paper, `Source/label` for anything else."""
    file, loc = src
    if file == PAPER:
        return loc
    return f"{SOURCE_ALIASES.get(file, source_stem(file))}/{loc}"


def paper_locators(text):
    """The `@source` locators attached to a module.

    `locator=label:lem:ramified-vanishing` is reported as `lem:ramified-vanishing` (the
    `label:` prefix is the annotation's syntax, not part of the label); a raw line anchor
    stays `line:1646`.
    """
    out = set()
    for m in SRC.finditer(text):
        loc = m.group(2)
        out.add(loc[len("label:"):] if loc.startswith("label:") else loc)
    return sorted(out)


def doc_heading(text):
    """The first `#` line of the module docstring, if any."""
    m = DOC.search(text)
    if not m:
        return ""
    for line in m.group(1).splitlines():
        s = line.strip()
        if s.startswith("#"):
            return s.lstrip("#").strip()
    return ""


def modules():
    """{module: record} for every `.lean` file under `L20261018/`.

    A record is a dict with module, directory, path, lines, paper (locators only),
    sources (list of (file, locator)), heading, ns (list of namespaces),
    decls (list of (name, line, kind)) and anon (int).
    """
    out = {}
    for dirpath, _dirnames, filenames in os.walk(DEV):
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, DEV)[:-len(".lean")]
            text = io.open(path, encoding="utf-8").read()
            decls = []
            for lineno, line in enumerate(text.splitlines(), 1):
                m = DECL.search(line)
                if m:
                    decls.append((m.group(2), lineno, m.group(1)))
            out[rel.replace(os.sep, ".")] = dict(
                module=rel.replace(os.sep, "."),
                directory=os.path.dirname(rel).replace(os.sep, "/") or ".",
                path=path,
                lines=len(text.splitlines()),
                paper=paper_locators(text),
                sources=sources(text),
                heading=doc_heading(text),
                ns=NS.findall(text),
                decls=decls,
                anon=len(ANON.findall(text)),
            )
    return out


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


def write(path, text):
    """Encode first, then atomically replace -- never truncate a file we might fail on."""
    tmp = path + ".tmp"
    with io.open(tmp, "wb") as fh:
        fh.write(text.encode("utf-8"))
    os.replace(tmp, path)
