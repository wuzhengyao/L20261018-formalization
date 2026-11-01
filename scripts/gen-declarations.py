#!/usr/bin/env python3
"""Regenerate `DECLARATIONS.md` -- every declaration, its module, line and paper item.

    python3 scripts/gen-declarations.py            # rewrite DECLARATIONS.md
    python3 scripts/gen-declarations.py --check    # compare, exit 1 on drift
    python3 scripts/gen-declarations.py --report   # print counts only
    python3 scripts/gen-declarations.py --pairs    # name<TAB>line<TAB>module, for diffing

The index is a *lookup table*: renaming a module moves a declaration's `module` column and
nothing else.  `--check` compares the whole file; the invariant used while restructuring
the tree (the `git mv` pass of 2026-11-08) was the set of `(declaration, line)` pairs,
which the module column cannot perturb.

History of the count: the first version of this index was built by an anchored scan
(`^theorem` / `^lemma` / ...), which silently lost every declaration preceded by an
attribute -- 29 of them, overwhelmingly `@[simp] lemma Foo_apply`, i.e. exactly the lemmas
one greps for.  The scan now allows a leading attribute list, so the count is 2636 rather
than the historical 2607.  Both numbers are printed, so the change is visible rather than
silent.  Anonymous instances (`instance : Foo`) have no name to look up: they are counted
in the header rather than dropped.

The scan itself lives in `scripts/kb_meta.py`, shared with `gen-directory-index.py`.
"""
import io
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb_meta as K

OUT = os.path.join(K.ROOT, "DECLARATIONS.md")


def scan():
    """(rows, modules_by_dir, anon) -- one row per *named* declaration."""
    rows = []
    modules_by_dir = {}
    anon = 0
    for mod in K.modules().values():
        modules_by_dir.setdefault(mod["directory"], set()).add(mod["module"])
        anon += mod["anon"]
        paper = "; ".join(K.display_locator(src) for src in mod["sources"])
        rel = os.path.relpath(mod["path"], K.ROOT).replace(os.sep, "/")
        for name, lineno, kind in mod["decls"]:
            rows.append((name, mod["module"], lineno, mod["directory"], kind, paper, rel))
    return rows, modules_by_dir, anon


def render(rows, historical=None, modules_by_dir=None, anon=0):
    all_modules = sorted({m for ms in (modules_by_dir or {}).values() for m in ms})
    dirs = {}
    for name, module, _line, directory, _kind, _paper, _rel in rows:
        d = dirs.setdefault(directory, [0, set()])
        d[0] += 1
        d[1].add(module)
    for directory, mods in (modules_by_dir or {}).items():
        dirs.setdefault(directory, [0, set()])
        dirs[directory][1] = set(mods)

    with_paper = len({r[1] for r in rows if r[5]})
    occurrences = {}
    for r in rows:
        occurrences[r[0]] = occurrences.get(r[0], 0) + 1
    repeated = sorted(n for n, c in occurrences.items() if c > 1)
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
    if repeated:
        notes.append(f"{len(repeated)} names occur more than once because they live in "
                     f"different namespaces ({', '.join('`' + n + '`' for n in repeated[:6])}"
                     f"{', ...' if len(repeated) > 6 else ''}); the index records the short "
                     f"name, so every occurrence is listed with its own line -- disambiguate "
                     f"by the module and line columns")
    if notes:
        out.append("Notes: " + "; ".join(notes) + ".\n")
        out.append("\n")
    out.append("## Where to look\n")
    out.append("\n")
    out.append("The module names carry the theme; the directory part follows the paper's own "
               "structure (`Ch2` = preliminaries, `Ch3`, `Ch4`), with `Infra/` for the general "
               "tooling that no single paper statement owns.  Every directory has its own "
               "`README.md` listing its modules, and `L20261018/README.md` maps the paper's "
               "own items onto them.  The `paper` column of the index gives the `@source` "
               "locator attached to the module, when the module "
               f"carries one ({with_paper} modules do).\n")
    out.append("\n")
    out.append("| directory | modules | declarations | theme |\n")
    out.append("|---|---|---|---|\n")
    for directory in sorted(dirs):
        count, mods = dirs[directory]
        theme = K.THEMES.get(directory, "")
        out.append(f"| `{directory}/` | {len(mods)} | {count} | {theme} |\n")
    out.append("\n")
    out.append("## Index\n")
    out.append("\n")
    out.append("| declaration | module | line | paper |\n")
    out.append("|---|---|---|---|\n")
    for name, module, line, _directory, _kind, paper, rel in sorted(
            rows, key=lambda r: (r[0], r[1], r[2])):
        cell = "" if not paper else "`" + paper + "`"
        out.append(f"| `{name}` | [`L20261018.{module}`]({rel}) | "
                   f"[{line}]({rel}#L{line}) | {cell} |\n")
    return "".join(out)


def main(argv):
    rows, modules_by_dir, anon = scan()
    historical = K.scan_historical_count()
    text = render(rows, historical, modules_by_dir, anon)
    if "--report" in argv:
        print(f"{len(rows)} declarations in "
              f"{len({m for ms in modules_by_dir.values() for m in ms})} modules, "
              f"{anon} anonymous instances, {historical} at the historical column-0 scan")
        return 0
    if "--pairs" in argv:
        for name, module, line, _directory, _kind, _paper, _rel in sorted(rows):
            print(f"{name}\t{line}\t{module}")
        return 0
    if "--check" in argv:
        old = io.open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if old == text:
            print("DECLARATIONS.md is up to date")
            return 0
        print("DECLARATIONS.md is STALE", file=sys.stderr)
        return 1
    K.write(OUT, text)
    print(f"wrote DECLARATIONS.md: {len(rows)} declarations, {anon} anonymous instances, "
          f"{len({m for ms in modules_by_dir.values() for m in ms})} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
