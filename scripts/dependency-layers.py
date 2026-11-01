#!/usr/bin/env python3
"""Why the development cannot be merged one-module-per-topic-directory.

    python3 scripts/dependency-layers.py            # the verdict, with evidence
    python3 scripts/dependency-layers.py --cycles   # every mutual dependency between dirs

Merging the `StepNNN` modules of a directory into a single module is mechanically fine --
`scripts/merge-directory.py` does it, and a one-directory trial (`Ch2/Rost`) compiled with
`lake build` clean.  What does *not* work is doing it for every directory at once: Lean
rejects an import cycle, and the quotient of the module graph by the topic directories is
**strongly connected** -- the topics are not dependency layers.  For example
`Ch2/Brauer/Step035` imports `Ch4/Step017` while `Ch4/Step025` imports
`Ch2/Brauer/Step035`.

So the only cycle-free merges are (a) merge nothing, or (b) merge the whole strongly
connected component into one module.  This script prints that verdict and the witnesses, so
the claim can be re-checked after any change to the development.
"""
import collections
import io
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import kb_meta as K

IMPORT = re.compile(r"^import L20261018\.(\S+)[ \t]*$", re.M)


def graph():
    """{module: (directory, [imported modules])} for the development."""
    out = {}
    for dp, _dirs, files in os.walk(K.DEV):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dp, fn)
            rel = os.path.relpath(path, K.DEV)[:-len(".lean")]
            out[rel.replace(os.sep, ".")] = (
                os.path.dirname(rel).replace(os.sep, "/") or ".",
                IMPORT.findall(io.open(path, encoding="utf-8").read()))
    return out


def quotient(g):
    """{(dir, dir): [edge witnesses]} for the topic-directory graph."""
    dir_of = {m: d for m, (d, _) in g.items()}
    edges = collections.defaultdict(list)
    for m, (d, imps) in g.items():
        for i in imps:
            if i in dir_of and dir_of[i] != d:
                edges[(d, dir_of[i])].append((m, i))
    return edges


def sccs(nodes, edges):
    index, low, on, stack, out, counter = {}, {}, set(), [], [], [0]

    def strong(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for u in sorted({b for (a, b) in edges if a == v}):
            if u not in index:
                strong(u)
                low[v] = min(low[v], low[u])
            elif u in on:
                low[v] = min(low[v], index[u])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))

    sys.setrecursionlimit(10000)
    for v in sorted(nodes):
        if v not in index:
            strong(v)
    return out


def height(nodes, edges):
    """Length of the longest chain in the condensation -- how many layers there are."""
    comp = {}
    for i, c in enumerate(sccs(nodes, edges)):
        for v in c:
            comp[v] = i
    dag = collections.defaultdict(set)
    for (a, b) in edges:
        if comp[a] != comp[b]:
            dag[comp[a]].add(comp[b])
    memo = {}

    def longest(c):
        if c in memo:
            return memo[c]
        best = 0
        for d in dag.get(c, ()):
            best = max(best, 1 + longest(d))
        memo[c] = best
        return best

    return max((longest(c) for c in set(comp.values())), default=0) + 1


def main(argv):
    g = graph()
    edges = quotient(g)
    dirs = sorted({d for d, _ in g.values()})
    comps = sccs(dirs, edges)
    big = [c for c in comps if len(c) > 1]
    print(f"modules: {len(g)}; topic directories: {len(dirs)}; "
          f"strongly connected components: {len(comps)}")
    for c in sorted(comps, key=lambda c: -len(c)):
        if len(c) > 1:
            print(f"  component of {len(c)} directories: {', '.join(c)}")
        else:
            print(f"  single directory (no cycle): {c[0]}")
    print(f"layers (longest chain in the condensation): {height(dirs, edges)}")

    if "--cycles" in argv or not big:
        for (a, b) in sorted(edges):
            if (b, a) in edges:
                m, i = edges[(a, b)][0]
                n, j = edges[(b, a)][0]
                print(f"  cycle  {a} -> {b}: {m} imports {i}")
                print(f"         {b} -> {a}: {n} imports {j}")
        return 0

    for c in big:
        # one witness per component: a pair inside it with edges both ways
        inside = [(a, b) for (a, b) in edges if a in c and b in c and (b, a) in edges]
        if inside:
            a, b = sorted(inside)[0]
            m, i = edges[(a, b)][0]
            n, j = edges[(b, a)][0]
            print(f"\nwitness inside the component:")
            print(f"  {m} imports {i}        (so {a} needs {b})")
            print(f"  {n} imports {j}        (so {b} needs {a})")
            print("  => merging both directories into one module each would be an import cycle")
    print("\nverdict: a cycle-free one-module-per-directory split does not exist; see the "
          "module docstring for the alternatives")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
