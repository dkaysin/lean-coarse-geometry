#!/usr/bin/env python3
"""List the state of every blueprint node and the frontier.

Reads the LaTeX nodes in `blueprint/src/chapters/*.tex` and the nodes LeanArchitect extracted
from `CoarseBlueprint` into `.lake/build/blueprint` (run `lake build :blueprint` first).

States: `planned` (LaTeX), `review` (Lean, tagged `notReady := true`: its Lean statement awaits
the user's review), `stated` (Lean, approved, proof not sorry-free), `proved` (Lean), `mathlib`
(`\\mathlibok`). The frontier is the set of planned nodes all of whose statement `\\uses` are
Lean nodes: statements are formalized before proofs, so the `\\uses` of a node's proof do not
hold it back.

Exits with status 1 if a label is used or input but defined nowhere, or defined twice, or if a
LaTeX node carries `\\notready` (only Lean nodes await review).
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHAPTERS = ROOT / "blueprint" / "src" / "chapters"
EXTRACTED = ROOT / ".lake" / "build" / "blueprint" / "module"
ENVS = "definition|lemma|theorem|corollary|proposition"
NODE = re.compile(
    r"\\begin\{(" + ENVS + r")\}(.*?)\\end\{\1\}(\s*\\begin\{proof\}(.*?)\\end\{proof\})?",
    re.S)
INPUT = re.compile(r"\\inputleannode\{([^}]*)\}")


def strip_comments(text):
    return re.sub(r"(?<!\\)%.*", "", text)


def labels_in(command, text):
    return [l.strip() for m in re.finditer(r"\\" + command + r"\{([^}]*)\}", text)
            for l in m.group(1).split(",") if l.strip()]


def parse(text):
    """Yield (label, statement, proof) for each node environment in `text`."""
    for m in NODE.finditer(text):
        statement, proof = m.group(2), m.group(4)
        label = labels_in("label", statement)
        if label:
            yield label[0], statement, proof


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--all", action="store_true", help="list every node, not only open work")
    args = ap.parse_args()

    nodes, errors, order = {}, [], []

    def add(label, node):
        if label in nodes:
            errors.append(f"label {label} defined twice ({nodes[label]['where']}, {node['where']})")
        nodes[label] = node

    if not EXTRACTED.exists():
        sys.exit("No extracted blueprint: run `lake build :blueprint` first.")
    for f in sorted(EXTRACTED.glob("**/*.artifacts/*.tex")):
        for label, statement, proof in parse(f.read_text()):
            lean = labels_in("lean", statement)
            if "\\mathlibok" in statement:
                state = "mathlib"
            elif "\\notready" in statement:
                state = "review"
            elif "\\leanok" in statement and (proof is None or "\\leanok" in proof):
                state = "proved"
            else:
                state = "stated"
            add(label, {"state": state, "where": ", ".join(lean),
                        "uses": labels_in("uses", statement) + labels_in("uses", proof or "")})

    content = strip_comments((CHAPTERS.parent / "content.tex").read_text())
    chapter_files = [CHAPTERS.parent / f"{c}.tex"
                     for c in re.findall(r"\\input\{(chapters/[^}]*)\}", content)]
    inputs = []
    for f in chapter_files:
        text = strip_comments(f.read_text())
        chapter = f.stem
        for m in INPUT.finditer(text):
            inputs.append((m.group(1), chapter))
            order.append((chapter, m.group(1)))
        for label, statement, proof in parse(text):
            planned = re.search(r"\\plannedlean\{([^}]*)\}", statement)
            if "\\notready" in statement:
                errors.append(f"LaTeX node {label} in {chapter}.tex carries \\notready")
            add(label, {"state": "planned",
                        "where": f"{chapter}.tex" + (f" ({planned.group(1)})" if planned else ""),
                        "uses": labels_in("uses", statement) + labels_in("uses", proof or ""),
                        "statement_uses": labels_in("uses", statement)})
            order.append((chapter, label))

    for label, chapter in inputs:
        if label not in nodes or nodes[label]["state"] == "planned":
            errors.append(f"\\inputleannode{{{label}}} in {chapter}.tex has no Lean node")
    for label, node in nodes.items():
        for u in node["uses"]:
            if u not in nodes:
                errors.append(f"{label} uses undefined label {u}")

    formal = {"review", "stated", "proved", "mathlib"}

    def missing(label):
        return [u for u in nodes[label]["statement_uses"]
                if nodes.get(u, {}).get("state") not in formal]

    seen, frontier, blocked, review, sorried = set(), [], [], [], []
    for chapter, label in order:
        if label in seen or label not in nodes:
            continue
        seen.add(label)
        node = nodes[label]
        if node["state"] == "planned":
            (blocked if missing(label) else frontier).append((chapter, label))
        elif node["state"] == "review":
            review.append((chapter, label))
        elif node["state"] == "stated":
            sorried.append((chapter, label))
        if args.all:
            print(f"{node['state']:9} {chapter:18} {label:45} {node['where']}")

    if args.all:
        print()
    print("Frontier (planned, every statement \\uses formalized):")
    for chapter, label in frontier:
        print(f"  {chapter:18} {label:45} {nodes[label]['where']}")
    print("Awaiting review (Lean statement not yet approved):")
    for chapter, label in review:
        print(f"  {chapter:18} {label:45} {nodes[label]['where']}")
    print("Stated, proof not sorry-free:")
    for chapter, label in sorried:
        print(f"  {chapter:18} {label:45} {nodes[label]['where']}")
    print("Planned but blocked:")
    for chapter, label in blocked:
        print(f"  {chapter:18} {label:45} waits for {', '.join(missing(label))}")
    if errors:
        print("\nErrors:")
        for e in errors:
            print("  " + e)
        sys.exit(1)


if __name__ == "__main__":
    main()
