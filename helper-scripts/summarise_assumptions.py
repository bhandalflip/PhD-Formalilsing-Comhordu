#!/usr/bin/env python3
"""Summarise what the top-level `safety` theorem still rests on, as Markdown.

Runs `Print Assumptions safety` against the compiled project (run `make` first) and leads with
the unproved results it rests on (Admitted / Conjecture), the measure of what is left to prove.
The model axioms (ComhBasics) are deliberate and shown consistent in ModelConsistency.v, so they
and the standard-library axioms come after, as counts. Also counts every `Admitted` /
`Conjecture` in src/, whether or not `safety` uses it.

Usage: python3 helper-scripts/summarise_assumptions.py   (from the repository root)
"""
import collections
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "src")


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return "".join(out)


def print_assumptions():
    with tempfile.TemporaryDirectory() as d:
        v = os.path.join(d, "PrintSafety.v")
        with open(v, "w") as f:
            f.write("From ComhCoq.protocol Require Import Main.\nPrint Assumptions safety.\n")
        r = subprocess.run(["rocq", "compile", "-R", SRC, "ComhCoq", v],
                           capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit("rocq compile failed:\n" + r.stderr + r.stdout)
    names = []
    for line in r.stdout.splitlines():
        if line and not line[0].isspace() and line != "Axioms:":
            names.append(line.split()[0])
    return names


def source_counts():
    admitted, conjectures = collections.Counter(), collections.Counter()
    for dirpath, _, files in os.walk(SRC):
        for fn in sorted(files):
            if fn.endswith(".v") and "Extras" not in dirpath:
                body = strip_comments(open(os.path.join(dirpath, fn)).read())
                admitted[fn] = len(re.findall(r"\bAdmitted\s*\.", body))
                conjectures[fn] = len(re.findall(r"^\s*Conjecture\b", body, re.M))
    return admitted, conjectures


def main():
    names = print_assumptions()
    model, std, unproved = [], [], []
    for n in names:
        mod = n.split(".")[0]
        if mod == "ComhBasics":
            model.append(n)
        elif mod in ("ClassicalDedekindReals", "ProofIrrelevance", "FunctionalExtensionality",
                     "Eqdep", "Classical_Prop", "ClassicalEpsilon", "IndefiniteDescription",
                     "Description", "ClassicalUniqueChoice", "PropExtensionality", "JMeq"):
            std.append(n)
        else:
            unproved.append(n)
    admitted, conjectures = source_counts()

    print("## What `safety` rests on\n")
    print(f"**{len(unproved)}** unproved results.\n")
    byfile = collections.defaultdict(list)
    for n in unproved:
        byfile[n.split(".")[0]].append(n.split(".", 1)[1])
    for f in sorted(byfile, key=lambda f: (-len(byfile[f]), f)):
        print(f"- `{f}`: " + ", ".join(f"`{x}`" for x in sorted(byfile[f])))
    if unproved:
        print()
    print(f"It also rests on {len(model)} model axioms, which are deliberate and shown consistent "
          f"in `ModelConsistency.v`, and on {len(std)} standard-library axioms.\n")
    print(f"Whole codebase: **{sum(admitted.values())}** `Admitted`, "
          f"**{sum(conjectures.values())}** `Conjecture`.\n")
    print("<details><summary>Everything it rests on</summary>\n\n```")
    for n in names:
        print(n)
    print("```\n</details>")


if __name__ == "__main__":
    main()
