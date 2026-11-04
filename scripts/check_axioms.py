#!/usr/bin/env python3
"""Check local sources and the axiom closure of the principal theorems."""
from pathlib import Path
import re
import subprocess
import sys
root = Path(__file__).resolve().parents[1]
for source in (root / "BentDecomposition").glob("*.lean"):
    if re.search(r"\b(sorry|admit|native_decide|sorryAx)\b|^\s*(axiom|unsafe)\b", source.read_text(), re.M):
        sys.exit(f"Forbidden admission or declaration: {source.name}")
p = subprocess.run(["lake", "env", "lean", "Audit.lean"], cwd=root,
                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
print(p.stdout, end="")
if p.returncode:
    sys.exit(p.returncode)
found = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", p.stdout))
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in ("Fn_not_sum_two_bent", "Fn_not_at_most_two", "full_infinite_family",
             "Bent.even_dimension", "walsh_parseval",
             "ThreeSummands.b0_bent", "ThreeSummands.F8_three_bent", "ThreeSummands.F8_exactly_three"):
    target = "BentDecompositions.Family." + name
    if target not in found or not {a.strip() for a in found[target].split(",") if a.strip()} <= allowed:
        sys.exit(f"Missing or unexpected axiom report: {target}")
print("Admission scan and standard-axiom checks passed.")
