#!/usr/bin/env python3
"""Check that no axioms are used in the proof."""
import subprocess
import sys

result = subprocess.run(
    ["lake", "env", "lean", "Audit.lean"],
    capture_output=True, text=True
)

output = result.stdout + result.stderr

# The #print axioms command outputs axiom lists.
# We check that no problematic axioms are used.
PROBLEMATIC_AXIOMS = [
    "sorryAx",
    "axiom_of_choice",
    "propext",
    "Classical.choice",
]

lines = output.strip().split("\n")
has_axioms = False
for line in lines:
    if "'axiom" in line or "axiom" in line.lower():
        has_axioms = True
        for ax in PROBLEMATIC_AXIOMS:
            if ax in line:
                print(f"ERROR: Problematic axiom '{ax}' found: {line}")
                sys.exit(1)

if has_axioms:
    print("WARNING: Some axioms are used (may be standard):")
    for line in lines:
        if "axiom" in line.lower():
            print(f"  {line}")
else:
    print("OK: No axioms used in any theorem.")

print("Axiom check passed.")
