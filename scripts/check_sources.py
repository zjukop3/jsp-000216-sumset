#!/usr/bin/env python3
"""Check that no sorry is used in the proof."""
import subprocess
import sys

result = subprocess.run(
    ["lake", "env", "lean", "ErdosProblems/ErdosProblem.lean"],
    capture_output=True, text=True
)

output = result.stdout + result.stderr

if "sorry" in output:
    print("ERROR: sorry found in the proof!")
    for line in output.split("\n"):
        if "sorry" in line.lower():
            print(f"  {line}")
    sys.exit(1)

if result.returncode != 0:
    print("ERROR: Proof file does not compile!")
    print(output)
    sys.exit(1)

print("OK: No sorry, proof compiles successfully.")
print("Source check passed.")
