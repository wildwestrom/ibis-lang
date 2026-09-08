"""Compare the original Haskell evaluator with the Lean CLI on shared cases."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent.parent
subprocess.run(["lake", "build", "ibis"], cwd=root, check=True)
oracle = subprocess.run(
    ["runghc", "-isrc", "test/LeanParity.hs"],
    cwd=root, check=True, text=True, capture_output=True,
)
fixtures = oracle.stdout.splitlines()
for fixture in fixtures:
    source, expected = fixture.split("\t", 1)
    actual = subprocess.run(
        [str(root / ".lake/build/bin/ibis"), "eval", source],
        cwd=root, check=True, text=True, capture_output=True,
    ).stdout.strip()
    if actual != expected:
        raise AssertionError(f"{source}: Haskell={expected!r}, Lean={actual!r}")
print(f"{len(fixtures)} Haskell/Lean evaluator comparisons passed")
