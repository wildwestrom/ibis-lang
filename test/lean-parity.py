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

haskell_chunks = subprocess.run(
    ["runghc", "-isrc", "test/ChunkParity.hs"],
    cwd=root, check=True, text=True, capture_output=True,
).stdout.splitlines()
lean_chunks = subprocess.run(
    ["lake", "env", "lean", "--run", "test/ChunkParity.lean"],
    cwd=root, check=True, text=True, capture_output=True,
).stdout.splitlines()
if len(haskell_chunks) != 3 or lean_chunks != haskell_chunks:
    raise AssertionError(f"Chunk format mismatch: Haskell={haskell_chunks!r}, Lean={lean_chunks!r}")
print(f"{len(haskell_chunks)} Haskell/Lean chunk wire-format comparisons passed")
