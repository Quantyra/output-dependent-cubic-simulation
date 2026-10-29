"""Fetch only the Mathlib modules needed by the complex semantics proof."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
HASHING = LEAN / ".lake/packages/mathlib/Cache/Hashing.lean"
MODULES = ["Mathlib.Data.Complex.Basic", "Mathlib.Data.Real.Sqrt",
           "Mathlib.Analysis.SpecialFunctions.Pow.Real"]


def main():
    original = HASHING.read_bytes()
    source = original.decode("utf-8")
    start = source.index("def roots : CacheM")
    end = source.index("/-- Main API", start)
    targeted = source[:start] + "def roots : CacheM (Array (Prod Name FilePath)) := pure #[]\n\n" + source[end:]
    try:
        HASHING.write_bytes(targeted.encode("utf-8"))
        subprocess.run(["lake", "exe", "cache", "get", *MODULES], cwd=LEAN, check=True)
    finally:
        HASHING.write_bytes(original)


if __name__ == "__main__":
    main()
