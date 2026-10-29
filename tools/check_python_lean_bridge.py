"""Exercise Python-compiled two-phase gate records against the Lean recognizer.

These finite examples detect interface regressions; they are not a proof of
Python/Lean equivalence or of any manuscript theorem.
"""
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import cubic_centroid_descent as compiler

CASES = [
    ["cubic-field-v1", 1, [1], [[], []], 0, 0],
    ["cubic-field-v1", 2, [1, 2], [[0, 1, 3], [2]], 0, 1],
    ["cubic-field-v1", 3, [1, 2, 4], [[0, 3, 7], [1, 5, 7]], 3, 2],
    ["cubic-field-v1", 2, [2, 1], [[1], [3]], 1, 0],
    ["cubic-field-v1", 3, [1, 2, 4], [[7, 1, 7, 0], [3, 3, 2]], 7, 1],
]


def main():
    lines = ["import SectorSimulation.ModeledSourceRecognizer", "open SectorSimulation"]
    for index, desc in enumerate(CASES):
        result = compiler.compile_native(desc)
        assert compiler.recognize_native(result["qubits"], result["gates"], result["basis"], result["output"]) == result["descriptor"]
        records = ", ".join(
            "\u27e8\"" + gate[0] + "\", [" + ", ".join(map(str, gate[1:])) + "]\u27e9"
            for gate in result["gates"]
        )
        lines.append(f"def pythonCase{index} : List NativeGate := [{records}]")
        lines.append(f"#guard (recognizeModeledSource pythonCase{index}).isSome")
    with tempfile.TemporaryDirectory(prefix="python-lean-bridge-") as temp:
        probe = Path(temp) / "PythonBridgeProbe.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
        subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", check=True)
    print(f"Python/Lean finite bridge examples passed: {len(CASES)}; no general equivalence claimed.")


if __name__ == "__main__":
    main()
