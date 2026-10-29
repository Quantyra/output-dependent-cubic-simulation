"""Exercise Python-compiled two-phase gate records against the Lean recognizer.

These finite examples detect interface regressions; they are not a proof of
Python/Lean equivalence or of any manuscript theorem.
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
import cubic_centroid_descent as compiler
import finite_field_acceptance as field

CASES = [
    ["cubic-field-v1", 1, [1], [[], []], 0, 0],
    ["cubic-field-v1", 2, [1, 2], [[0, 1, 3], [2]], 0, 1],
    ["cubic-field-v1", 3, [1, 2, 4], [[0, 3, 7], [1, 5, 7]], 3, 2],
    ["cubic-field-v1", 2, [2, 1], [[1], [3]], 1, 0],
    ["cubic-field-v1", 3, [1, 2, 4], [[7, 1, 7, 0], [3, 3, 2]], 7, 1],
]


def main():
    # Validation must precede cancellation: both copies of mask 2 exceed width 1.
    invalid = ["cubic-field-v1", 1, [1], [[2, 2], []], 0, 0]
    try:
        compiler.normalize_descriptor(invalid)
    except ValueError:
        pass
    else:
        raise AssertionError("Python accepted duplicate out-of-range masks")
    lines = ["import SectorSimulation.ByteCanonicalRecognizer", "open SectorSimulation"]
    for index, desc in enumerate(CASES):
        result = compiler.compile_native(desc)
        assert compiler.recognize_native(result["qubits"], result["gates"], result["basis"], result["output"]) == result["descriptor"]
        records = ", ".join(
            "\u27e8\"" + gate[0] + "\", [" + ", ".join(map(str, gate[1:])) + "]\u27e9"
            for gate in result["gates"]
        )
        lines.append(f"def pythonCase{index} : List NativeGate := [{records}]")
        lines.append(f"#guard (recognizeModeledSource pythonCase{index}).isSome")
        lines.append(f"#guard (recognizeNormalizedModeledSource pythonCase{index}).isSome")
        lines.append(f"#guard (recognizeByteCanonicalModeledSource pythonCase{index}).isSome")
    # The body is canonical, but the original header retains canceling duplicates.
    raw = ["cubic-field-v1", 2, [1, 2], [[1, 1], []], 0, 1]
    normalized = compiler.compile_native(raw)
    canonical_header = field.header(normalized["descriptor"])
    noncanonical_gates = field.header(raw) + normalized["gates"][len(canonical_header):]
    try:
        compiler.recognize_native(2, noncanonical_gates, 0, 1)
    except ValueError:
        pass
    else:
        raise AssertionError("Python accepted a noncanonical descriptor header")
    records = ", ".join(
        "\u27e8\"" + gate[0] + "\", [" + ", ".join(map(str, gate[1:])) + "]\u27e9"
        for gate in noncanonical_gates
    )
    lines.append(f"def noncanonicalCase : List NativeGate := [{records}]")
    lines.append("#guard (recognizeNormalizedModeledSource noncanonicalCase).isNone")
    # Semantically identical JSON with spaces is not Python's canonical header.
    raw = normalized["descriptor"]
    spaced = json.dumps(raw).encode("ascii")
    spaced_header = []
    for byte in spaced:
        for shift in range(7, -1, -1):
            tag = "Z" if byte >> shift & 1 else "X"
            spaced_header.extend([(tag, 0), (tag, 0)])
    spaced_header.extend([("H", 0), ("H", 0)])
    spaced_gates = spaced_header + normalized["gates"][len(canonical_header):]
    try:
        compiler.recognize_native(2, spaced_gates, 0, 1)
    except ValueError:
        pass
    else:
        raise AssertionError("Python accepted noncanonical JSON whitespace")
    records = ", ".join(
        "\u27e8\"" + gate[0] + "\", [" + ", ".join(map(str, gate[1:])) + "]\u27e9"
        for gate in spaced_gates
    )
    lines.append(f"def whitespaceCase : List NativeGate := [{records}]")
    lines.append("#guard (recognizeNormalizedModeledSource whitespaceCase).isSome")
    lines.append("#guard (recognizeByteCanonicalModeledSource whitespaceCase).isNone")
    with tempfile.TemporaryDirectory(prefix="python-lean-bridge-") as temp:
        probe = Path(temp) / "PythonBridgeProbe.lean"
        probe.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
        subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", check=True)
    print(f"Python/Lean finite bridge examples passed: {len(CASES)}; no general equivalence claimed.")


if __name__ == "__main__":
    main()
