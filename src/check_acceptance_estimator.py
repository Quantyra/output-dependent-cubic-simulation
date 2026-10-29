"""Bounded checks for S013; exact moments plus independent dense/truth-table oracles.

No third-party packages, stochastic pass criteria, hardware, or cloud execution.
This deliberately enumerates small state spaces and is not a universal simulator.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import cmath
import json
import math
import random


@dataclass(frozen=True)
class Q2:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    @staticmethod
    def coerce(v):
        return v if isinstance(v, Q2) else Q2(v)

    def __add__(self, v):
        v = self.coerce(v)
        return Q2(self.a + v.a, self.b + v.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, v):
        return self + -self.coerce(v)

    def __mul__(self, v):
        v = self.coerce(v)
        return Q2(self.a * v.a + 2 * self.b * v.b,
                  self.a * v.b + self.b * v.a)

    __rmul__ = __mul__

    def __truediv__(self, v):
        v = self.coerce(v)
        d = v.a * v.a - 2 * v.b * v.b
        if not d:
            raise ZeroDivisionError
        return self * Q2(v.a / d, -v.b / d)

    def sign(self):
        if not self.a:
            return (self.b > 0) - (self.b < 0)
        if not self.b or self.a * self.b > 0:
            return (self.a > 0) - (self.a < 0)
        dominant = self.a if self.a * self.a > 2 * self.b * self.b else self.b
        return (dominant > 0) - (dominant < 0)

    def __abs__(self):
        return self * self.sign()

    def __float__(self):
        return float(self.a) + math.sqrt(2) * float(self.b)


ZERO, ONE, INV_SQRT2 = Q2(), Q2(1), Q2(0, F(1, 2))
PRODUCTS = {("X", "Y"): (1, "Z"), ("Y", "Z"): (1, "X"),
            ("Z", "X"): (1, "Y"), ("Y", "X"): (3, "Z"),
            ("Z", "Y"): (3, "X"), ("X", "Z"): (3, "Y")}


def pauli_product(left, right):
    phase, out = 0, []
    for a, b in zip(left, right):
        if a == "I":
            out.append(b)
        elif b == "I":
            out.append(a)
        elif a == b:
            out.append("I")
        else:
            shift, char = PRODUCTS[a, b]
            phase += shift
            out.append(char)
    return phase % 4, "".join(out)


def gate_column(pauli, gate):
    name, *wires = gate
    if name == "CX":
        c, t = wires
        # Conjugation is an algebra homomorphism; multiply images in wire order.
        out, phase = "I" * len(pauli), 0
        for q, char in enumerate(pauli):
            image = ["I"] * len(pauli)
            image[q] = char
            if q == c and char in "XY":
                image[t] = "X"
            if q == t and char in "YZ":
                image[c] = "Z"
            shift, out = pauli_product(out, image)
            phase += shift
        assert phase % 2 == 0
        return {out: Q2(1 if phase % 4 == 0 else -1)}
    q = wires[0]
    char = pauli[q]
    rules = {
        "H": {"I": [("I", ONE)], "X": [("Z", ONE)],
              "Y": [("Y", -ONE)], "Z": [("X", ONE)]},
        "S": {"I": [("I", ONE)], "X": [("Y", -ONE)],
              "Y": [("X", ONE)], "Z": [("Z", ONE)]},
        "T": {"I": [("I", ONE)], "Z": [("Z", ONE)],
              "X": [("X", INV_SQRT2), ("Y", -INV_SQRT2)],
              "Y": [("X", INV_SQRT2), ("Y", INV_SQRT2)]},
        "TDG": {"I": [("I", ONE)], "Z": [("Z", ONE)],
                "X": [("X", INV_SQRT2), ("Y", INV_SQRT2)],
                "Y": [("X", -INV_SQRT2), ("Y", INV_SQRT2)]},
    }
    return {pauli[:q] + out + pauli[q + 1:]: a for out, a in rules[name][char]}


def block_column(pauli, block):
    terms = {pauli: ONE}
    for gate in reversed(block):
        updated = {}
        for p, coefficient in terms.items():
            for q, a in gate_column(p, gate).items():
                updated[q] = updated.get(q, ZERO) + coefficient * a
        terms = {p: a for p, a in updated.items() if a != ZERO}
    assert sum((a * a for a in terms.values()), ZERO) == ONE
    return terms


def overlap(pauli, x):
    if any(c in "XY" for c in pauli):
        return 0
    return (-1) ** sum(((x >> q) & 1) for q, c in enumerate(pauli) if c == "Z")


def distribution(column, eta=None):
    norm = sum((abs(a) for a in column.values()), ZERO)
    ideal = {p: abs(a) / norm for p, a in column.items()}
    if eta is None:
        return ideal
    # Fixed finite test implementation; every rounding claim is checked exactly.
    scale = 1 << 24
    counts = {p: math.floor(float(q) * scale) for p, q in ideal.items()}
    counts[next(iter(counts))] += scale - sum(counts.values())
    rounded = {p: Q2(F(c, scale)) for p, c in counts.items()}
    for p, q in rounded.items():
        assert q.sign() > 0
        assert (q - ideal[p] * (1 - eta)).sign() >= 0
        assert (ideal[p] * (1 + eta) - q).sign() >= 0
    assert sum(rounded.values(), ZERO) == ONE
    return rounded


def moments(n, blocks, x=0, output=0, corrected=False):
    initial = "I" * output + "Z" + "I" * (n - output - 1)
    # Store unconditional probability, weighted first moment, weighted second moment.
    states = {initial: (ONE, ONE, ONE)}
    eta = F(1, 4 * max(1, len(blocks))) if corrected else None
    for block in reversed(blocks):
        updated = {}
        for p, (prob, first, second) in states.items():
            column = block_column(p, block)
            proposal = distribution(column, eta)
            for q, a in column.items():
                mass, mean, square = updated.get(q, (ZERO, ZERO, ZERO))
                updated[q] = (mass + prob * proposal[q], mean + first * a,
                              square + second * a * a / proposal[q])
        states = updated
        assert sum((v[0] for v in states.values()), ZERO) == ONE
    mean = sum((v[1] * overlap(p, x) for p, v in states.items()), ZERO)
    second = sum((v[2] * overlap(p, x) ** 2 for p, v in states.items()), ZERO)
    assert (second - mean * mean).sign() >= 0
    return mean, second


def apply_dense(state, gate):
    name, *wires = gate
    if name == "CX":
        c, t = wires
        out = [0j] * len(state)
        for i, amplitude in enumerate(state):
            out[i ^ ((1 << t) if (i >> c) & 1 else 0)] = amplitude
        return out
    q = wires[0]
    if name == "H":
        out = state.copy()
        for i in range(len(state)):
            if not (i >> q) & 1:
                j = i | (1 << q)
                out[i] = (state[i] + state[j]) / math.sqrt(2)
                out[j] = (state[i] - state[j]) / math.sqrt(2)
        return out
    phase = {"S": 1j, "T": cmath.exp(1j * math.pi / 4),
             "TDG": cmath.exp(-1j * math.pi / 4)}[name]
    return [a * phase if (i >> q) & 1 else a for i, a in enumerate(state)]


def dense_state(n, gates, x=0):
    state = [0j] * (1 << n)
    state[x] = 1
    for gate in gates:
        state = apply_dense(state, gate)
    return state


def dense_expectation(n, gates, x=0, output=0):
    return sum(abs(a) ** 2 * (-1 if (i >> output) & 1 else 1)
               for i, a in enumerate(dense_state(n, gates, x)))


def pauli_action(pauli, basis):
    target, phase = basis, 1 + 0j
    for q, char in enumerate(pauli):
        bit = (basis >> q) & 1
        if char in "XY":
            target ^= 1 << q
        if char == "Y":
            phase *= -1j if bit else 1j
        if char == "Z":
            phase *= -1 if bit else 1
    return target, phase


def check_gate_columns():
    checked = 0
    for gate in [(g, q) for g in ("H", "S", "T", "TDG") for q in (0, 1)] + [
            ("CX", 0, 1), ("CX", 1, 0)]:
        columns = [dense_state(2, [gate], basis) for basis in range(4)]
        for chars in product("IXYZ", repeat=2):
            p = "".join(chars)
            terms = gate_column(p, gate)
            for a in range(4):
                for b in range(4):
                    lhs = 0j
                    for i in range(4):
                        j, phase = pauli_action(p, i)
                        lhs += columns[a][j].conjugate() * phase * columns[b][i]
                    rhs = sum(float(c) * phase for q, c in terms.items()
                              for j, phase in [pauli_action(q, b)] if j == a)
                    assert abs(lhs - rhs) < 1e-12, (gate, p, a, b)
            checked += 1
    return checked


def toffoli_decomposition(a, b, t):
    return [("H", t), ("CX", b, t), ("TDG", t), ("CX", a, t),
            ("T", t), ("CX", b, t), ("TDG", t), ("CX", a, t),
            ("T", b), ("T", t), ("H", t), ("CX", a, b),
            ("T", a), ("TDG", b), ("CX", a, b)]


def walsh(values):
    out = values.copy()
    half = 1
    while half < len(out):
        for base in range(0, len(out), 2 * half):
            for j in range(half):
                a, b = out[base + j], out[base + j + half]
                out[base + j], out[base + j + half] = a + b, a - b
        half *= 2
    return [F(v, len(out)) for v in out]


def check_toffoli_family():
    for basis in range(8):
        expected = basis ^ (4 if basis & 3 == 3 else 0)
        state = dense_state(3, toffoli_decomposition(0, 1, 2), basis)
        assert max(abs(a - (1 if i == expected else 0))
                   for i, a in enumerate(state)) < 1e-12
    rows = []
    for r in range(1, 7):
        n, target = 2 * r + 1, 2 * r
        truth = []
        for basis in range(1 << n):
            output = (basis >> target) & 1
            for j in range(r):
                output ^= ((basis >> (2 * j)) & 1) & ((basis >> (2 * j + 1)) & 1)
            truth.append((-1) ** output)
        fourier = walsh(truth)
        expansion = {1 << target: F(1)}
        for j in range(r):
            u, v = 1 << (2 * j), 1 << (2 * j + 1)
            expansion = {mask ^ term: c * sign / 2 for mask, c in expansion.items()
                         for term, sign in [(0, 1), (u, 1), (v, 1), (u | v, -1)]}
        assert {mask: c for mask, c in enumerate(fourier) if c} == expansion
        l1 = sum(abs(c) for c in expansion.values())
        assert len(expansion) == 4 ** r and l1 == 2 ** r
        assert sum(expansion.values()) == 1
        assert sum(c * c for c in expansion.values()) == 1
        rows.append({"r": r, "qubits": n, "terms": len(expansion),
                     "coefficient_l1": int(l1), "second_moment_lower_bound": 4 ** r,
                     "acceptance_variance_lower_bound": str(F(4 ** r - 1, 4))})
    # Verify grouping and the compiled native gate sequence on the first two members.
    for r in (1, 2):
        blocks = [toffoli_decomposition(2 * j, 2 * j + 1, 2 * r) for j in range(r)]
        gates = sum(blocks, [])
        for partition in (blocks, [gates]):
            mean, second = moments(2 * r + 1, partition, output=2 * r)
            assert mean == ONE and second == Q2(4 ** r)
        mean, second = moments(2 * r + 1, [[g] for g in gates], output=2 * r)
        assert mean == ONE and (second - 4 ** r).sign() >= 0
    return rows


def main():
    max_error, comparisons, corrected_checks = 0.0, 0, 0
    gate_checks = check_gate_columns()
    circuits = []
    for length in range(5):
        for names in product(("H", "S", "T", "TDG"), repeat=length):
            circuits.append((1, [(name, 0) for name in names], length % 2, 0))
    one_qubit_count = len(circuits)
    rng = random.Random(13006)
    for _ in range(96):
        n = rng.choice((2, 3))
        gates = []
        for _ in range(12):
            name = rng.choice(("H", "S", "T", "TDG", "CX"))
            wires = rng.sample(range(n), 2) if name == "CX" else [rng.randrange(n)]
            gates.append((name, *wires))
        circuits.append((n, gates, rng.randrange(1 << n), rng.randrange(n)))
    for n, gates, x, output in circuits:
        partitions = [[[g] for g in gates], [gates] if gates else [],
                      [gates[i:i + 3] for i in range(0, len(gates), 3)]]
        expected = dense_expectation(n, gates, x, output)
        for blocks in partitions:
            mean, second = moments(n, blocks, x, output)
            error = abs(float(mean) - expected)
            max_error = max(max_error, error)
            assert error < 1e-11, (n, gates, x, output, mean, expected)
            corrected_mean, corrected_second = moments(n, blocks, x, output, True)
            assert corrected_mean == mean
            assert (2 * second - corrected_second).sign() >= 0
            comparisons += 1
            corrected_checks += 1
    identity_rows = []
    for t in (8, 16, 32, 64):
        gates = [("H", 0)] + [("T", 0)] * t + [("H", 0)]
        mean, second = moments(1, [[g] for g in gates])
        assert mean == ONE and second == Q2(2 ** (t - 1))
        grouped = [[("H", 0)]] + [[("T", 0)] * 8 for _ in range(t // 8)] + [[("H", 0)]]
        assert moments(1, grouped) == (ONE, ONE)
        identity_rows.append({"T_count": t, "raw_second_moment": str(2 ** (t - 1)),
                              "grouped_second_moment": 1})
    result = {
        "scope": "Finite internal checks only; no independent review or complexity-class result.",
        "exact_arithmetic": "Fraction pairs a + b*sqrt(2); moments and inequalities exact",
        "dense_oracle_tolerance": 1e-11,
        "gate_pauli_columns_checked_against_dense_matrices": gate_checks,
        "exhaustive_one_qubit_circuits_lengths_0_through_4": one_qubit_count,
        "seeded_two_and_three_qubit_circuits": 96,
        "seed": 13006,
        "partition_expectation_comparisons": comparisons,
        "dyadic_importance_correction_checks": corrected_checks,
        "maximum_dense_expectation_error": max_error,
        "identity_family": identity_rows,
        "toffoli_family_exact_walsh_checks": check_toffoli_family(),
        "toffoli_compilation_basis_states_checked": 8,
        "compiled_toffoli_family_members_with_moment_checks": [1, 2],
        "limits": ["Small finite state spaces only; no asymptotic lemma proved by tests.",
                   "24-bit dyadic test probabilities certified on these cases only.",
                   "General bit-complexity and all-grouping obstruction are arguments in the note."]
    }
    destination = Path(__file__).resolve().parents[1] / "artifacts" / "acceptance-estimator-checks.json"
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "comparisons": comparisons,
                      "max_dense_error": max_error, "artifact": str(destination)}, indent=2))


if __name__ == "__main__":
    main()
