"""S015 exact small-instance reference and checks, using only the standard library.

Dense vectors/branch enumeration deliberately replace scalable CH-form subroutines.
The large reversible-prefix checks use bit operations, not dense vectors.
Run with python -B src/check_input_aware_estimator.py to avoid cache artifacts.
"""

from bisect import bisect_right
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import product
from pathlib import Path
import json
import math
import random

from check_acceptance_estimator import Q2, apply_dense, toffoli_decomposition


@dataclass(frozen=True)
class C2:
    re: Q2 = Q2()
    im: Q2 = Q2()

    def __post_init__(self):
        object.__setattr__(self, 're', Q2.coerce(self.re))
        object.__setattr__(self, 'im', Q2.coerce(self.im))

    @staticmethod
    def coerce(v):
        return v if isinstance(v, C2) else C2(v)

    def __add__(self, v):
        v = self.coerce(v)
        return C2(self.re + v.re, self.im + v.im)

    __radd__ = __add__

    def __neg__(self):
        return C2(-self.re, -self.im)

    def __sub__(self, v):
        return self + -self.coerce(v)

    def __mul__(self, v):
        v = self.coerce(v)
        return C2(self.re * v.re - self.im * v.im,
                  self.re * v.im + self.im * v.re)

    __rmul__ = __mul__

    def __truediv__(self, v):
        v = self.coerce(v)
        z = self * v.conj()
        return C2(z.re / v.norm(), z.im / v.norm())

    def conj(self):
        return C2(self.re, -self.im)

    def norm(self):
        return self.re * self.re + self.im * self.im

    def as_complex(self):
        return complex(float(self.re), float(self.im))


Z, O, I = C2(), C2(1), C2(0, 1)
HALF_ROOT = Q2(0, F(1, 2))
OMEGA = C2(HALF_ROOT, HALF_ROOT)
W0, W1 = C2(1, Q2(-1, 1)), C2(1, Q2(1, -1))
XI = Q2(4, -2)


def qpow(q, k):
    result = Q2(1)
    for _ in range(k):
        result *= q
    return result


def norm(v):
    return sum((a.norm() for a in v), Q2())


def inner(u, v):
    return sum((a.conj() * b for a, b in zip(u, v)), Z)


def basis(n, x):
    return tuple(O if i == x else Z for i in range(1 << n))


def gate(v, op):
    name, *wires = op
    if name in ('CX', 'CCX', 'X'):
        out = [Z] * len(v)
        for i, a in enumerate(v):
            active = all((i >> q) & 1 for q in wires[:-1])
            out[i ^ ((1 << wires[-1]) if active else 0)] = a
        return tuple(out)
    q = wires[0]
    if name == 'H':
        out = list(v)
        for i in range(len(v)):
            if not (i >> q) & 1:
                j = i | (1 << q)
                out[i] = (v[i] + v[j]) * HALF_ROOT
                out[j] = (v[i] - v[j]) * HALF_ROOT
        return tuple(out)
    phase = {'S': I, 'SDG': -I, 'T': OMEGA, 'TDG': OMEGA.conj()}[name]
    return tuple(a * phase if (i >> q) & 1 else a for i, a in enumerate(v))


def evolve(n, ops, x=0):
    v = basis(n, x)
    for op in ops:
        v = gate(v, op)
    return v


def recognize_toffoli(ops):
    out, index, recognized = [], 0, 0
    while index < len(ops):
        chunk = ops[index:index + 15]
        if (len(chunk) == 15 and chunk[0][0] == 'H'
                and chunk[1][0] == chunk[3][0] == 'CX'):
            t, b, a = chunk[0][1], chunk[1][1], chunk[3][1]
            if len({a, b, t}) == 3 and chunk == toffoli_decomposition(a, b, t):
                out.append(('CCX', a, b, t))
                index += 15
                recognized += 1
                continue
        out.append(ops[index])
        index += 1
    return out, recognized


def preprocess(ops, x):
    macros, recognized = recognize_toffoli(ops)
    phase, removed = O, 0
    for name, *qs in macros:
        if name == 'H':
            break
        if name in ('X', 'CX', 'CCX'):
            if all((x >> q) & 1 for q in qs[:-1]):
                x ^= 1 << qs[-1]
        else:
            assert name in ('S', 'SDG', 'T', 'TDG')
            if (x >> qs[0]) & 1:
                phase *= {'S': I, 'SDG': -I, 'T': OMEGA, 'TDG': OMEGA.conj()}[name]
        removed += 1
    remaining = []
    for op in macros[removed:]:
        remaining.extend(toffoli_decomposition(*op[1:]) if op[0] == 'CCX' else [op])
    return x, phase, remaining, recognized


def z_eigenbit(v, q):
    bits = {(i >> q) & 1 for i, a in enumerate(v) if a != Z}
    return next(iter(bits)) if len(bits) == 1 else None


def projected(v, output):
    return tuple(a if (i >> output) & 1 else Z for i, a in enumerate(v))


def trajectories(n, ops, x=0, output=0):
    start, phase, remaining, _ = preprocess(ops, x)
    paths = [(F(1), phase, basis(n, start))]
    for op in remaining:
        updated = []
        for prob, w, v in paths:
            if op[0] not in ('T', 'TDG'):
                updated.append((prob, w, gate(v, op)))
                continue
            bit = z_eigenbit(v, op[1])
            if bit is not None:
                zphase = OMEGA if op[0] == 'T' else OMEGA.conj()
                updated.append((prob, w * (zphase if bit else O), v))
            else:
                w0, w1 = (W0, W1) if op[0] == 'T' else (W0.conj(), W1.conj())
                updated.append((prob / 2, w * w0, v))
                updated.append((prob / 2, w * w1,
                                gate(v, ('S' if op[0] == 'T' else 'SDG', op[1]))))
        paths = updated
    assert sum(prob for prob, _, _ in paths) == 1
    terms = [(prob, tuple(w * a for a in projected(v, output))) for prob, w, v in paths]
    return terms, sum(op[0] in ('T', 'TDG') for op in remaining)


def vector_mean(terms):
    return tuple(sum((p * v[i] for p, v in terms), Z) for i in range(len(terms[0][1])))


def equatorial_states(n):
    pairs = [(i, j) for i in range(n) for j in range(i)]
    for diagonal in product(range(4), repeat=n):
        for edges in product(range(2), repeat=len(pairs)):
            values = []
            for x in range(1 << n):
                power = sum(diagonal[q] * ((x >> q) & 1) for q in range(n))
                power += 2 * sum(a * ((x >> i) & 1) * ((x >> j) & 1)
                                 for a, (i, j) in zip(edges, pairs))
                phase = (O, I, -O, -I)[power % 4]
                values.append(phase * qpow(HALF_ROOT, n))
            yield tuple(values)


def ceil_q2(q):
    value = math.ceil(float(q))
    while (Q2(value) - q).sign() < 0:
        value += 1
    while (Q2(value - 1) - q).sign() >= 0:
        value -= 1
    return value


def reference_estimate(n, ops, x, output, epsilon, delta, rng):
    """Dense bounded implementation of the specified estimator, not scalable CH form."""
    terms, t = trajectories(n, ops, x, output)
    if t == 0:
        return norm(vector_mean(terms)), {'exact_shortcut': True, 'residual_T': 0}
    bound = ceil_q2(qpow(XI, t))
    m = math.ceil(1024 * bound / (epsilon * epsilon))
    j = math.ceil(1024 / (epsilon * epsilon))
    repetitions = math.ceil(8 * math.log(1 / delta)) | 1
    scale = max(p.denominator for p, _ in terms)
    ends, running = [], 0
    for prob, _ in terms:
        running += int(prob * scale)
        ends.append(running)
    assert running == scale
    theta = list(equatorial_states(n))
    estimates = []
    for _ in range(repetitions):
        counts = Counter(bisect_right(ends, rng.randrange(scale)) for _ in range(m))
        v = tuple(sum((terms[k][1][i] * F(count, m) for k, count in counts.items()), Z)
                  for i in range(1 << n))
        probe_counts = Counter(rng.randrange(len(theta)) for _ in range(j))
        estimates.append(sum(((1 << n) * inner(theta[k], v).norm() * F(count, j)
                              for k, count in probe_counts.items()), Q2()))
    estimates.sort(key=cmp_to_key(lambda a, b: (a - b).sign()))
    value = estimates[len(estimates) // 2]
    grid = 1
    while F(1, grid) > epsilon / 4:
        grid *= 2
    floored = ceil_q2(value * grid) - 1
    if (value * grid - floored - 1) == Q2():
        floored += 1
    rounded = Q2(F(floored, grid))
    assert abs(rounded - value).sign() == 0 or (Q2(epsilon / 4) - abs(rounded - value)).sign() >= 0
    result = Q2(0) if rounded.sign() < 0 else Q2(1) if (rounded - 1).sign() > 0 else rounded
    return result, {'exact_shortcut': False, 'residual_T': t, 'M': m, 'J': j,
                    'repetitions': repetitions, 'conservative_second_moment_bound': bound}


def all_stabilizers_float(n):
    def canonical(v):
        a = next(a for a in v if abs(a) > 1e-9)
        phase = a.conjugate() / abs(a)
        return tuple((round((z * phase).real, 10), round((z * phase).imag, 10)) for z in v)
    start = [1 + 0j] + [0j] * ((1 << n) - 1)
    seen, queue = {canonical(start): start}, deque([start])
    generators = [(g, q) for g in ('H', 'S') for q in range(n)]
    generators += [('CX', a, b) for a in range(n) for b in range(n) if a != b]
    while queue:
        v = queue.popleft()
        for op in generators:
            w = apply_dense(v, op)
            key = canonical(w)
            if key not in seen:
                seen[key] = w
                queue.append(w)
    return list(seen.values())


def main():
    assert W0.norm() == W1.norm() == XI
    for bit in (0, 1):
        v = basis(1, bit)
        for name, w0, w1, clifford in [('T', W0, W1, 'S'), ('TDG', W0.conj(), W1.conj(), 'SDG')]:
            rhs = tuple((w0 * a + w1 * b) / 2 for a, b in zip(v, gate(v, (clifford, 0))))
            assert gate(v, (name, 0)) == rhs
    for x in range(8):
        assert evolve(3, toffoli_decomposition(0, 1, 2), x) == gate(basis(3, x), ('CCX', 0, 1, 2))
    rng = random.Random(15006)
    circuits = []
    for length in range(5):
        for word in product(('H', 'S', 'T', 'TDG'), repeat=length):
            circuits.append((1, [(g, 0) for g in word], length % 2, 0))
    one_count = len(circuits)
    for _ in range(64):
        n = rng.choice((2, 3))
        ops = []
        for _ in range(9):
            g = rng.choice(('H', 'S', 'T', 'TDG', 'CX'))
            ops.append((g, *rng.sample(range(n), 2)) if g == 'CX' else (g, rng.randrange(n)))
        circuits.append((n, ops, rng.randrange(1 << n), rng.randrange(n)))
    pair_checks, max_terms, probe_checks = 0, 0, 0
    for index, (n, ops, x, output) in enumerate(circuits):
        terms, t = trajectories(n, ops, x, output)
        mu = projected(evolve(n, ops, x), output)
        assert vector_mean(terms) == mu
        p = norm(mu)
        r = sum((prob * norm(v) for prob, v in terms), Q2())
        assert (r - p).sign() >= 0 and (qpow(XI, t) - r).sign() >= 0
        max_terms = max(max_terms, len(terms))
        if len(terms) <= 8 and (index % 13 == 0 or index >= one_count):
            q = sum((pa * pb * norm(tuple((a + b) / 2 for a, b in zip(va, vb)))
                     for pa, va in terms for pb, vb in terms), Q2())
            assert q == p + (r - p) / 2  # exact raw bias for M=2
            pair_checks += 1
    for n in (1, 2, 3):
        theta = list(equatorial_states(n))
        examples = [basis(n, 0), evolve(n, [('H', 0), ('T', 0)]),
                    tuple(C2(F(i - 2, 7), F(1 - i, 11)) for i in range(1 << n))]
        for v in examples:
            samples = [(1 << n) * inner(w, v).norm() for w in theta]
            mean = sum(samples, Q2()) / len(samples)
            second = sum((a * a for a in samples), Q2()) / len(samples)
            vnorm = norm(v)
            assert mean == vnorm
            assert second == 2 * vnorm * vnorm - sum((a.norm() * a.norm() for a in v), Q2())
            assert (vnorm * vnorm - (second - mean * mean)).sign() >= 0
            probe_checks += 1
    reversible_rows = []
    for r in (1, 2, 4, 8, 16, 32):
        native = [('CCX', 2 * i, 2 * i + 1, 2 * r) for i in range(r)]
        compiled = sum((toffoli_decomposition(*op[1:]) for op in native), [])
        for _ in range(8):
            x = rng.randrange(1 << (2 * r + 1))
            expected = x
            for _, a, b, t in native:
                if ((expected >> a) & 1) and ((expected >> b) & 1):
                    expected ^= 1 << t
            for ops in (native, compiled):
                actual, phase, remaining, _ = preprocess(ops, x)
                assert actual == expected and phase == O and not remaining
        reversible_rows.append({'Toffoli_gates': r, 'qubits': 2 * r + 1,
                                'basis_inputs': 8, 'native_and_compiled': True, 'residual_T': 0})
    fidelity_rows = []
    for n, expected_count in [(1, 6), (2, 60), (3, 1080)]:
        states = all_stabilizers_float(n)
        assert len(states) == expected_count
        magic = evolve(n, sum(([('H', q), ('T', q)] for q in range(n)), []))
        magic_c = [a.as_complex() for a in magic]
        fidelity = max(abs(sum(a.conjugate() * b for a, b in zip(phi, magic_c))) ** 2 for phi in states)
        expected_fidelity = math.cos(math.pi / 8) ** (2 * n)
        assert abs(fidelity - expected_fidelity) < 1e-9
        fidelity_rows.append({'magic_qubits': n, 'all_stabilizers_enumerated': len(states),
                              'maximum_fidelity': fidelity, 'theory': expected_fidelity})
    parity_rows = []
    for r in range(1, 7):
        ops = sum(([('H', q), ('T', q)] for q in range(r)), []) + [('CX', q, r) for q in range(r)]
        psi = evolve(r + 1, ops)
        mu = projected(psi, r)
        assert norm(mu) == Q2(F(1, 2)) and inner(psi, mu) == C2(F(1, 2))
        parity_rows.append({'magic_qubits': r, 'acceptance_probability': '1/2',
                            'second_moment_lower_bound_eta_1_over_100':
                            float(qpow(XI, r) * F(49, 100) ** 2)})
    demos = []
    for n, ops, x, output in [(1, [('H', 0), ('T', 0), ('H', 0)], 0, 0),
                              (2, [('H', 0), ('T', 0), ('CX', 0, 1), ('H', 0)], 0, 0)]:
        exact = norm(projected(evolve(n, ops, x), output))
        estimate, config = reference_estimate(n, ops, x, output, F(1, 6), 0.05, rng)
        assert (Q2(F(1, 6)) - abs(estimate - exact)).sign() >= 0
        demos.append({'qubits': n, 'exact': float(exact), 'estimate': float(estimate),
                      'epsilon': '1/6', 'delta': 0.05, **config})
    result = {
        'scope': 'Internal bounded verification and dense reference, not a scalable CH-form implementation.',
        'arithmetic': 'Exact Q(sqrt(2), i) for branch means, raw bias, probe moments and parity probabilities.',
        'seed': 15006, 'one_qubit_circuits': one_count, 'seeded_multi_qubit_circuits': 64,
        'exact_projected_mean_checks': len(circuits), 'maximum_enumerated_trajectories': max_terms,
        'exact_M2_raw_bias_checks': pair_checks, 'exact_equatorial_moment_checks': probe_checks,
        'toffoli_compilation_exact_basis_checks': 8, 'reversible_prefix_checks': reversible_rows,
        'finite_stabilizer_fidelity_checks_float_tolerance_1e_minus9': fidelity_rows,
        'parity_magic_family_exact_checks': parity_rows, 'seeded_end_to_end_reference_runs': demos,
        'limits': ['No independent review requested or claimed.',
                   'The all-size fidelity theorem is sourced; finite enumeration is only a check.',
                   'Dense reference timing cannot support scalable runtime claims.',
                   'Two seeded estimator runs do not empirically establish a tail guarantee.']
    }
    path = Path(__file__).resolve().parents[1] / 'artifacts' / 'input-aware-estimator-checks.json'
    path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'passed', 'exact_mean_checks': len(circuits),
                      'probe_checks': probe_checks, 'artifact': str(path)}, indent=2))


if __name__ == '__main__':
    main()
