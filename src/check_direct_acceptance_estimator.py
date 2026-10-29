"""Bounded, independent dense/exhaustive checks for the S016 scalar estimator."""

from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random

from check_acceptance_estimator import Q2, toffoli_decomposition
from check_input_aware_estimator import Z, basis, gate, norm, projected
from direct_acceptance_estimator import (
    COEFFICIENTS, PROPOSAL, SECOND, choose_channels,
    classical_step, clifford_branch, clifford_expectation, estimate,
    power, prepare, sample_basis, stabilizers,
)


def dense(n, ops, x=0):
    v = basis(n, x)
    for op in ops:
        if op[0] == 'Z':
            v = gate(gate(v, ('S', op[1])), ('S', op[1]))
        else:
            v = gate(v, op)
    return v


class BitString:
    def __init__(self, value):
        self.value = value
        self.used = 0

    def getrandbits(self, count):
        result = (self.value >> self.used) & ((1 << count) - 1)
        self.used += count
        return result


def distribution(rows, n):
    counts = Counter(sample_basis(rows, n, BitString(value)) for value in range(1 << n))
    return {x: F(count, 1 << n) for x, count in counts.items()}


def suffix_probability(prepared, ops):
    if prepared.affine is not None:
        return F(1 - clifford_expectation(ops, prepared.basis_input, *prepared.affine), 2)
    result = F(0)
    for value, probability in distribution(stabilizers(prepared.n, ops, prepared.basis_input), prepared.n).items():
        for op in prepared.suffix:
            value = classical_step(value, op)
        result += probability * ((value >> prepared.output) & 1)
    return result


def exact_moments(prepared):
    mean, second = Q2(), Q2()
    for choices in product(range(3), repeat=prepared.k):
        proposal, coefficient = F(1), Q2(1)
        for choice in choices:
            proposal *= PROPOSAL[choice]
            coefficient *= COEFFICIENTS[choice]
        acceptance = suffix_probability(prepared, clifford_branch(prepared, choices))
        mean += coefficient * acceptance
        # Conditional expectation is used only for an affine terminal function.
        endpoint_second = acceptance * acceptance if prepared.affine is not None else acceptance
        second += coefficient * coefficient / proposal * endpoint_second
    return mean, second


def parity_family(r, interfering):
    ops = []
    for q in range(r):
        ops.extend([('H', q), ('T', q)])
        if interfering:
            ops.append(('H', q))
    ops.extend(('CX', q, r) for q in range(r))
    return ops


def main():
    rng = random.Random(16006)
    assert SECOND == Q2(F(23, 3), -4)
    assert sum(COEFFICIENTS, Q2()) == Q2(1)
    assert [choose_channels(1, BitString(i))[0] for i in range(8)] == [0, 0, 0, 1, 1, 1, 1, 2]
    # Check the channel identity on four linearly spanning density operators.
    spanning = [basis(1, 0), basis(1, 1), dense(1, [('H', 0)]), dense(1, [('H', 0), ('S', 0)])]
    channel_checks = 0
    for name in ('T', 'TDG'):
        for v in spanning:
            actual = gate(v, (name, 0))
            terms = [v, gate(v, ('S' if name == 'T' else 'SDG', 0)),
                     gate(gate(v, ('S', 0)), ('S', 0))]
            for a, b in product(range(2), repeat=2):
                rhs = sum((phi[a] * phi[b].conj() * c for c, phi in zip(COEFFICIENTS, terms)), Z)
                assert actual[a] * actual[b].conj() == rhs
            channel_checks += 1
    # Complete Z-output distributions check joint correlations and phase signs.
    measurement_checks = 0
    for n in range(1, 6):
        for _ in range(12):
            ops = []
            for _ in range(14):
                name = rng.choice(('H', 'S', 'SDG', 'X', 'Z', 'CX') if n > 1 else ('H', 'S', 'SDG', 'X', 'Z'))
                ops.append((name, *rng.sample(range(n), 2)) if name == 'CX' else (name, rng.randrange(n)))
            x = rng.randrange(1 << n)
            psi = dense(n, ops, x)
            actual = distribution(stabilizers(n, ops, x), n)
            assert all(Q2(actual.get(i, 0)) == a.norm() for i, a in enumerate(psi))
            for mask in range(1 << n):
                expected = sum((a.norm() * (-1) ** ((mask & i).bit_count()) for i, a in enumerate(psi)), Q2())
                assert Q2(clifford_expectation(ops, x, mask, 0)) == expected
            measurement_checks += 1
    circuits = []
    for length in range(5):
        for word in product(('H', 'S', 'T', 'TDG'), repeat=length):
            circuits.append((1, [(g, 0) for g in word], length % 2, 0))
    for _ in range(80):
        n = rng.choice((2, 3, 4))
        ops = []
        for _ in range(9):
            name = rng.choice(('H', 'S', 'SDG', 'T', 'TDG', 'CX', 'X', 'Z'))
            ops.append((name, *rng.sample(range(n), 2)) if name == 'CX' else (name, rng.randrange(n)))
        circuits.append((n, ops, rng.randrange(1 << n), rng.randrange(n)))
    for _ in range(32):
        ops = [('H', 0), ('H', 1)]
        for _ in range(5):
            ops.append((rng.choice(('H', 'T', 'TDG', 'S')), rng.randrange(2)))
        ops.append(('CCX', 0, 1, 2))
        circuits.append((3, ops, rng.randrange(8), 2))
    circuits.extend([(3, [('H', 0), ('H', 1), ('CCX', 0, 1, 2), ('H', 2)], 0, 2),
                     (3, [('H', 0), ('H', 1), ('CCX', 0, 1, 2), ('H', 0)], 0, 0)])
    maximum_k, nonlinear = 0, 0
    for n, ops, x, output in circuits:
        prepared = prepare(n, ops, x, output)
        maximum_k = max(maximum_k, prepared.k)
        nonlinear += prepared.affine is None
        mean, second = exact_moments(prepared)
        actual = norm(projected(dense(n, ops, x), output))
        assert mean == actual, (n, ops, x, output, mean, actual)
        assert (second - mean * mean).sign() >= 0
        assert (power(SECOND, prepared.k) - second).sign() >= 0
    diagnostics = []
    for r in (1, 2, 4, 8, 16, 32, 64, 128):
        reversible = [('CCX', 2 * i, 2 * i + 1, 2 * r) for i in range(r)]
        compiled = sum((toffoli_decomposition(*op[1:]) for op in reversible), [])
        for ops in (reversible, compiled):
            for x in (0, (1 << (2 * r + 1)) - 1):
                prepared = prepare(2 * r + 1, ops, x, 2 * r)
                expected = x
                for op in reversible:
                    expected = classical_step(expected, op)
                result = estimate(prepared, rng=BitString(0))
                assert result['exact'] and result['samples'] == 0
                assert F(result['estimate']) == ((expected >> (2 * r)) & 1)
        prepared = prepare(r + 1, parity_family(r, False), 0, r)
        result = estimate(prepared, rng=BitString(0))
        assert prepared.k == 0 and result['exact'] and F(result['estimate']) == F(1, 2)
        diagnostics.append({'r': r, 'reversible_qubits': 2 * r + 1, 'native_and_compiled': True,
                            'magic_parity_qubits': r + 1, 'magic_parity_result': '1/2', 'samples': 0})
    # Exact local phase cancellation must remove a trivial T^8 identity.
    cancelled = prepare(1, [('H', 0)] + [('T', 0)] * 32 + [('H', 0)])
    assert estimate(cancelled)['estimate'] == '0' and cancelled.k == 0
    variance_rows = []
    d0, d1, d2 = tuple(c * c / p for c, p in zip(COEFFICIENTS, PROPOSAL))
    for r in range(1, 7):
        prepared = prepare(r + 1, parity_family(r, True), 0, r)
        assert prepared.k == r and prepared.affine is not None
        mean, second = exact_moments(prepared)
        predicted_p = (Q2(1) - power(Q2(0, F(1, 2)), r)) / 2
        predicted_second = (power(SECOND, r) - 2 * power(d0 - d2, r) + power(d0 + d2, r)) / 4
        assert mean == predicted_p and second == predicted_second
        assert (second - power(SECOND, r) / 6).sign() >= 0
        variance_rows.append({'r': r, 'k': prepared.k, 'probability': float(mean),
                              'second_moment': float(second), 'variance': float(second - mean * mean)})
    assert (SECOND - 6 * (d0 - d2)).sign() >= 0  # exact all-size lower-bound premise
    try:
        estimate(prepare(1, [('H', 0), ('T', 0), ('H', 0)]), max_samples=0, rng=BitString(0))
        raise AssertionError('A sample cap was silently ignored')
    except ValueError as exc:
        assert 'no estimate produced' in str(exc)
    demos = []
    examples = [(1, [('H', 0), ('T', 0), ('H', 0)], 0),
                (3, [('H', 0), ('T', 0), ('H', 1), ('T', 1), ('CCX', 0, 1, 2)], 2),
                (3, [('H', 0), ('T', 0), ('H', 0), ('H', 1), ('CCX', 0, 1, 2)], 2)]
    for n, ops, output in examples:
        prepared = prepare(n, ops, 0, output)
        result = estimate(prepared, F(1, 4), F(1, 4), rng)
        actual = norm(projected(dense(n, ops), output))
        assert (Q2(F(1, 4)) - abs(Q2(F(result['estimate'])) - actual)).sign() >= 0
        demos.append({'qubits': n, 'exact_probability': float(actual), **result})
    artifact = {
        'status': 'passed', 'seed': 16006,
        'scope': 'Exact bounded verification plus bit-packed scalable estimator checks; no independent review.',
        'channel_identity_spanning_inputs': channel_checks,
        'full_clifford_measurement_distributions': measurement_checks,
        'exact_acceptance_and_second_moment_checks': len(circuits),
        'maximum_enumerated_internal_T': maximum_k,
        'nonlinear_terminal_cases': nonlinear,
        'old_diagnostics': diagnostics, 'interfering_parity_variance': variance_rows,
        'phase_fusion_identity': 'passed', 'sample_cap': 'passed', 'seeded_end_to_end_runs': demos,
        'limitations': ['Finite checks do not establish complexity bounds or a statistical tail theorem.',
                        'All-size costs and error/variance arguments are in the mathematical note.',
                        'Fixed channel proposal and terminal rule are not an optimized universal simulator.']}
    path = Path(__file__).resolve().parents[1] / 'artifacts' / 'direct-acceptance-estimator-checks.json'
    path.write_text(json.dumps(artifact, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': 'passed', 'exact_acceptance_checks': len(circuits),
                      'measurement_distributions': measurement_checks, 'artifact': str(path)}, indent=2))


if __name__ == '__main__':
    main()
