"""S016 direct scalar estimator with exact arithmetic and bit-packed stabilizers.

No statevectors or enumeration of channel trajectories are used by this module.
The gate model is H, S, SDG, T, TDG, X, Z, CX and the exact CCX macro.
See proofs/direct-acceptance-estimator-2026-10-06.md for costs and limitations.
"""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key, lru_cache
import json
from pathlib import Path
import random

from check_acceptance_estimator import Q2, toffoli_decomposition


COEFFICIENTS = (Q2(F(1, 2)), Q2(0, F(1, 2)), Q2(F(1, 2), F(-1, 2)))
PROPOSAL = (F(3, 8), F(1, 2), F(1, 8))
WEIGHTS = tuple(c / q for c, q in zip(COEFFICIENTS, PROPOSAL))
SECOND = sum((c * c / q for c, q in zip(COEFFICIENTS, PROPOSAL)), Q2())
PHASES = {'T': 1, 'S': 2, 'Z': 4, 'SDG': 6, 'TDG': 7}
PHASE_WORDS = ((), ('T',), ('S',), ('S', 'T'), ('Z',), ('Z', 'T'), ('SDG',), ('TDG',))


def power(a, k):
    result = Q2(1)
    while k:
        if k & 1:
            result *= a
        a *= a
        k >>= 1
    return result


def ceil_exact(a):
    """Integer ceiling without conversion to floating point."""
    bound = abs(a.a) + 2 * abs(a.b) + 1
    high = bound.numerator // bound.denominator + 2
    low = -high
    while low + 1 < high:
        middle = (low + high) // 2
        if (Q2(middle) - a).sign() >= 0:
            high = middle
        else:
            low = middle
    return high


def multiply(left, right):
    """Paulis use i^r X^x Z^z, with all X factors before all Z factors."""
    x, z, r = left
    u, v, s = right
    return x ^ u, z ^ v, (r + s + 2 * (z & u).bit_count()) % 4


def conjugate(pauli, op):
    """Return G P G-dagger for a Clifford gate G."""
    x, z, r = pauli
    name, q, *rest = op
    xb, zb = (x >> q) & 1, (z >> q) & 1
    if name == 'H':
        r += 2 * xb * zb
        if xb != zb:
            x ^= 1 << q
            z ^= 1 << q
    elif name in ('S', 'SDG'):
        r += xb if name == 'S' else -xb
        z ^= xb << q
    elif name == 'X':
        r += 2 * zb
    elif name == 'Z':
        r += 2 * xb
    elif name == 'CX':
        target = rest[0]
        x ^= xb << target
        z ^= ((z >> target) & 1) << q
    else:
        raise ValueError('Not a Clifford gate: ' + str(op))
    return x, z, r % 4


def clifford_expectation(ops, basis_input, mask, sign):
    pauli = (0, mask, 2 * sign)
    for op in reversed(ops):
        name = {'S': 'SDG', 'SDG': 'S'}.get(op[0], op[0])
        pauli = conjugate(pauli, (name, *op[1:]))
    x, z, r = pauli
    if x:
        return 0
    assert r % 2 == 0
    return (-1) ** ((r // 2 + (z & basis_input).bit_count()) % 2)


def stabilizers(n, ops, basis_input):
    rows = [(0, 1 << q, 2 * ((basis_input >> q) & 1)) for q in range(n)]
    for op in ops:
        rows = [conjugate(row, op) for row in rows]
    return tuple(rows)


def measure_z(rows, n, q, rng):
    """Measure in place; n independent commuting generators, no destabilizers."""
    pivot = next((i for i, row in enumerate(rows) if (row[0] >> q) & 1), None)
    if pivot is not None:
        old = rows[pivot]
        for i, row in enumerate(rows):
            if i != pivot and (row[0] >> q) & 1:
                rows[i] = multiply(row, old)
        bit = rng.getrandbits(1)
        rows[pivot] = (0, 1 << q, 2 * bit)
        return bit
    echelon = {}
    for row in rows:
        current = row
        while current[0] or current[1]:
            key = (current[0] | (current[1] << n)).bit_length() - 1
            if key not in echelon:
                echelon[key] = current
                break
            current = multiply(current, echelon[key])
    target = (0, 1 << q, 0)
    while target[0] or target[1]:
        key = (target[0] | (target[1] << n)).bit_length() - 1
        target = multiply(target, echelon[key])
    assert target[2] % 2 == 0
    return target[2] // 2


def sample_basis(rows, n, rng):
    working = list(rows)
    result = 0
    for q in range(n):
        result |= measure_z(working, n, q, rng) << q
    return result


def classical_step(bits, op):
    if op[0] in ('X', 'CX', 'CCX'):
        if all((bits >> q) & 1 for q in op[1:-1]):
            bits ^= 1 << op[-1]
    else:
        assert op[0] in PHASES
    return bits


def recognize_macros(ops):
    result, i, count = [], 0, 0
    while i < len(ops):
        chunk = ops[i:i + 15]
        if (len(chunk) == 15 and chunk[0][0] == 'H'
                and chunk[1][0] == chunk[3][0] == 'CX'):
            t, b, a = chunk[0][1], chunk[1][1], chunk[3][1]
            if len({a, b, t}) == 3 and chunk == toffoli_decomposition(a, b, t):
                result.append(('CCX', a, b, t))
                i += 15
                count += 1
                continue
        result.append(ops[i])
        i += 1
    return result, count


def fuse_local(ops):
    result = []
    for op in ops:
        if op[0] in PHASES:
            exponent, q = PHASES[op[0]], op[1]
            while result and result[-1][0] in PHASES and result[-1][1] == q:
                exponent += PHASES[result.pop()[0]]
            result.extend((g, q) for g in PHASE_WORDS[exponent % 8])
        elif result and result[-1] == op and op[0] in ('H', 'X', 'CX', 'CCX'):
            result.pop()
        else:
            result.append(op)
    return result


@dataclass(frozen=True)
class Prepared:
    n: int
    basis_input: int
    output: int
    prefix: tuple
    suffix: tuple
    affine: object
    k: int
    recognized_macros: int
    pruned_gates: int


def prepare(n, gates, basis_input=0, output=0):
    if not isinstance(n, int) or n <= 0 or not 0 <= basis_input < (1 << n) or not 0 <= output < n:
        raise ValueError('Invalid qubit count, basis input or output wire')
    ops = [tuple(op) for op in gates]
    arities = {name: 1 for name in ('H', 'S', 'SDG', 'T', 'TDG', 'X', 'Z')}
    arities.update(CX=2, CCX=3)
    for op in ops:
        if (not op or op[0] not in arities or len(op) != arities[op[0]] + 1
                or any(not isinstance(q, int) or not 0 <= q < n for q in op[1:])
                or len(set(op[1:])) != len(op) - 1):
            raise ValueError('Invalid gate: ' + str(op))
    ops, recognized = recognize_macros(ops)
    cone, retained = {output}, []
    for op in reversed(ops):
        if cone.intersection(op[1:]):
            cone.update(op[1:])
            retained.append(op)
    pruned = len(ops) - len(retained)
    ops = fuse_local(list(reversed(retained)))
    # One deterministic insertion pass: H only crosses disjoint non-H gates.
    for i in range(len(ops)):
        if ops[i][0] == 'H':
            j = i
            while j and ops[j - 1][0] != 'H' and set(ops[j][1:]).isdisjoint(ops[j - 1][1:]):
                ops[j - 1], ops[j] = ops[j], ops[j - 1]
                j -= 1
    ops = fuse_local(ops)
    removed = 0
    for op in ops:
        if op[0] == 'H':
            break
        basis_input = classical_step(basis_input, op)
        removed += 1
    ops = ops[removed:]
    cut = max((i + 1 for i, op in enumerate(ops) if op[0] == 'H'), default=0)
    prefix = []
    for op in ops[:cut]:
        prefix.extend(toffoli_decomposition(*op[1:]) if op[0] == 'CCX' else [op])
    suffix = tuple(op for op in ops[cut:] if op[0] not in PHASES)
    mask, sign, affine = 1 << output, 0, True
    for op in reversed(suffix):
        if not (mask >> op[-1]) & 1:
            continue
        if op[0] == 'X':
            sign ^= 1
        elif op[0] == 'CX':
            mask ^= 1 << op[1]
        else:
            affine = False
            break
    return Prepared(n, basis_input, output, tuple(prefix), suffix,
                    (mask, sign) if affine else None,
                    sum(op[0] in ('T', 'TDG') for op in prefix), recognized, pruned)


def clifford_branch(prepared, choices):
    it, result = iter(choices), []
    for op in prepared.prefix:
        if op[0] not in ('T', 'TDG'):
            result.append(op)
        else:
            choice = next(it)
            if choice:
                result.append((('S' if op[0] == 'T' else 'SDG') if choice == 1 else 'Z', op[1]))
    return tuple(result)


def branch_weight(counts):
    result = Q2(1)
    for value, count in zip(WEIGHTS, counts):
        result *= power(value, count)
    return result


def choose_channels(k, rng):
    choices = []
    for _ in range(k):
        bits = rng.getrandbits(3)
        choices.append(0 if bits < 3 else 1 if bits < 7 else 2)
    return tuple(choices)


def sample_configuration(k, epsilon, delta):
    epsilon, delta = F(epsilon), F(delta)
    if not 0 < epsilon <= 1 or not 0 < delta < 1:
        raise ValueError('Require 0 < epsilon <= 1 and 0 < delta < 1')
    bound = ceil_exact(power(SECOND, k))
    per_batch = ceil_exact(Q2(64 * bound / (epsilon * epsilon)))
    ell = 0
    while delta * (1 << ell) < 1:
        ell += 1
    batches = (8 * ell) | 1
    return per_batch, batches, bound


def estimate(prepared, epsilon=F(1, 6), delta=F(1, 20), rng=None, max_samples=1_000_000):
    epsilon, delta = F(epsilon), F(delta)
    if not 0 < epsilon <= 1 or not 0 < delta < 1:
        raise ValueError('Require 0 < epsilon <= 1 and 0 < delta < 1')
    if prepared.k == 0 and prepared.affine is not None:
        z = clifford_expectation(prepared.prefix, prepared.basis_input, *prepared.affine)
        return {'estimate': str(F(1 - z, 2)), 'exact': True, 'samples': 0, 'residual_T': 0}
    m, batches, bound = sample_configuration(prepared.k, epsilon, delta)
    required = m * batches
    if max_samples is not None and required > max_samples:
        raise ValueError(f'Sample cap exceeded: required {required}, cap {max_samples}; no estimate produced')
    rng = rng if rng is not None else random.SystemRandom()

    @lru_cache(maxsize=256)
    def endpoint(choices):
        ops = clifford_branch(prepared, choices)
        if prepared.affine is not None:
            return 1 - clifford_expectation(ops, prepared.basis_input, *prepared.affine)
        return stabilizers(prepared.n, ops, prepared.basis_input)

    values = []
    for _ in range(batches):
        # Counts compress equal scalar weights, not quantum states; O(k^2) keys.
        accepted = Counter()
        for _ in range(m):
            choices = choose_channels(prepared.k, rng)
            data = endpoint(choices)
            if prepared.affine is not None:
                twice_acceptance = data
            else:
                bits = sample_basis(data, prepared.n, rng)
                for op in prepared.suffix:
                    bits = classical_step(bits, op)
                twice_acceptance = 2 * ((bits >> prepared.output) & 1)
            if twice_acceptance:
                counts = tuple(choices.count(i) for i in range(3))
                accepted[counts] += twice_acceptance
        values.append(sum((branch_weight(key) * F(count, 2 * m)
                           for key, count in accepted.items()), Q2()))
    values.sort(key=cmp_to_key(lambda a, b: (a - b).sign()))
    median = values[len(values) // 2]
    grid = 1
    while F(1, grid) > epsilon / 4:
        grid <<= 1
    ceiling = ceil_exact(median * grid)
    floor = ceiling if median * grid == Q2(ceiling) else ceiling - 1
    nearest = floor + int((median * (2 * grid) - (2 * floor + 1)).sign() >= 0)
    result = min(F(1), max(F(0), F(nearest, grid)))
    return {'estimate': str(result), 'exact': False, 'samples': required,
            'samples_per_batch': m, 'batches': batches, 'residual_T': prepared.k,
            'second_moment_upper_bound_ceiling': bound, 'epsilon': str(epsilon),
            'delta': str(delta), 'affine_terminal': prepared.affine is not None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('circuit', type=Path, help='JSON with n, gates, input, output, epsilon and delta')
    parser.add_argument('--seed', type=int, help='Optional reproducible pseudorandom diagnostic seed')
    parser.add_argument('--max-samples', type=int, default=1_000_000)
    args = parser.parse_args()
    data = json.loads(args.circuit.read_text(encoding='utf-8'))
    prepared = prepare(data['n'], data['gates'], data.get('input', 0), data.get('output', 0))
    result = estimate(prepared, F(data.get('epsilon', '1/6')), F(data.get('delta', '1/20')),
                      random.Random(args.seed) if args.seed is not None else None, args.max_samples)
    result['randomness'] = 'seeded diagnostic' if args.seed is not None else 'system random bits'
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
