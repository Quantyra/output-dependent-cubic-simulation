"""Exact finite checks for S158; no ETH solver or Lean build is invoked."""
import hashlib
import json
import random
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path

from eth_acceptance_encoding import (PHASES, CNF, acceptance_interval,
    cyclotomic_sum, encode_acceptance, reference_buckets, truth, validate)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mul(a, b):
    out = [0] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % 4] += x * y * (-1 if i + j >= 4 else 1)
    return tuple(out)


def omega(k):
    out = [0] * 4
    out[k % 4] = 1 if k % 8 < 4 else -1
    return tuple(out)


def conjugate(a):
    out = ZERO
    for j, coefficient in enumerate(a):
        out = add(out, tuple(coefficient * v for v in omega(-j)))
    return out


def dense_numerator(n, gates, basis, output):
    """Independent exact statevector with a common 2^(-h/2) scale."""
    state = [ZERO] * (2 ** n)
    state[basis] = ONE
    h = 0
    for gate in validate(n, gates, basis, output):
        name, q = gate[:2]
        if name == 'H':
            nxt = [ZERO] * len(state)
            for x, amplitude in enumerate(state):
                for y in (0, 1):
                    target = (x & ~(1 << q)) | (y << q)
                    sign = -1 if ((x >> q) & y) else 1
                    nxt[target] = add(nxt[target], tuple(sign * v for v in amplitude))
            h += 1
            state = nxt
        elif name in {'X', 'CX'}:
            nxt = [ZERO] * len(state)
            for x, amplitude in enumerate(state):
                target = x ^ (1 << q) if name == 'X' else x ^ (((x >> q) & 1) << gate[2])
                nxt[target] = amplitude
            state = nxt
        else:
            state = [mul(a, omega(PHASES[name] * ((x >> q) & 1))) for x, a in enumerate(state)]
    result = ZERO
    for x, amplitude in enumerate(state):
        if x >> output & 1:
            result = add(result, mul(amplitude, conjugate(amplitude)))
    return result, h


def sat(clauses, values):
    return all(any(values[abs(v)] == (v > 0) for v in c) for c in clauses)


def check_gadgets():
    checks = 0
    for name, arity in (('XOR', 2), ('AND', 2), ('NOT', 1)):
        cnf = CNF()
        args = [cnf.fresh() for _ in range(arity)]
        out = cnf.gate(name, *args)
        for bits in product((0, 1), repeat=arity):
            good = []
            for answer in (0, 1):
                values = dict(zip(args, bits)) | {out: answer}
                if sat(cnf.clauses, values):
                    good.append(answer)
                checks += 1
            require(good == [truth(name, bits)], 'gate is not parsimonious')
    return checks


def check_circuits():
    rng = random.Random(158026)
    cases = [
        ('zero', 1, [], 0, 0), ('one', 1, [], 1, 0),
        ('H', 1, [('H', 0)], 0, 0),
        ('HH-cancellation', 1, [('H', 0), ('H', 0)], 0, 0),
        ('HTH-interference', 1, [('H', 0), ('T', 0), ('H', 0)], 0, 0),
        ('bell', 2, [('H', 0), ('CX', 0, 1)], 0, 1),
        ('uncompute', 2, [('H', 0), ('CX', 0, 1), ('CX', 0, 1), ('H', 0)], 0, 0),
        ('interleaved', 2, [('H', 0), ('H', 1), ('T', 1), ('CX', 1, 0), ('H', 0), ('SDG', 1), ('H', 1)], 0, 1),
        ('inverse-phases', 1, [('H', 0), ('T', 0), ('TDG', 0), ('S', 0), ('SDG', 0), ('H', 0)], 0, 0),
    ]
    for i in range(36):
        n = 1 + i % 3
        gates = []
        for _ in range(3 + i % 7):
            name = rng.choice(['H', 'H', 'X', 'T', 'TDG', 'S', 'SDG', 'Z', 'CX'] if n > 1 else ['H', 'H', 'X', 'T', 'TDG', 'S', 'SDG', 'Z'])
            q = rng.randrange(n)
            gates.append((name, q, (q + rng.randrange(1, n)) % n) if name == 'CX' else (name, q))
        if sum(g[0] == 'H' for g in gates) > 5:
            continue
        cases.append((f'seeded-{i}', n, gates, rng.randrange(2 ** n), rng.randrange(n)))
    records, assignments = [], 0
    for name, n, gates, basis, output in cases:
        cnf, phase, h = encode_acceptance(n, gates, basis, output)
        require(all(1 <= len(c) <= 3 for c in cnf.clauses), 'width')
        require(len(cnf.inputs) == 2 * h, 'path bit count')
        require(len(cnf.clauses) + 3 <= 5 * cnf.variables, 'fixed density')
        buckets = reference_buckets(cnf, phase)
        functional = [0] * 8
        for bits in product((0, 1), repeat=2 * h):
            values = cnf.evaluate(bits)
            if sat(cnf.clauses, values):
                functional[sum(values[v] << j for j, v in enumerate(phase))] += 1
            assignments += 1
        require(buckets == functional, 'DPLL/functional count disagreement')
        numerator, dense_h = dense_numerator(n, gates, basis, output)
        require(h == dense_h and cyclotomic_sum(buckets) == numerator, 'dense probability disagreement')
        lo, hi = acceptance_interval(buckets, h, h + 4)
        require(hi - lo <= Q(1, 16), 'precision budget')
        require(hi >= 0 and lo <= 1, 'interval misses physical range')
        require(all(buckets[j] == buckets[-j % 8] for j in range(8)), 'conjugacy')
        records.append({'name': name, 'qubits': n, 'gates': len(gates), 'hadamards': h,
                        'variables': cnf.variables, 'clauses_per_bucket': len(cnf.clauses) + 3,
                        'buckets': buckets, 'numerator_in_Z_omega': numerator,
                        'denominator': 2 ** h, 'interval': [str(lo), str(hi)]})
    cancellation = next(r for r in records if r['name'] == 'HH-cancellation')
    require(sum(cancellation['buckets']) > 0 and not any(cancellation['numerator_in_Z_omega']),
            'missing destructive-interference control')
    return records, assignments


def padd(a, b):
    return [ (a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
             for i in range(max(len(a), len(b))) ]


def pmul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def compose_linear(poly, t, alpha=1):
    out, power = [Q(0)], [Q(1)]
    for coefficient in poly:
        out = padd(out, [coefficient * x for x in power])
        power = pmul(power, [Q(t), Q(alpha)])
    return out


def kernel(L, x, y):
    denominator = 1
    for q in range(-L, L):
        if q:
            denominator *= -q
    out = [Q(1, denominator)]
    for q in range(-L, L):
        if q != y - x:
            out = pmul(out, [Q(-q), Q(1)])
    return out


def modq(value, p):
    value = Q(value)
    require(value.denominator % 2 == 1, 'nonintegral 2-adic coefficient')
    return value.numerator * pow(value.denominator, -1, 2 ** p) % (2 ** p)


def solve(matrix, rhs):
    a = [list(row) + [value] for row, value in zip(matrix, rhs)]
    for j in range(len(a)):
        pivot = next(i for i in range(j, len(a)) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        divisor = a[j][j]
        a[j] = [x / divisor for x in a[j]]
        for i in range(len(a)):
            if i != j:
                multiplier = a[i][j]
                a[i] = [x - multiplier * y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def check_deformation():
    kernel_checks = mode_checks = 0
    for L in (2, 4):
        for x, y in product(range(L), repeat=2):
            w = kernel(L, x, y)
            require(w[0] == int(x == y), 'W(0) is not identity')
            for t in range(-L, L):
                shifted = compose_linear(w, t, 2 * L)
                require(all(c.denominator % 2 for c in shifted), '2-adic integrality')
                if t != y - x:
                    require(all(c.numerator % 2 == 0 for c in shifted), 'missing crossing divisibility')
                    require(shifted[0] == 0, 'node not local')
                kernel_checks += 1
                if t == 0:
                    continue
                i = (abs(t) & -abs(t)).bit_length() - 1
                if (x >> i & 1) != (y >> i & 1):
                    continue
                step = 2 ** (i + 1)
                y0, j = y % step, y // step
                for zeta, p in product((1, 3), (3, 5, 7)):
                    T = t + 2 * L * zeta
                    c = Q(1)
                    denominator = 1
                    for q in range(-L, L):
                        c *= T - q
                        if q:
                            denominator *= -q
                    leading = c / (denominator * (T - y0 + x))
                    ratio = Q(step, T - y0 + x)
                    expanded = sum((leading * ratio ** b * j ** b for b in range(p - 1)), Q(0))
                    actual = compose_linear(w, T)[0]
                    require(modq(expanded, p) == modq(actual, p), 'mode expansion')
                    mode_checks += 1
    rng = random.Random(158)
    interpolation_checks = 0
    L = M = 2
    W = [[kernel(L, x, y) for y in range(M)] for x in range(M)]
    assignments = list(product((0, 1), repeat=M))
    for _ in range(12):
        left = {bits: rng.randrange(-3, 4) for bits in assignments}
        right = {bits: rng.randrange(-3, 4) for bits in assignments}
        F = [Q(0)]
        for X, Y in product(assignments, repeat=2):
            term = [Q(left[Y] * right[X])]
            for x in range(M):
                form = [Q(0)]
                for y in range(M):
                    form = padd(form, [c * X[y] for c in W[x][y]])
                if Y[x] == 0:
                    form = padd([Q(1)], [-c for c in form])
                term = pmul(term, form)
            F = padd(F, term)
        direct = sum(left[x] * right[x] for x in assignments)
        require(F[0] == direct, 'deformation changed original contraction')
        matrix, rhs = [], []
        for t in (-2, -1, 1):
            shifted = compose_linear(F, t)
            for derivative in range(3):
                matrix.append([Q(comb(j, derivative) * t ** (j - derivative)) if j >= derivative else Q(0)
                               for j in range(9)])
                rhs.append(shifted[derivative])
        recovered = solve(matrix, rhs)
        require(recovered == F + [Q(0)] * (9 - len(F)), 'Hermite recovery')
        interpolation_checks += 1
    return {'kernel_node_checks': kernel_checks, 'modular_mode_checks': mode_checks,
            'signed_tensor_Hermite_recoveries': interpolation_checks}


def check_rejections():
    bad = [(0, [], 0, 0), (1, [('CX', 0, 0)], 0, 0), (1, [('RX', 0)], 0, 0),
           (1, [('H', 1)], 0, 0), (1, [], 2, 0), (1, [], 0, 1)]
    for args in bad:
        try:
            encode_acceptance(*args)
        except ValueError:
            continue
        raise AssertionError('invalid source accepted')
    cnf, phase, _ = encode_acceptance(1, [('H', 0)] * 6)
    try:
        reference_buckets(cnf, phase)
    except ValueError:
        return len(bad) + 1
    raise AssertionError('reference cap not enforced')


def construction_ledger():
    rows = []
    for n in (1, 2, 4, 8, 16, 32):
        gates = ([('H', j) for j in range(n)] + [('T', j) for j in range(n)]
                 + [('CX', j, j + 1) for j in range(n - 1)]
                 + [('H', j) for j in range(n)])
        cnf, _, h = encode_acceptance(n, gates)
        clauses = len(cnf.clauses) + 3
        require(cnf.variables <= n + 2 + 28 * len(gates), 'linear variable budget')
        require(clauses <= 5 * cnf.variables, 'clause density budget')
        rows.append({'qubits': n, 'native_gates': len(gates), 'variables': cnf.variables,
                     'clauses_per_bucket': clauses, 'exact_count_bits': 2 * h + 1,
                     'subdivided_tensor_edges_upper_bound': 12 * clauses,
                     'counting_run': False})
    # At root u=floor(epsilon*lambda), epsilon=2^-17. The appendix requires
    # u>=lambda^(4/5), hence lambda>=epsilon^-5=2^85. Exact integer check.
    inverse_epsilon = 128 * 1024
    require(inverse_epsilon ** 5 == 2 ** 85, 'literal parameter cutoff')
    return {'connected_source_encodings': rows,
            'literal_appendix_root_necessary_log2_size': str(2 ** 85),
            'cutoff_is_not_a_lower_bound_on_other_algorithms': True}


def main():
    gadgets = check_gadgets()
    cases, assignments = check_circuits()
    result = {'story': 'S158', 'status': 'passed', 'arithmetic': 'exact integers and fractions',
              'scope': 'transfer compiler and finite algebraic ingredients; not an ETH solver or full proof audit',
              'gate_truth_table_checks': gadgets, 'circuit_cases': len(cases),
              'DPLL_bucket_counts': 8 * len(cases), 'functional_path_assignments': assignments,
              'deformation': check_deformation(), 'refusal_checks': check_rejections(),
              'construction_ledger': construction_ledger(),
              'cases': cases,
              'source_sha256': {name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                  for name in ('eth_acceptance_encoding.py', 'check_eth_acceptance_transfer.py')}}
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({k: v for k, v in result.items() if k not in {'cases', 'source_sha256', 'construction_ledger'}}, indent=2))
    else:
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
