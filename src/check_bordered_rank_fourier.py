"""Exact finite tests of distinguished-entry orbit classification and updates."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import random
from bordered_rank_fourier import (
    binary_rank, classify, bordered_kernel, rectangular_kernel,
    representative, evolve, compile_circuit, round_probability)
from rank_orbit_fourier import (
    rank_matrix, native_records, acceptance_numerator)
from check_rank_orbit_fourier import span_rank, dense_fourier
from check_acceptance_estimator import Q2
from check_eth_acceptance_transfer import ZERO, ONE, add, mul, omega, conjugate


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def action(x, m, A, B):
    rows = [(x >> (i*m)) & ((1 << m)-1) for i in range(m)]
    left, right = [1]+[v << 1 for v in A], [1]+[v << 1 for v in B]
    out = []
    for row in left:
        value = 0
        for j in range(m):
            if row >> j & 1:
                value ^= rows[j]
        result = 0
        for j in range(m):
            if value >> j & 1:
                result ^= right[j]
        out.append(result)
    return sum(v << (i*m) for i, v in enumerate(out))


def dense_data(m, ops):
    v, k = [ONE]+[ZERO]*((1 << (m*m))-1), 0
    ranks = [span_rank(x, m) for x in range(len(v))]
    phases = {'T0': 1, 'TDG0': 7, 'S0': 2, 'SDG0': 6, 'Z0': 4}
    for op in ops:
        if op == 'H':
            v, k = dense_fourier(v), k+m*m
        elif op == 'H0':
            old, v = v, []
            for x in range(0, len(old), 2):
                v += [add(old[x], old[x+1]),
                      add(old[x], tuple(-a for a in old[x+1]))]
            k += 1
        elif op == 'X0':
            v = [v[x ^ 1] for x in range(len(v))]
        elif isinstance(op, str):
            v = [mul(a, omega(phases[op]*(x & 1))) for x, a in enumerate(v)]
        else:
            v = [mul(a, omega(op[r])) for a, r in zip(v, ranks)]
    return v, k, ranks


def inverse_ops(ops):
    inv = {'H': 'H', 'H0': 'H0', 'X0': 'X0', 'T0': 'TDG0',
           'TDG0': 'T0', 'S0': 'SDG0', 'SDG0': 'S0', 'Z0': 'Z0'}
    return [inv[op] if isinstance(op, str) else [(-x) % 8 for x in op]
            for op in reversed(ops)]


def sparse_native(gates):
    v, h, high = {0: ONE}, 0, 1
    phases = {'T': 1, 'TDG': 7, 'S': 2, 'SDG': 6, 'Z': 4}
    for gate in gates:
        name, q = gate[:2]
        if name == 'H':
            nxt = {}
            for x, a in v.items():
                for bit in range(2):
                    y = (x & ~(1 << q)) | (bit << q)
                    sign = -1 if bit and (x >> q & 1) else 1
                    nxt[y] = add(nxt.get(y, ZERO), tuple(sign*t for t in a))
            v, h = {x: a for x, a in nxt.items() if a != ZERO}, h+1
            while h >= 2 and all(not (c & 1) for a in v.values() for c in a):
                v = {x: tuple(c//2 for c in a) for x, a in v.items()}
                h -= 2
        elif name == 'X':
            v = {x ^ (1 << q): a for x, a in v.items()}
        elif name == 'CX':
            v = {x ^ (((x >> q) & 1) << gate[2]): a for x, a in v.items()}
        elif name in phases:
            v = {x: mul(a, omega(phases[name])) if x >> q & 1 else a
                 for x, a in v.items()}
        else:
            raise AssertionError('non-native source record')
        require(bool(v), 'zero state under unitary')
        high = max(high, len(v))
    return v, h, high


def main():
    counts = dict(rectangular_coefficients=0, classified_matrices=0,
                  full_group_orbits=0, Fourier_coefficients=0,
                  transform_identities=0, circuits=0, state_coordinates=0,
                  acceptance=0, precision=0, native_sources=0,
                  symmetry_breaks=0)
    for a, b in product(range(4), repeat=2):
        K = rectangular_kernel(a, b)
        for rho, row in enumerate(K):
            y = sum(1 << (i*b+i) for i in range(rho))
            actual = [0]*(min(a, b)+1)
            for x in range(1 << (a*b)):
                rank = binary_rank([(x >> (i*b)) & ((1 << b)-1) for i in range(a)])
                actual[rank] += -1 if (x & y).bit_count() & 1 else 1
            require(tuple(actual) == row, 'rectangular character sum')
            counts['rectangular_coefficients'] += len(row)
    rng, native_records_out, large = random.Random(173042), [], []
    for m in range(1, 4):
        labels, reps, K, pops = bordered_kernel(m)
        W = len(labels)
        require(W == (2 if m == 1 else 20*m-24), 'orbit dimension formula')
        groups = defaultdict(set)
        for x in range(1 << (m*m)):
            groups[classify(x, m)].add(x)
            counts['classified_matrices'] += 1
        require(set(groups) == set(labels), 'orbit label completeness')
        n = m-1
        GL = [rows for rows in product(range(1 << n), repeat=n)
              if binary_rank(rows) == n]
        for j, (label, x) in enumerate(zip(labels, reps)):
            orbit = {action(x, m, A, B) for A, B in product(GL, repeat=2)}
            require(orbit == groups[label], 'classification differs from full group orbit')
            require(pops[j] == len(orbit), 'orbit population')
            counts['full_group_orbits'] += 1
        for row, y in zip(K, reps):
            actual = [sum(-1 if (x & y).bit_count() & 1 else 1 for x in groups[label])
                      for label in labels]
            require(tuple(actual) == row, 'bordered Fourier character sum')
            counts['Fourier_coefficients'] += W
        for r, s in product(range(W), repeat=2):
            require(sum(K[r][j]*K[j][s] for j in range(W)) ==
                    ((1 << (m*m)) if r == s else 0), 'Fourier inversion')
            require(sum(pops[j]*K[j][r]*K[j][s] for j in range(W)) ==
                    (pops[r]*(1 << (m*m)) if r == s else 0), 'weighted isometry')
            counts['transform_identities'] += 2
        bank = [[], ['H', 'T0', 'H'],
                ['H', 'T0', [0]*m+[3], 'H0', 'S0', 'H'],
                ['H0', [s % 8 for s in range(m+1)], 'X0', 'H']]
        for trial in range(10):
            seq = []
            for layer in range(1+trial % 4):
                seq += [rng.choice(['H', 'H0', 'X0', 'T0', 'TDG0', 'S0']),
                        [rng.randrange(8) for s in range(m+1)]]
            bank.append(seq+['H'])
        for ops in bank:
            v, k, populations, ranks = evolve(m, ops)
            full, kd, fullranks = dense_data(m, ops)
            index = {label: j for j, label in enumerate(labels)}
            require(k == kd and all(full[x] == v[index[classify(x, m)]]
                                    for x in range(len(full))), 'mixed local/global evolution')
            counts['state_coordinates'] += len(full)
            counts['circuits'] += 1
            norm = ZERO
            for value, count in zip(v, populations):
                norm = add(norm, tuple(count*t for t in mul(value, conjugate(value))))
            require(norm == (1 << k, 0, 0, 0), 'orbit state norm')
            for predicate in [[int(r != 0) for r in ranks],
                              [label[0] for label in labels]]:
                A, B = acceptance_numerator(v, populations, predicate)
                exact = Q2(F(A, 1 << k), F(B, 1 << k))
                require(exact.sign() >= 0 and (Q2(1)-exact).sign() >= 0, 'probability range')
                counts['acceptance'] += 1
                for bits in [2, 6, 20]:
                    p, q, width = round_probability(A, B, m, k, bits)
                    require((Q2(F(1, 1 << bits))-abs(exact-Q2(p))).sign() > 0,
                            'precision budget')
                    require(width < F(1, 1 << (bits+3)), 'interval width')
                    counts['precision'] += 1
        if m <= 2:
            ops = ['H', 'T0', [0]*m+[3], 'H0', 'S0', 'H']
            pred = [int(s != 0) for s in range(m+1)]
            plan, abstract = compile_circuit(m, ops, pred)
            native = list(native_records(abstract))
            state, h, high = sparse_native(native)
            allowed = ((1 << (m*m))-1) | (1 << plan['output'])
            require(all(x & ~allowed == 0 for x in state), 'native scratch not clean')
            pnum = ZERO
            for x, value in state.items():
                if x >> plan['output'] & 1:
                    pnum = add(pnum, mul(value, conjugate(value)))
            v, k, populations, ranks = evolve(m, ops)
            A, B = acceptance_numerator(v, populations, [pred[s] for s in ranks])
            expected = (A, B, 0, -B)
            require(tuple(t << k for t in pnum) == tuple(t << h for t in expected),
                    'full native output differs from orbit prediction')
            source = json.dumps(dict(qubits=plan['wires'], basis=0, gates=native,
                                     output=plan['output']), separators=(',', ':')).encode()
            native_records_out.append(dict(m=m, wires=plan['wires'],
                gates=len(native), maximum_sparse_support=high,
                canonical_source_sha256=hashlib.sha256(source).hexdigest()))
            counts['native_sources'] += 1
    for m in [4, 8, 12, 16]:
        labels, reps, K, pops = bordered_kernel(m)
        ops = ['H', 'T0', [s % 8 for s in range(m+1)], 'H0', 'X0', 'H']
        v, k, populations, ranks = evolve(m, ops+inverse_ops(ops))
        zero = labels.index((0, 0, '0', '0', -1))
        require(k % 2 == 0 and v[zero] == (1 << (k//2), 0, 0, 0) and
                all(a == ZERO for j, a in enumerate(v) if j != zero),
                'large inverse circuit')
        large.append(dict(m=m, data_qubits=m*m, orbit_coordinates=len(labels),
                          full_source_generated=False,
                          maximum_transition_bits=max(abs(x).bit_length() for row in K for x in row)))
    # At m>=3, a T on the first trailing entry distinguishes same-orbit matrices.
    for m in [3, 4, 8]:
        x, y = 1 << (m+1), 1 << (m+2)
        require(classify(x, m) == classify(y, m) and
                ((x >> (m+1)) & 1) != ((y >> (m+1)) & 1), 'second entry counterexample')
        counts['symmetry_breaks'] += 1
    root = Path(__file__).resolve().parents[1]
    paths = ['src/check_bordered_rank_fourier.py', 'src/bordered_rank_fourier.py',
             'src/rank_orbit_fourier.py', 'src/check_rank_orbit_fourier.py',
             'src/check_acceptance_estimator.py', 'src/check_eth_acceptance_transfer.py',
             'src/eth_acceptance_encoding.py']
    raw = {p: (root/p).read_bytes() for p in paths}
    receipt = dict(status='passed', counts=counts, native_sources=native_records_out,
        large_quotient_controls=large,
        source_sha256={p: hashlib.sha256(v).hexdigest() for p, v in raw.items()},
        source_canonical_lf_sha256={p: hashlib.sha256(v.replace(b'\r\n', b'\n')).hexdigest()
                                  for p, v in raw.items()},
        scope='Finite full-group, signed-Fourier, mixed-circuit and native-source checks; no general multi-entry closure or universal compiler.')
    (root/'artifacts/s173-bordered-rank-fourier-checks.json').write_text(
        json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(status='passed', counts=counts,
                          native_sources=native_records_out, large_controls=len(large))))


if __name__ == '__main__':
    main()
