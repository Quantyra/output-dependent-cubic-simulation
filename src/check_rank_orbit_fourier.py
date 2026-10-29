"""Finite checks of the rank-orbit Fourier theorem and source compiler."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import random
from check_acceptance_estimator import Q2, toffoli_decomposition
from check_direct_acceptance_estimator import dense
from check_input_aware_estimator import C2
from check_eth_acceptance_transfer import ZERO, ONE, add, mul, conjugate, omega
from rank_orbit_fourier import (
    rank_matrix, rank_kernel, orbit_evolve, acceptance_numerator,
    rank_circuit, phase_block, readout_block, compile_circuit,
    native_records, basis_phase, round_probability)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def span_rank(x, m):
    space = {0}
    for j in range(m):
        row = (x >> (j*m)) & ((1 << m)-1)
        space |= {v ^ row for v in space}
    return len(space).bit_length()-1


def dense_fourier(v):
    out = list(v)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2*step):
            for j in range(step):
                a, b = out[base+j], out[base+j+step]
                out[base+j] = add(a, b)
                out[base+j+step] = add(a, tuple(-c for c in b))
        step *= 2
    return out


def dense_orbits(m, ops, ranks):
    v, h = [ONE]+[ZERO]*((1 << (m*m))-1), 0
    for op in ops:
        if op == 'H':
            v = dense_fourier(v)
            h += 1
        else:
            v = [mul(a, omega(op[r])) for a, r in zip(v, ranks)]
    return v, h


def main():
    counts = dict(native_toffoli=0, rank_compiler=0, phase_compiler=0,
                  predicate_compiler=0, Fourier_coefficients=0,
                  orbit_identities=0, evolution_states=0, circuits=0,
                  acceptance=0, precision=0, promised_gaps=0,
                  symmetry_break=0)
    compiler_records, large = [], []
    for x in range(8):
        target = x ^ ((((x >> 0) & 1)*((x >> 1) & 1)) << 2)
        require(dense(3, toffoli_decomposition(0, 1, 2), x) ==
                tuple(C2(int(y == target)) for y in range(8)),
                'native Toffoli action or relative phase')
        counts['native_toffoli'] += 1
    rng = random.Random(173004)
    for m in range(1, 4):
        ranks = [span_rank(x, m) for x in range(1 << (m*m))]
        require(all(rank_matrix(x, m) == r for x, r in enumerate(ranks)),
                'independent rank calculation')
        K = rank_kernel(m)
        populations = [ranks.count(s) for s in range(m+1)]
        require(K[0] == populations, 'orbit multiplicities')
        for r in range(m+1):
            y = sum(1 << (j*m+j) for j in range(r))
            actual = [0]*(m+1)
            for x, s in enumerate(ranks):
                actual[s] += -1 if (x & y).bit_count() % 2 else 1
            require(K[r] == actual, 'Fourier character aggregate')
            counts['Fourier_coefficients'] += m+1
        for r, s in product(range(m+1), repeat=2):
            require(sum(K[r][t]*K[t][s] for t in range(m+1)) ==
                    ((1 << (m*m)) if r == s else 0), 'Fourier involution')
            require(sum(populations[t]*K[t][r]*K[t][s] for t in range(m+1)) ==
                    (populations[r]*(1 << (m*m)) if r == s else 0),
                    'weighted Fourier isometry')
            counts['orbit_identities'] += 2
        plan = rank_circuit(m)
        tables = [[0]*(m+1), [(3*s+1) % 8 for s in range(m+1)],
                  [0]*m+[1], [0]*m+[3]]
        pred = [s % 2 for s in range(m+1)]
        read = readout_block(plan, pred)
        blocks = [phase_block(plan, table) for table in tables]
        for x, r in enumerate(ranks):
            result, phase = basis_phase(plan['V'], x)
            expected = x | sum(((r >> j) & 1) << q
                               for j, q in enumerate(plan['rank']))
            require((result, phase) == (expected, 0), 'reversible rank circuit')
            require(basis_phase(list(reversed(plan['V'])), result) == (x, 0),
                    'rank workspace cleanup')
            counts['rank_compiler'] += 1
            for table, block in zip(tables, blocks):
                require(basis_phase(block, x) == (x, table[r]),
                        'rank phase or workspace cleanup')
                counts['phase_compiler'] += 1
            require(basis_phase(read, x) == (x | (pred[r] << plan['output']), 0),
                    'rank predicate output and cleanup')
            counts['predicate_compiler'] += 1
        ops_bank = [[], ['H'], ['H', 'H'],
                    ['H', tables[2], 'H'], ['H', tables[3], 'H']]
        for j in range(9):
            seq = []
            for layer in range(1+j % 5):
                seq += ['H', [rng.randrange(8) for s in range(m+1)]]
            seq += ['H']
            ops_bank.append(seq)
        for ops in ops_bank:
            v, h, pops = orbit_evolve(m, ops)
            full, hd = dense_orbits(m, ops, ranks)
            require(h == hd and all(full[x] == v[r] for x, r in enumerate(ranks)),
                    'rank-coordinate state differs from dense transform')
            total = ZERO
            for a in full:
                total = add(total, mul(a, conjugate(a)))
            require(total == (1 << (h*m*m), 0, 0, 0), 'full state norm')
            counts['evolution_states'] += len(full)
            counts['circuits'] += 1
            for pred in [[int(s != 0) for s in range(m+1)],
                         [int(s == m) for s in range(m+1)]]:
                a, b = acceptance_numerator(v, pops, pred)
                expected = ZERO
                for x, value in enumerate(full):
                    if pred[ranks[x]]:
                        expected = add(expected, mul(value, conjugate(value)))
                require(expected == (a, b, 0, -b), 'rank readout')
                counts['acceptance'] += 1
                exact = Q2(F(a, 1 << (h*m*m)), F(b, 1 << (h*m*m)))
                for bits in [2, 6, 20]:
                    rounded, q, width = round_probability(a, b, m, h, bits)
                    require((Q2(F(1, 1 << bits))-abs(exact-Q2(rounded))).sign() > 0,
                            'certified rounded probability')
                    require(width < F(1, 1 << (bits+3)), 'square-root interval')
                    counts['precision'] += 1
        plan, compiled = compile_circuit(m, ['H', tables[3], 'H'],
                                        [int(s != 0) for s in range(m+1)])
        native = list(native_records(compiled))
        require(all(g[0] in ('X', 'CX', 'T', 'TDG', 'H') for g in native),
                'non-native emitted record')
        compiler_records.append(dict(m=m, wires=plan['wires'],
            abstract_gates=len(compiled), native_gates=len(native),
            phase_tables=len(tables)))
    for m in [1, 2, 3, 4, 8, 16, 32, 64]:
        K = rank_kernel(m)
        require(sum(K[0]) == 1 << (m*m), 'large populations')
        for power in [1, 3]:
            v, h, pops = orbit_evolve(m, ['H', [0]*m+[power], 'H'])
            a, b = acceptance_numerator(v, pops, [0]+[1]*m)
            p = Q2(F(a, 1 << (h*m*m)), F(b, 1 << (h*m*m)))
            alpha = F(pops[m], 1 << (m*m))
            require(F(9, 32) <= alpha <= F(1, 2), 'invertible density bound')
            expected = Q2(2*alpha*(1-alpha),
                          (-1 if power == 1 else 1)*alpha*(1-alpha))
            require(p == expected, 'interfering full-rank phase readout')
            require((Q2(F(1, 3))-p).sign() > 0 if power == 1 else
                    (p-Q2(F(2, 3))).sign() > 0, 'decision gap')
            counts['promised_gaps'] += 1
        large.append(dict(m=m, data_qubits=m*m, coordinates=m+1,
                          max_kernel_bits=max(abs(x).bit_length() for row in K for x in row),
                          sources_generated=m <= 3))
    # T on entry (0,0) sends two equal rank-one amplitudes to distinct phases.
    require(rank_matrix(1, 2) == rank_matrix(2, 2) == 1 and omega(1) != omega(0),
            'local-gate symmetry break')
    counts['symmetry_break'] += 1
    root = Path(__file__).resolve().parents[1]
    paths = ['src/check_rank_orbit_fourier.py', 'src/rank_orbit_fourier.py',
             'src/check_acceptance_estimator.py', 'src/check_eth_acceptance_transfer.py',
             'src/eth_acceptance_encoding.py', 'src/check_direct_acceptance_estimator.py',
             'src/check_input_aware_estimator.py', 'src/direct_acceptance_estimator.py']
    raw = {p: (root/p).read_bytes() for p in paths}
    receipt = dict(status='passed', counts=counts, compiled_sources=compiler_records,
        large_kernel_controls=large,
        source_sha256={p: hashlib.sha256(v).hexdigest() for p, v in raw.items()},
        source_canonical_lf_sha256={p: hashlib.sha256(v.replace(b'\r\n', b'\n')).hexdigest()
                                  for p, v in raw.items()},
        scope='Exact rank-orbit kernel and reversible-source finite checks; no arbitrary-circuit recognizer, universal reduction or unchanged portfolio comparison.')
    (root/'artifacts/s173-rank-orbit-fourier-checks.json').write_text(
        json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(status='passed', counts=counts,
                          compiled_sources=compiler_records, large_controls=len(large))))


if __name__ == '__main__':
    main()
