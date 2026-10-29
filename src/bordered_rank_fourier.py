"""Constructive Fourier aggregation with one distinguished matrix entry."""
from functools import lru_cache
from itertools import product
from fractions import Fraction as F
from math import isqrt
from rank_orbit_fourier import (
    rank_circuit, phase_block, readout_block, rank_matrix)
from check_eth_acceptance_transfer import ZERO, ONE, mul, omega

LOCAL_PHASES = {'T0': 1, 'TDG0': 7, 'S0': 2, 'SDG0': 6, 'Z0': 4}


def binary_rank(rows):
    basis = {}
    for v in rows:
        while v:
            j = v.bit_length()-1
            if j in basis:
                v ^= basis[j]
            else:
                basis[j] = v
                break
    return len(basis)


def solve(rows, rhs):
    basis = {}
    for i, v in enumerate(rows):
        b = (rhs >> i) & 1
        while v:
            j = v.bit_length()-1
            if j in basis:
                w, c = basis[j]
                v, b = v ^ w, b ^ c
            else:
                basis[j] = v, b
                break
        if not v and b:
            return None
    answer = 0
    for j in sorted(basis):
        v, b = basis[j]
        if b ^ ((v & answer).bit_count() & 1):
            answer |= 1 << j
    return answer


def split_matrix(x, m):
    n = m-1
    a = x & 1
    b = (x >> 1) & ((1 << n)-1)
    c = sum(((x >> ((i+1)*m)) & 1) << i for i in range(n))
    D = [(x >> ((i+1)*m+1)) & ((1 << n)-1) for i in range(n)]
    return a, b, c, D


def join_matrix(a, b, c, D, m):
    x = a | (b << 1)
    for i, row in enumerate(D):
        x |= ((c >> i) & 1) << ((i+1)*m)
        x |= row << ((i+1)*m+1)
    return x


def classify(x, m):
    a, b, c, D = split_matrix(x, m)
    r = binary_rank(D)
    bs = '0' if not b else ('I' if binary_rank(D+[b]) == r else 'O')
    solution = solve(D, c)
    cs = '0' if not c else ('I' if solution is not None else 'O')
    t = ((b & solution).bit_count() & 1) if bs == cs == 'I' else -1
    return a, r, bs, cs, t


def orbit_labels(m):
    n, labels = m-1, []
    # Explicit loops keep the two status coordinates independent.
    for a, r in product(range(2), range(n+1)):
        statuses = ['0'] + (['I'] if r else []) + (['O'] if r < n else [])
        for bs, cs in product(statuses, repeat=2):
            ts = ([0, 1] if r >= 2 else [1]) if bs == cs == 'I' else [-1]
            labels.extend((a, r, bs, cs, t) for t in ts)
    return tuple(labels)


def representative(label, m):
    a, r, bs, cs, t = label
    n = m-1
    D = [1 << i if i < r else 0 for i in range(n)]
    b = 0 if bs == '0' else (1 if bs == 'I' else 1 << r)
    c = 0 if cs == '0' else (1 if cs == 'I' else 1 << r)
    if bs == cs == 'I' and t == 0:
        c = 2
    return join_matrix(a, b, c, D, m)


@lru_cache(None)
def rectangular_kernel(a, b):
    limit = min(a, b)
    choose = [[0]*(a+1) for _ in range(a+1)]
    choose[0][0] = 1
    for n in range(1, a+1):
        choose[n][0] = 1
        for u in range(1, n+1):
            choose[n][u] = choose[n-1][u] + (1 << (n-u))*choose[n-1][u-1]
    K = []
    for rho in range(limit+1):
        row = []
        for u in range(limit+1):
            value = (1 << (b*u))*choose[a-rho][u]
            value -= sum(choose[a-s][u-s]*row[s] for s in range(u))
            row.append(value)
        K.append(tuple(row))
    return tuple(K)


def annihilator(v, n):
    if not v:
        return [1 << j for j in range(n)]
    p = (v & -v).bit_length()-1
    return [(1 << j) | (((v >> j) & 1) << p) for j in range(n) if j != p]


def restrict_character(E, left, right):
    rows = []
    for v in left:
        row = 0
        for i, e in enumerate(E):
            if v >> i & 1:
                row ^= e
        rows.append(sum(((row & w).bit_count() & 1) << j
                        for j, w in enumerate(right)))
    return binary_rank(rows)


def Fourier_row(y, m, labels):
    alpha, beta, gamma, E = split_matrix(y, m)
    n = m-1
    identity = [1 << j for j in range(n)]
    S = {}
    for e, f in product(range(2), repeat=2):
        left = annihilator(gamma, n) if f else identity
        right = annihilator(beta, n) if e else identity
        rho = restrict_character(E, left, right)
        values = rectangular_kernel(len(left), len(right))[rho]
        S[e, f] = list(values) + [0]*(n+1-len(values))
    shifted = [row ^ (beta if gamma >> i & 1 else 0) for i, row in enumerate(E)]
    shifted_values = rectangular_kernel(n, n)[binary_rank(shifted)]
    result = []
    for a, r, bs, cs, t in labels:
        if bs == cs == 'I':
            numerator = (1 << (2*r))*S[1, 1][r] + (
                -1 if t else 1)*(1 << r)*shifted_values[r]
            if numerator % 2:
                raise AssertionError('nonintegral inner-pair character sum')
            value = numerator//2
            if t == 0:
                value -= (1 << r)*(S[1, 0][r]+S[0, 1][r])
                value += S[0, 0][r]
        else:
            def coefficients(status, dual):
                return {'0': (1, 0), 'I': (-1, 1 << r),
                        'O': ((1 << n) if dual == 0 else 0, -(1 << r))}[status]
            u, v = coefficients(bs, beta), coefficients(cs, gamma)
            value = sum(u[e]*v[f]*S[e, f][r]
                        for e, f in product(range(2), repeat=2))
        result.append(-value if a & alpha else value)
    return tuple(result)


@lru_cache(None)
def bordered_kernel(m):
    if m < 1:
        raise ValueError('positive dimension required')
    labels = orbit_labels(m)
    reps = tuple(representative(label, m) for label in labels)
    K = tuple(Fourier_row(x, m, labels) for x in reps)
    zero = labels.index((0, 0, '0', '0', -1))
    populations = K[zero]
    if any(v <= 0 for v in populations) or sum(populations) != 1 << (m*m):
        raise AssertionError('invalid orbit populations')
    return labels, reps, K, populations


def evolve(m, operations):
    labels, reps, K, populations = bordered_kernel(m)
    index = {label: j for j, label in enumerate(labels)}
    ranks = [rank_matrix(x, m) for x in reps]
    v = [ZERO]*len(labels)
    v[index[(0, 0, '0', '0', -1)]] = ONE
    denominator = 0
    for op in operations:
        if op == 'H':
            v = [tuple(sum(k*v[j][t] for j, k in enumerate(row)) for t in range(4))
                 for row in K]
            denominator += m*m
        elif op == 'H0':
            old = v
            v = []
            for a, r, bs, cs, t in labels:
                u = old[index[(0, r, bs, cs, t)]]
                w = old[index[(1, r, bs, cs, t)]]
                v.append(tuple(x+(-1 if a else 1)*y for x, y in zip(u, w)))
            denominator += 1
        elif op == 'X0':
            v = [v[index[(1-a, r, bs, cs, t)]] for a, r, bs, cs, t in labels]
        elif isinstance(op, str) and op in LOCAL_PHASES:
            v = [mul(value, omega(LOCAL_PHASES[op]*label[0]))
                 for value, label in zip(v, labels)]
        else:
            if not isinstance(op, (tuple, list)) or len(op) != m+1:
                raise ValueError('invalid operation or rank phase')
            if any(not isinstance(x, int) or not 0 <= x < 8 for x in op):
                raise ValueError('invalid phase residues')
            v = [mul(value, omega(op[r])) for value, r in zip(v, ranks)]
    return v, denominator, populations, ranks


def round_probability(a, b, m, denominator, bits):
    q = denominator+m*m+bits+4
    z = isqrt(2 << (2*q))
    endpoints = [F(a, 1 << denominator)+F(b*t, 1 << (denominator+q))
                 for t in (z, z+1)]
    lo, hi = min(endpoints), max(endpoints)
    midpoint = max(F(0), min(F(1), (lo+hi)/2))
    scale = 1 << (bits+2)
    x = midpoint*scale+F(1, 2)
    return F(x.numerator//x.denominator, scale), q, hi-lo


def compile_circuit(m, operations, predicate):
    plan, gates = rank_circuit(m), []
    for op in operations:
        if op == 'H':
            gates.extend(('H', j) for j in range(m*m))
        elif isinstance(op, str) and op in ['H0', 'X0']+list(LOCAL_PHASES):
            gates.append((op[:-1], 0))
        else:
            gates.extend(phase_block(plan, op))
    gates.extend(readout_block(plan, predicate))
    return plan, gates
