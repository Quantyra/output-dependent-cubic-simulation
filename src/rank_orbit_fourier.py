"""Exact binary-matrix rank-orbit kernel and reference reversible compiler.

This is a restricted mathematical implementation, not an arbitrary-circuit
recognizer or simulator. The compiler emits abstract X/CX/CCX/T/H records;
native_records expands each CCX into the retained exact 15-gate macro.
"""
from check_acceptance_estimator import toffoli_decomposition
from fractions import Fraction
from math import isqrt
from check_eth_acceptance_transfer import add, mul, conjugate, omega, ZERO, ONE


def rank_matrix(x, m):
    rows = [(x >> (j*m)) & ((1 << m)-1) for j in range(m)]
    pivots = {}
    for row in rows:
        while row:
            j = row.bit_length()-1
            if j in pivots:
                row ^= pivots[j]
            else:
                pivots[j] = row
                break
    return len(pivots)


def rank_kernel(m):
    if m < 1:
        raise ValueError('positive matrix dimension required')
    choose = [[0]*(m+1) for _ in range(m+1)]
    choose[0][0] = 1
    for n in range(1, m+1):
        choose[n][0] = 1
        for k in range(1, n+1):
            choose[n][k] = (choose[n-1][k] +
                            (1 << (n-k))*choose[n-1][k-1])
    K = []
    for r in range(m+1):
        row = []
        for u in range(m+1):
            value = (1 << (m*u))*choose[m-r][u]
            value -= sum(choose[m-s][u-s]*row[s] for s in range(u))
            row.append(value)
        K.append(row)
    return K


def scaled(value, integer):
    return tuple(integer*x for x in value)


def orbit_evolve(m, operations):
    K = rank_kernel(m)
    v = [ONE] + [ZERO]*m
    h = 0
    for op in operations:
        if op == 'H':
            v = [tuple(sum(K[r][s]*v[s][j] for s in range(m+1))
                       for j in range(4)) for r in range(m+1)]
            h += 1
        else:
            if len(op) != m+1 or any(not 0 <= k < 8 for k in op):
                raise ValueError('phase table must have m+1 residues modulo 8')
            v = [mul(a, omega(k)) for a, k in zip(v, op)]
    return v, h, K[0]


def acceptance_numerator(v, populations, predicate):
    out = ZERO
    for a, count, bit in zip(v, populations, predicate):
        if bit:
            out = add(out, scaled(mul(a, conjugate(a)), count))
    if out[2] != 0 or out[3] != -out[1]:
        raise AssertionError('probability is not real in Q(sqrt(2))')
    return out[0], out[1]


def round_probability(a, b, m, h, bits):
    if bits < 1:
        raise ValueError('positive accuracy bits required')
    q = (h+1)*m*m + bits + 4
    z = isqrt(2 << (2*q))
    endpoints = [Fraction(a, 1 << (h*m*m)) +
                 Fraction(b*t, 1 << (h*m*m+q)) for t in (z, z+1)]
    lo, hi = min(endpoints), max(endpoints)
    midpoint = max(Fraction(0), min(Fraction(1), (lo+hi)/2))
    scale = 1 << (bits+2)
    scaled_mid = midpoint*scale + Fraction(1, 2)
    rounded = Fraction(scaled_mid.numerator//scaled_mid.denominator, scale)
    return rounded, q, hi-lo


def rank_circuit(m):
    # Functional Boolean elimination: all node updates reference old values.
    # Nodes are computed into fresh zero bits and then uncomputed.
    d = m*m
    zero, one = d, d+1
    next_wire = d+2
    forward = [('X', one)]
    def node(kind, a, b=None):
        nonlocal next_wire
        target = next_wire
        next_wire += 1
        if kind == 'AND':
            if a == b:
                forward.append(('CX', a, target))
            else:
                forward.append(('CCX', a, b, target))
        elif kind == 'XOR':
            if a != b:
                forward.extend([('CX', a, target), ('CX', b, target)])
        elif kind == 'NOT':
            forward.extend([('X', target), ('CX', a, target)])
        return target
    occupied = [zero]*m
    basis = [[zero]*m for _ in range(m)]
    for i in range(m):
        v = [i*m+j for j in range(m)]
        for j in reversed(range(m)):
            oldrow, oldp, oldv = basis[j], occupied[j], v
            eliminate = node('AND', oldv[j], oldp)
            insert = node('AND', oldv[j], node('NOT', oldp))
            keep = node('NOT', insert)
            basis[j] = [node('XOR', oldrow[k], node('AND', insert, oldv[k]))
                        for k in range(m)]
            occupied[j] = node('XOR', oldp, insert)
            v = [node('AND', node('XOR', oldv[k],
                                 node('AND', eliminate, oldrow[k])), keep)
                 for k in range(m)]
    width = m.bit_length()
    bits = [zero]*width
    for bit in occupied:
        carry, updated = bit, []
        for old in bits:
            updated.append(node('XOR', old, carry))
            carry = node('AND', old, carry)
        bits = updated
    rank_wires = list(range(next_wire, next_wire+width))
    next_wire += width
    copies = [('CX', a, b) for a, b in zip(bits, rank_wires)]
    V = forward + copies + list(reversed(forward))
    flag = next_wire
    scratch = list(range(flag+1, flag+1+max(0, width-2)))
    output = flag+1+len(scratch)
    return dict(m=m, data=d, rank=rank_wires, flag=flag, scratch=scratch,
                output=output, wires=output+1, V=V,
                forward_records=len(forward))


def equality_compute(plan, value):
    controls = plan['rank']
    gates = [('X', q) for j, q in enumerate(controls) if not (value >> j & 1)]
    if len(controls) == 1:
        gates.append(('CX', controls[0], plan['flag']))
    elif len(controls) == 2:
        gates.append(('CCX', controls[0], controls[1], plan['flag']))
    else:
        work = plan['scratch']
        gates.append(('CCX', controls[0], controls[1], work[0]))
        for j in range(2, len(controls)-1):
            gates.append(('CCX', work[j-2], controls[j], work[j-1]))
        gates.append(('CCX', work[-1], controls[-1], plan['flag']))
    return gates


def phase_block(plan, table):
    if len(table) != plan['m']+1 or any(not 0 <= x < 8 for x in table):
        raise ValueError('invalid phase table')
    gates = list(plan['V'])
    for s, f in enumerate(table):
        E = equality_compute(plan, s)
        gates.extend(E + [('T', plan['flag'])]*f + list(reversed(E)))
    gates.extend(reversed(plan['V']))
    return gates


def readout_block(plan, predicate):
    if len(predicate) != plan['m']+1 or any(x not in (0, 1) for x in predicate):
        raise ValueError('invalid rank predicate')
    gates = list(plan['V'])
    for s, bit in enumerate(predicate):
        E = equality_compute(plan, s)
        gates.extend(E + ([('CX', plan['flag'], plan['output'])] if bit else [])
                     + list(reversed(E)))
    gates.extend(reversed(plan['V']))
    return gates


def compile_circuit(m, operations, predicate):
    plan = rank_circuit(m)
    gates = []
    for op in operations:
        gates.extend([('H', j) for j in range(m*m)] if op == 'H'
                     else phase_block(plan, op))
    gates.extend(readout_block(plan, predicate))
    return plan, gates


def native_records(gates):
    for gate in gates:
        if gate[0] == 'CCX':
            yield from toffoli_decomposition(*gate[1:])
        else:
            yield gate


def basis_phase(gates, basis):
    state, phase = basis, 0
    for gate in gates:
        kind, *wires = gate
        if kind in ('X', 'CX', 'CCX'):
            if all(state >> q & 1 for q in wires[:-1]):
                state ^= 1 << wires[-1]
        elif kind == 'T':
            phase += (state >> wires[0]) & 1
        else:
            raise ValueError('basis-phase verifier received a Hadamard')
    return state, phase % 8
