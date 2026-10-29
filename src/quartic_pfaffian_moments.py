"""Exact finite-field arithmetic for quartic/Pfaffian moment research.

No claim of efficient factor discovery or a general polynomial circuit simulator.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial
from check_acceptance_estimator import Q2
from check_eth_acceptance_transfer import ZERO, ONE, add, omega, conjugate


def scale(a, c):
    return tuple(x*c for x in a)


def mul(a, b):
    out = [Q(0)]*4
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b):
            if y:
                out[(i+j)%4] += x*y*(-1 if i+j >= 4 else 1)
    return tuple(out)


def inverse(a):
    v = mul(a, conjugate(a))
    if v[2] or v[3] != -v[1]:
        raise AssertionError('field norm is not real')
    reciprocal = Q2(1)/Q2(v[0], v[1])
    return mul(conjugate(a), (reciprocal.a, reciprocal.b, Q(0), -reciprocal.b))


def zeros(n):
    return [[ZERO for _ in range(n)] for _ in range(n)]


def pfaffian(matrix):
    n = len(matrix)
    if n%2 or any(len(row) != n for row in matrix):
        raise ValueError('even square matrix required')
    a = [list(row) for row in matrix]
    if any(a[i][i] != ZERO or a[i][j] != scale(a[j][i], -1)
           for i in range(n) for j in range(i, n)):
        raise ValueError('skew matrix required')
    answer = ONE
    for base in range(0, n, 2):
        pivot = next((j for j in range(base+1, n) if a[base][j] != ZERO), None)
        if pivot is None:
            return ZERO
        if pivot != base+1:
            a[pivot], a[base+1] = a[base+1], a[pivot]
            for row in a:
                row[pivot], row[base+1] = row[base+1], row[pivot]
            answer = scale(answer, -1)
        p = a[base][base+1]
        answer = mul(answer, p)
        inv = inverse(p)
        left = {i: mul(a[base][i], inv) for i in range(base+2, n)}
        for i in range(base+2, n):
            for j in range(i+1, n):
                correction = add(mul(left[i], a[base+1][j]),
                                 scale(mul(left[j], a[base+1][i]), -1))
                a[i][j] = add(a[i][j], scale(correction, -1))
                a[j][i] = scale(a[i][j], -1)
    return answer


def rank(matrix):
    a = [list(row) for row in matrix]
    row = 0
    for col in range(len(a[0]) if a else 0):
        pivot = next((j for j in range(row, len(a)) if a[j][col] != ZERO), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        inv = inverse(a[row][col])
        for j in range(row+1, len(a)):
            factor = mul(a[j][col], inv)
            if factor != ZERO:
                a[j] = [add(x, scale(mul(factor, y), -1))
                        for x, y in zip(a[j], a[row])]
        row += 1
        if row == len(a):
            break
    return row


def square_quartic(B):
    out = {}
    for a,b,c,d in combinations(range(len(B)), 4):
        value = scale(add(add(mul(B[a][b], B[c][d]),
                              scale(mul(B[a][c], B[b][d]), -1)),
                          mul(B[a][d], B[b][c])), 2)
        if value != ZERO:
            out[(a,b,c,d)] = value
    return out


def moment_weights(degree, lam):
    moments, power = [ONE], ONE
    for j in range(1, degree+1):
        if j%2:
            moments.append(ZERO)
        else:
            power = mul(power, lam)
            moments.append(scale(power, Q(factorial(j), factorial(j//2))))
    weights = []
    for node in range(degree+1):
        coefficients, denominator = [Q(1)], 1
        for other in range(degree+1):
            if other == node:
                continue
            nxt = [Q(0)]*(len(coefficients)+1)
            for i,c in enumerate(coefficients):
                nxt[i] -= other*c
                nxt[i+1] += c
            coefficients = nxt
            denominator *= node-other
        value = ZERO
        for c, moment in zip(coefficients, moments):
            value = add(value, scale(moment, c/denominator))
        weights.append(value)
    return weights


def moment_contract(W, factors):
    """Each factor is (lambda, B) for q_B=theta^T B theta/2."""
    degrees = [rank(B)//2 for lam,B in factors]
    weights = [moment_weights(d, lam) for d,(lam,B) in zip(degrees, factors)]
    answer, calls = ZERO, 0
    for nodes in product(*(range(d+1) for d in degrees)):
        weight = ONE
        for j,node in enumerate(nodes):
            weight = mul(weight, weights[j][node])
        if weight == ZERO:
            continue
        matrix = [list(row) for row in W]
        for node,(_,B) in zip(nodes, factors):
            if node:
                matrix = [[add(x, scale(y, node)) for x,y in zip(row, grow)]
                          for row,grow in zip(matrix,B)]
        answer = add(answer, mul(weight, pfaffian(matrix)))
        calls += 1
    grid = 1
    for d in degrees:
        grid *= d+1
    return answer, dict(degrees=degrees, grid_points=grid, pfaffian_calls=calls)


def native_wick(n, gates, basis, output):
    """Two-rail S144 map with route/unroute already cancelled on each CZ."""
    from eth_acceptance_encoding import ALIASES, PHASES
    if (type(n) is not int or n < 1 or type(basis) is not int or basis < 0
            or basis.bit_length() > n or type(output) is not int or not 0 <= output < n):
        raise ValueError('invalid source boundary')
    normalized, used = [], {output}
    for gate in gates:
        if not gate or not isinstance(gate[0], str):
            raise ValueError('invalid gate')
        name = ALIASES.get(gate[0], gate[0])
        if name not in {'H', 'X', 'CX', *PHASES}:
            raise ValueError('unsupported gate')
        arity = 2 if name == 'CX' else 1
        if len(gate) != arity+1 or any(type(j) is not int or not 0 <= j < n for j in gate[1:]):
            raise ValueError('invalid gate wires')
        if name == 'CX' and gate[1] == gate[2]:
            raise ValueError('repeated CX wire')
        normalized.append((name, *gate[1:]))
        used.update(gate[1:])
    wires = sorted(used)
    mapping = {wire:j for j,wire in enumerate(wires)}
    basis = sum(((basis >> wire)&1) << j for j,wire in enumerate(wires)
                if wire < basis.bit_length())
    n, output = len(wires), mapping[output]
    gates = [(gate[0], *(mapping[j] for j in gate[1:])) for gate in normalized]
    q = 2*n
    R = [[ONE if i == j else ZERO for j in range(2*q)] for i in range(2*q)]
    residuals = []
    phases = {'T':1, 'TDG':7, 'S':2, 'SDG':6, 'Z':4}
    def gaussian(name, logical):
        a,b,c = 4*logical, 4*logical+1, 4*logical+2
        if name == 'H':
            R[a], R[c] = R[c], R[a]
            R[b] = [scale(x,-1) for x in R[b]]
        elif name == 'X':
            R[b] = [scale(x,-1) for x in R[b]]
            R[c] = [scale(x,-1) for x in R[c]]
        else:
            phase = phases[name]
            cosine = scale(add(omega(phase), omega(-phase)), Q(1,2))
            sine = mul(scale(add(omega(phase), scale(omega(-phase),-1)), Q(1,2)),
                       omega(6))
            x,y = R[a],R[b]
            R[a] = [add(mul(cosine,u), scale(mul(sine,v),-1)) for u,v in zip(x,y)]
            R[b] = [add(mul(sine,u), mul(cosine,v)) for u,v in zip(x,y)]
    def forms(mode):
        x,y = R[2*mode],R[2*mode+1]
        creation = [scale(add(u, mul(omega(6),v)),Q(1,2)) for u,v in zip(x,y)]
        annihilation = [scale(add(u, mul(omega(2),v)),Q(1,2)) for u,v in zip(x,y)]
        return [creation, annihilation]
    for gate in gates:
        if gate[0] == 'CX':
            a,b = gate[1:]
            gaussian('H',b)
            residuals.append(forms(2*a)+forms(2*b))
            gaussian('H',b)
        else:
            gaussian(gate[0],gate[1])
    m = len(residuals)
    vectors = [v for group in residuals for v in group]+forms(2*output)
    vectors += [v for group in reversed(residuals) for v in group]
    blocks = [list(range(4*j,4*j+4)) for j in range(m)]
    blocks += [list(range(4*m+2+4*j,4*m+6+4*j)) for j in range(m)]
    output_pair = [4*m,4*m+1]
    beta = sum(((basis >> j)&1)*3 << (2*j) for j in range(n))
    def contraction(u,v):
        value = ZERO
        for mode in range(q):
            a,b = 2*mode,2*mode+1
            value = add(value, add(mul(u[a],v[a]),mul(u[b],v[b])))
            cross = add(mul(u[a],v[b]),scale(mul(u[b],v[a]),-1))
            value = add(value, mul(scale(omega(2),1-2*((beta>>mode)&1)),cross))
        return value
    W = zeros(len(vectors))
    for i in range(len(W)):
        for j in range(i+1,len(W)):
            W[i][j] = contraction(vectors[i],vectors[j])
            W[j][i] = scale(W[i][j],-1)
    return W, blocks, output_pair


def block_factors(n, blocks):
    factors = []
    for a,b,c,d in blocks:
        B = zeros(n)
        for i,j in ((a,b),(c,d)):
            B[i][j],B[j][i] = ONE,scale(ONE,-1)
        factors.append((scale(ONE,Q(-1,4)),B))
    return factors


def verify_quartic_factors(n, blocks, factors):
    """Check the entire quartic polynomial, not only one scalar output."""
    flattened = [i for block in blocks for i in block]
    if (len(set(flattened)) != len(flattened)
            or any(len(block) != 4 or sorted(block) != list(block)
                   or any(not 0 <= i < n for i in block) for block in blocks)):
        raise ValueError('disjoint ordered blocks required')
    target = {tuple(block):scale(ONE,Q(-1,2)) for block in blocks}
    actual = {}
    for lam,B in factors:
        if (len(B) != n or any(len(row) != n for row in B)
                or any(B[i][i] != ZERO or B[i][j] != scale(B[j][i],-1)
                       for i in range(n) for j in range(i,n))):
            raise ValueError('skew quadratic matrix required')
        for key,value in square_quartic(B).items():
            actual[key] = add(actual.get(key,ZERO),mul(lam,value))
    return {key:value for key,value in actual.items() if value != ZERO} == target


def subset_output(W, blocks, output_pair):
    answer = ZERO
    for bits in range(1 << len(blocks)):
        indices = sorted(output_pair+[i for j,block in enumerate(blocks)
                                      if bits >> j & 1 for i in block])
        minor = [[W[i][j] for j in indices] for i in indices]
        answer = add(answer, scale(pfaffian(minor),(-2)**bits.bit_count()))
    return answer


def binary_auxiliary_output(W, blocks):
    # The local q has rank four and individual Pfaffian degree <=2.
    # Formal moments 1,0,-1/2 are matched at +/-i/sqrt(2).
    n, answer = len(W), ZERO
    amplitude = (Q(0),Q(1,2),Q(0),Q(1,2))  # i/sqrt(2)
    for signs in product((-1,1), repeat=len(blocks)):
        matrix = [list(row) for row in W]
        for sign,(a,b,c,d) in zip(signs,blocks):
            for i,j in ((a,b),(c,d)):
                matrix[i][j] = add(matrix[i][j],scale(amplitude,sign))
                matrix[j][i] = scale(matrix[i][j],-1)
        answer = add(answer,pfaffian(matrix))
    return scale(answer,Q((-2)**len(blocks),1 << len(blocks)))


def round_probability(value, bits):
    if type(bits) is not int or bits < 0:
        raise ValueError('nonnegative precision required')
    if value[2] or value[3] != -value[1]:
        raise ValueError('non-real probability')
    x, lo, hi, size = Q2(value[0],value[1]), 0, (1 << bits)+1, 1 << bits
    if x.sign() < 0 or (Q2(1)-x).sign() < 0:
        raise ValueError('probability outside [0,1]')
    while lo+1 < hi:
        mid = (lo+hi)//2
        if (x*size-Q2(mid)).sign() >= 0:
            lo = mid
        else:
            hi = mid
    return Q(lo,size)
