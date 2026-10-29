"""S159: source-derived Clifford elimination and local residual counts.

All construction is polynomial. Small-instance reference counting remains
exponential. The ETH backend is an external theorem premise, not implemented.
Paulis use i**phase X**x Z**z, including every global sign.
"""
from fractions import Fraction
from math import isqrt

from eth_acceptance_encoding import CNF, add_phase, reference_count, validate


def multiply(a, b):
    r, x, z = a
    s, y, w = b
    return ((r + s + 2 * (z & y).bit_count()) % 4, x ^ y, z ^ w)


def selected_product(generators, selection):
    result = (0, 0, 0)
    for j, generator in enumerate(generators):
        if selection >> j & 1:
            result = multiply(result, generator)
    return result


def pullback(pauli, gates):
    r, x, z = pauli
    for gate in reversed(gates):
        name, q = gate[:2]
        a, b = x >> q & 1, z >> q & 1
        if name == 'H':
            r += 2 * a * b
            x ^= (a ^ b) << q
            z ^= (a ^ b) << q
        elif name in {'S', 'SDG'}:
            r += (-1 if name == 'S' else 1) * a
            z ^= a << q
        elif name == 'X':
            r += 2 * b
        elif name == 'Z':
            r += 2 * a
        elif name == 'CX':
            target = gate[2]
            x ^= a << target
            z ^= (z >> target & 1) << q
        else:
            raise ValueError('pullback requires Clifford gates')
    return r % 4, x, z


def affine_fiber(columns, target):
    """Return one preimage and an independent kernel basis over F_2."""
    pivots, kernel = {}, []
    for j, column in enumerate(columns):
        combination = 1 << j
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (column, combination)
                break
            known, coefficients = pivots[pivot]
            column ^= known
            combination ^= coefficients
        if column == 0:
            kernel.append(combination)
    particular = 0
    while target:
        pivot = target.bit_length() - 1
        if pivot not in pivots:
            return None, kernel
        column, coefficients = pivots[pivot]
        target ^= column
        particular ^= coefficients
    return particular, kernel


def extract_bits(mask, positions):
    return sum(((mask >> position) & 1) << j for j, position in enumerate(positions))


def split_components(offset, generators, t):
    parent = list(range(t))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    scalar = 1
    for r, x, z in generators:
        support = [j for j in range(t) if (x | z) >> j & 1]
        if not support:
            if r not in (0, 2):
                raise ValueError('non-Hermitian identity generator')
            scalar *= 2 if r == 0 else 0
        else:
            for j in support[1:]:
                parent[root(j)] = root(support[0])
    r, x, z = offset
    sign = (r - (x & z).bit_count()) % 4
    if sign not in (0, 2):
        raise ValueError('non-Hermitian offset')
    scalar *= 1 if sign == 0 else -1
    groups = {}
    active = x | z
    for _, gx, gz in generators:
        active |= gx | gz
    for j in range(t):
        if active >> j & 1:
            groups.setdefault(root(j), []).append(j)
    components = []
    for positions in groups.values():
        local_x, local_z = extract_bits(x, positions), extract_bits(z, positions)
        local_generators = []
        for phase, gx, gz in generators:
            xx, zz = extract_bits(gx, positions), extract_bits(gz, positions)
            if xx | zz:
                local_generators.append((phase, xx, zz))
        components.append({'positions': positions, 'qubits': len(positions),
                           'offset': ((local_x & local_z).bit_count() % 4, local_x, local_z),
                           'generators': local_generators})
    return scalar, components


def reduce_source(q, gates, basis=0, output=0):
    """Dense explicit-input adapter. No count or probability oracle is used."""
    gates = validate(q, gates, basis, output)
    clifford, t = [], 0
    for gate in gates:
        if gate[0] in {'T', 'TDG'}:
            if gate[0] == 'TDG':
                clifford.append(('SDG', gate[1]))
            clifford.append(('CX', gate[1], q + t))
            t += 1
        else:
            clifford.append(gate)
    generators = [pullback((0, 0, 1 << (q + j)), clifford) for j in range(t)]
    observable = pullback((0, 0, 1 << output), clifford)
    data_mask = (1 << q) - 1
    particular, kernel = affine_fiber([g[1] & data_mask for g in generators], observable[1] & data_mask)
    record = {'qubits': q, 'gates': len(gates), 'hadamards': sum(g[0] == 'H' for g in gates),
              'magic_qubits': t, 'kernel_dimension': len(kernel),
              'source_consistent': particular is not None}
    if particular is None:
        return record | {'scalar': 0, 'components': []}
    def condense(pauli):
        r, x, z = pauli
        if x & data_mask:
            raise ValueError('uneliminated data X support')
        return ((r + 2 * ((z & data_mask) & basis).bit_count()) % 4, x >> q, z >> q)
    offset = condense(multiply(observable, selected_product(generators, particular)))
    residual = [condense(selected_product(generators, vector)) for vector in kernel]
    scalar, components = split_components(offset, residual, t)
    return record | {'particular': particular, 'kernel_basis': kernel,
                     'scalar': scalar, 'components': components}


def component_buckets_reference(component, max_generators=16):
    """Exponential reference. Returns ordinary weighted model counts."""
    generators = component['generators']
    if len(generators) > max_generators:
        raise ValueError('reference generator cap exceeded')
    d = component['qubits']
    counts = [[0, 0], [0, 0]]  # sign, parity of nonidentity weight
    for selection in range(1 << len(generators)):
        r, x, z = multiply(component['offset'], selected_product(generators, selection))
        if z & ~x:  # Magic-state expectation of Z is zero.
            continue
        phase = (r - (x & z).bit_count()) % 4
        if phase not in (0, 2):
            raise ValueError('non-real component summand')
        w = x.bit_count()
        counts[phase // 2][w % 2] += 1 << (d - (w + 1) // 2)
    return counts


def compile_component(component):
    """Four ordinary 3CNF counts with unique deterministic extension.

    Witness bits supply a deliberate multiplicity 2**(d-ceil(weight/2)).
    This is distinct from accidental multiplicity in gate auxiliaries.
    """
    d, generators = component['qubits'], component['generators']
    cnf = CNF()
    zero, one = cnf.fresh(), cnf.fresh()
    cnf.clause(-zero)
    cnf.clause(one)
    cnf.fixed = {zero: 0, one: 1}
    selectors = [cnf.fresh(free=True) for _ in generators]
    r0, x0, z0 = component['offset']
    initial = 2 * r0 % 8
    phase = [one if initial >> j & 1 else zero for j in range(3)]
    for i, (r, x, _) in enumerate(generators):
        coefficient = (2 * r + 4 * ((z0 & x).bit_count() % 2)) % 8
        if coefficient:
            phase = add_phase(cnf, phase, selectors[i], coefficient)
        for j in range(i):
            if (generators[j][2] & x).bit_count() % 2:
                term = cnf.gate('AND', selectors[j], selectors[i])
                phase = add_phase(cnf, phase, term, 4)
    parity = zero
    for j in range(d):
        xbit, zbit = (one if x0 >> j & 1 else zero), (one if z0 >> j & 1 else zero)
        for selector, (_, x, z) in zip(selectors, generators):
            if x >> j & 1:
                xbit = cnf.gate('XOR', xbit, selector)
            if z >> j & 1:
                zbit = cnf.gate('XOR', zbit, selector)
        cnf.clause(xbit, -zbit)
        phase = add_phase(cnf, phase, cnf.gate('AND', xbit, zbit), -2)
        odd_hit = cnf.gate('AND', xbit, cnf.gate('NOT', parity))
        witness = cnf.fresh(free=True)
        cnf.clause(-odd_hit, -witness)
        parity = cnf.gate('XOR', parity, xbit)
    cnf.clause(-phase[0])
    cnf.clause(-phase[1])
    return cnf, phase[2], parity


def cnf_buckets_reference(cnf, sign, parity, max_inputs=18):
    if len(cnf.inputs) > max_inputs:
        raise ValueError('reference CNF cap exceeded')
    return [[reference_count(cnf.variables, tuple(cnf.clauses) +
                             ((sign if s else -sign,), (parity if w else -parity,)))
             for w in range(2)] for s in range(2)]


def ring_product(a, b):
    return a[0] * b[0] + 2 * a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def quadratic_sum(constant, linear, pairs, n):
    """Exact Boolean quadratic Gauss sum, in polynomial operations."""
    active = set(range(n))
    pairs = set(pairs)
    linear = set(linear)
    scale = 1
    while pairs:
        i, j = min(pairs)
        a = {v if u == i else u for u, v in pairs if i in (u, v) and j not in (u, v)}
        b = {v if u == j else u for u, v in pairs if j in (u, v) and i not in (u, v)}
        ca, cb = int(i in linear), int(j in linear)
        pairs = {edge for edge in pairs if i not in edge and j not in edge}
        linear -= {i, j}
        constant ^= ca & cb
        if ca:
            linear ^= b
        if cb:
            linear ^= a
        for u in a:
            for v in b:
                if u == v:
                    linear ^= {u}
                else:
                    pairs ^= {tuple(sorted((u, v)))}
        active -= {i, j}
        scale *= 2
    return 0 if linear else (-1 if constant else 1) * scale * 2 ** len(active)


def fixed_x_gauss(component):
    """Polynomial shortcut when every surviving generator has X-mask zero.

    Returns an exact numerator pair at denominator 2**component.qubits,
    or None if this sufficient condition is absent.
    """
    generators = component['generators']
    if any(g[1] for g in generators):
        return None
    offset = component['offset']
    outside = ((1 << component['qubits']) - 1) ^ offset[1]
    particular, kernel = affine_fiber([g[2] & outside for g in generators], offset[2] & outside)
    if particular is None:
        return 0, 0
    base = multiply(offset, selected_product(generators, particular))
    rows = [selected_product(generators, v) for v in kernel]
    def sign(selection):
        r, x, z = multiply(base, selected_product(rows, selection))
        e = (r - (x & z).bit_count()) % 4
        if e not in (0, 2) or z & ~x:
            raise ValueError('invalid fixed-X affine restriction')
        return e // 2
    k = len(rows)
    c = sign(0)
    linear = {i for i in range(k) if sign(1 << i) ^ c}
    pairs = {(i, j) for i in range(k) for j in range(i + 1, k)
             if sign((1 << i) | (1 << j)) ^ c ^ int(i in linear) ^ int(j in linear)}
    signed_count = quadratic_sum(c, linear, pairs, k)
    weight = base[1].bit_count()
    value = signed_count * (1 << (component['qubits'] - (weight + 1) // 2))
    return (0, value) if weight % 2 else (value, 0)


def combine_counts(reduction, bucket_lists):
    """Return exact output-one probability (a+b*sqrt(2))/2**e."""
    if len(bucket_lists) != len(reduction['components']):
        raise ValueError('missing component counts')
    values = []
    for component, counts in zip(reduction['components'], bucket_lists):
        bound = 1 << (component['qubits'] + len(component['generators']))
        if any(type(c) is not int or c < 0 for row in counts for c in row) or sum(map(sum, counts)) > bound:
            raise ValueError('invalid component counts')
        values.append((counts[0][0] - counts[1][0], counts[0][1] - counts[1][1]))
    return combine_values(reduction, values)


def combine_values(reduction, component_values):
    if len(component_values) != len(reduction['components']):
        raise ValueError('missing component values')
    value, exponent = (reduction['scalar'], 0), 0
    for component, numerator in zip(reduction['components'], component_values):
        value = ring_product(value, numerator)
        exponent += component['qubits']
    a, b, e = (1 << exponent) - value[0], -value[1], exponent + 1
    while e and a % 2 == 0 and b % 2 == 0:
        a, b, e = a // 2, b // 2, e - 1
    return a, b, e


def probability_interval(value, epsilon=Fraction(1, 12)):
    """Outward global interval after exact component recombination."""
    a, b, e = value
    if not 0 < epsilon < 1:
        raise ValueError('invalid epsilon')
    error_bits = max(0, epsilon.denominator.bit_length() - epsilon.numerator.bit_length())
    if (epsilon.numerator << error_bits) < epsilon.denominator:
        error_bits += 1
    precision = max(0, abs(b).bit_length() - e) + error_bits + 2
    scale = 1 << precision
    lo = Fraction(isqrt(2 * scale * scale), scale)
    hi = lo + Fraction(1, scale)
    ends = ((a + b * lo) / (1 << e), (a + b * hi) / (1 << e))
    return min(ends), max(ends), precision
