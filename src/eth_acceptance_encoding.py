"""Parsimonious native-circuit acceptance-to-3CNF transfer (S158).

This constructs counts consumed by the reported ETH-refutation theorem.
It does NOT implement that theorem's subexponential counting algorithm.
The DPLL backend below is an exponential, small-instance reference only.
"""
from dataclasses import dataclass, field
from itertools import product


@dataclass
class CNF:
    variables: int = 0
    clauses: list = field(default_factory=list)
    inputs: list = field(default_factory=list)
    operations: list = field(default_factory=list)
    fixed: dict = field(default_factory=dict)

    def fresh(self, free=False):
        self.variables += 1
        if free:
            self.inputs.append(self.variables)
        return self.variables

    def clause(self, *literals):
        unique = set(literals)
        if any(-x in unique for x in unique):
            return
        self.clauses.append(tuple(sorted(unique, key=lambda x: (abs(x), x))))

    def gate(self, name, *args):
        out = self.fresh()
        for bits in product((0, 1), repeat=len(args)):
            value = truth(name, bits)
            # Forbid precisely this input tuple with the wrong output.
            self.clause(*(v if b == 0 else -v for v, b in zip(args, bits)),
                        out if value else -out)
        self.operations.append((out, name, args))
        return out

    def evaluate(self, bits):
        if len(bits) != len(self.inputs):
            raise ValueError('wrong number of free path bits')
        values = dict(self.fixed)
        values.update(zip(self.inputs, bits))
        for out, name, args in self.operations:
            values[out] = truth(name, tuple(values[x] for x in args))
        return values


def truth(name, bits):
    if name == 'XOR':
        return bits[0] ^ bits[1]
    if name == 'AND':
        return bits[0] & bits[1]
    if name == 'NOT':
        return 1 - bits[0]
    raise ValueError(name)


PHASES = {'T': 1, 'TDG': 7, 'S': 2, 'SDG': 6, 'Z': 4}
ALIASES = {'CNOT': 'CX', 'T_DAG': 'TDG', 'S_DAG': 'SDG'}


def validate(n, gates, basis, output):
    if type(n) is not int or n < 1 or not 0 <= basis < 2 ** n:
        raise ValueError('invalid width or basis input')
    if type(output) is not int or not 0 <= output < n:
        raise ValueError('invalid output wire')
    normalized = []
    for gate in gates:
        name = ALIASES.get(gate[0], gate[0])
        if name not in {'H', 'X', 'CX', *PHASES}:
            raise ValueError('unsupported gate')
        arity = 2 if name == 'CX' else 1
        if len(gate) != arity + 1 or any(type(q) is not int or not 0 <= q < n for q in gate[1:]):
            raise ValueError('invalid gate wires')
        if name == 'CX' and gate[1] == gate[2]:
            raise ValueError('CNOT wires must differ')
        normalized.append((name, *gate[1:]))
    return normalized


def add_phase(cnf, phase, signal, coefficient):
    coefficient %= 8
    carry = 1  # Variable 1 is the fixed zero.
    result = []
    for j in range(3):
        addend = signal if coefficient >> j & 1 else 1
        pair = cnf.gate('XOR', phase[j], addend)
        result.append(cnf.gate('XOR', pair, carry))
        if j != 2:
            carry = cnf.gate('XOR', cnf.gate('AND', phase[j], addend),
                             cnf.gate('AND', pair, carry))
    return result


def encode_acceptance(n, gates, basis=0, output=0):
    """Return base 3CNF, phase output bits, and Hadamard count.

    The eight extensions obtained by pinning phase=j count ordered ket/bra
    histories with matching complete final basis states and output one.
    Every path-bit assignment has exactly one assignment to gate variables.
    """
    gates = validate(n, gates, basis, output)
    cnf = CNF()
    zero, one = cnf.fresh(), cnf.fresh()
    cnf.clause(-zero)
    cnf.clause(one)
    cnf.fixed.update({zero: 0, one: 1})
    initial = []
    for j in range(n):
        v = cnf.fresh()
        bit = basis >> j & 1
        cnf.clause(v if bit else -v)
        cnf.fixed[v] = bit
        initial.append(v)
    phase = [zero] * 3
    ends = []
    for sign in (1, -1):
        wires = list(initial)
        for gate in gates:
            name, q = gate[:2]
            if name == 'H':
                branch = cnf.fresh(free=True)
                phase = add_phase(cnf, phase, cnf.gate('AND', wires[q], branch), 4)
                wires[q] = branch
            elif name == 'X':
                wires[q] = cnf.gate('NOT', wires[q])
            elif name == 'CX':
                target = gate[2]
                wires[target] = cnf.gate('XOR', wires[q], wires[target])
            else:
                phase = add_phase(cnf, phase, wires[q], sign * PHASES[name])
        ends.append(wires)
    for ket, bra in zip(*ends):
        cnf.clause(-ket, bra)
        cnf.clause(ket, -bra)
    cnf.clause(ends[0][output])
    return cnf, phase, sum(g[0] == 'H' for g in gates)


def residue_clauses(phase, residue):
    return tuple((v if residue >> j & 1 else -v,) for j, v in enumerate(phase))


def reference_count(variables, clauses):
    """Exact exponential DPLL reference; never a claimed fast solver."""
    def recurse(current, remaining):
        while True:
            if any(len(c) == 0 for c in current):
                return 0
            if not current:
                return 2 ** len(remaining)
            unit = next((c[0] for c in current if len(c) == 1), None)
            if unit is None:
                break
            remaining = remaining - {abs(unit)}
            current = tuple(tuple(v for v in c if v != -unit)
                            for c in current if unit not in c)
        variable = min(remaining)  # Free inputs/gates retain their actual count.
        return sum(recurse(current + ((signed,),), remaining)
                   for signed in (variable, -variable))
    return recurse(tuple(clauses), frozenset(range(1, variables + 1)))


def reference_buckets(cnf, phase, max_path_bits=10):
    if len(cnf.inputs) > max_path_bits:
        raise ValueError('reference enumeration cap exceeded')
    return [reference_count(cnf.variables, tuple(cnf.clauses) + residue_clauses(phase, j))
            for j in range(8)]


def cyclotomic_sum(counts):
    """Integer coefficients of 1,w,w^2,w^3 with w^4=-1."""
    return tuple(counts[j] - counts[j + 4] for j in range(4))


def acceptance_interval(counts, hadamards, precision=16):
    """Outward dyadic interval, using exact integer arithmetic throughout.

    Probabilities equal (A + D*sqrt(2))/2^h. The conjugacy check is
    mandatory. Absolute error <= 1/12 follows for precision >= h+4.
    """
    from fractions import Fraction
    from math import isqrt
    if len(counts) != 8 or any(type(c) is not int or c < 0 for c in counts):
        raise ValueError('invalid bucket counts')
    if any(counts[j] != counts[-j % 8] for j in range(8)):
        raise ValueError('non-real path-pair sum')
    if precision < 0 or hadamards < 0:
        raise ValueError('invalid precision or normalization')
    scale = 2 ** precision
    low = Fraction(isqrt(2 * scale * scale), scale)
    high = low + Fraction(1, scale)
    a, d = counts[0] - counts[4], counts[1] - counts[3]
    values = ((a + d * low) / 2 ** hadamards, (a + d * high) / 2 ** hadamards)
    return min(values), max(values)
