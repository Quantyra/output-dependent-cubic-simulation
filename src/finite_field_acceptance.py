"""S173/R05-01: native finite-field source and exact point-count reduction.

The Lauder-Wan polynomial-time backend is an external theorem, not implemented
here. Enumeration functions are explicitly small-instance verification oracles.
"""
import json
from fractions import Fraction
from itertools import product
from math import comb

from check_acceptance_estimator import toffoli_decomposition


def polynomial_remainder(a,b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a


def polynomial_gcd(a,b):
    while b:
        a,b = b,polynomial_remainder(a,b)
    return a


def raw_mul(a,b,modulus):
    r=modulus.bit_length()-1
    value=0
    while b:
        if b&1:
            value ^= a
        b >>= 1
        a <<= 1
        if a >> r:
            a ^= modulus
    return value


def irreducible(modulus):
    if type(modulus) is not int or modulus < 3:
        return False
    r=modulus.bit_length()-1
    x=polynomial_remainder(2,modulus)
    value=x
    for k in range(1,r+1):
        value=raw_mul(value,value,modulus)
        if k <= r//2 and polynomial_gcd(value^x,modulus) != 1:
            return False
    return value == x


def find_field(r,h,rng):
    """Bounded randomized construction; failure probability at most 2**(-h)."""
    if type(r) is not int or r<1 or type(h) is not int or h<1:
        raise ValueError('positive degree and confidence parameter required')
    if r==1:
        return Field(3),1
    for attempt in range(1,r*h+1):
        candidate=(1 << r) | (rng.getrandbits(r-1) << 1) | 1
        if irreducible(candidate):
            return Field(candidate),attempt
    return None,r*h


class Field:
    def __init__(self,modulus):
        if not irreducible(modulus):
            raise ValueError('irreducible binary field polynomial required')
        self.modulus=modulus
        self.r=modulus.bit_length()-1
        self.q=1 << self.r

    def mul(self,a,b):
        return raw_mul(a,b,self.modulus)

    def power(self,a,e):
        out=1
        while e:
            if e&1:
                out=self.mul(out,a)
            a=self.mul(a,a)
            e >>= 1
        return out

    def trace(self,a):
        out=0
        for _ in range(self.r):
            out ^= a
            a=self.mul(a,a)
        if out not in (0,1):
            raise AssertionError('trace outside prime field')
        return out

    def evaluate(self,terms,x):
        value=0
        for e,a in terms:
            value ^= self.mul(a,self.power(x,e))
        return value

    def dual(self,j):
        # Solve M a = e_j; rows M_i encode Tr(b_i*b_k).
        rows=[sum(self.trace(self.mul(1 << i,1 << k)) << k for k in range(self.r))
              | ((i == j) << self.r) for i in range(self.r)]
        for col in range(self.r):
            pivot=next(i for i in range(col,self.r) if rows[i] >> col & 1)
            rows[col],rows[pivot]=rows[pivot],rows[col]
            for i in range(self.r):
                if i != col and rows[i] >> col & 1:
                    rows[i] ^= rows[col]
        return sum((row >> self.r) << i for i,row in enumerate(rows))


def normalize_descriptor(desc):
    if not isinstance(desc,list) or len(desc)!=5:
        raise ValueError('descriptor [r,modulus,phases,input,output] required')
    r,modulus,phases,basis,output=desc
    if (type(r) is not int or r<1 or type(modulus) is not int
            or modulus.bit_length()!=r+1 or type(basis) is not int
            or basis<0 or basis.bit_length()>r or type(output) is not int
            or not 0 <= output < r or not isinstance(phases,list) or not phases):
        raise ValueError('invalid descriptor boundary')
    field=Field(modulus)
    normalized=[]
    for terms in phases:
        merged={}
        if not isinstance(terms,list):
            raise ValueError('phase term list required')
        for term in terms:
            if (not isinstance(term,(list,tuple)) or len(term)!=2
                    or type(term[0]) is not int or term[0]<0
                    or type(term[1]) is not int or not 0<=term[1]<field.q):
                raise ValueError('invalid sparse polynomial term')
            e,a=term
            merged[e]=merged.get(e,0)^a
        normalized.append([[e,a] for e,a in sorted(merged.items()) if a])
    return [r,modulus,normalized,basis,output],field


def linear_map_gates(rows):
    n=len(rows)
    work=list(rows)
    ops=[]
    for col in range(n):
        pivot=next((i for i in range(col,n) if work[i] >> col & 1),None)
        if pivot is None:
            raise ValueError('invertible binary matrix required')
        if pivot != col:
            work[pivot],work[col]=work[col],work[pivot]
            ops += [('CX',col,pivot),('CX',pivot,col),('CX',col,pivot)]
        for i in range(n):
            if i != col and work[i] >> col & 1:
                work[i] ^= work[col]
                ops.append(('CX',col,i))
    assert work == [1 << i for i in range(n)]
    return list(reversed(ops))


def fourier_gates(field):
    rows=[sum(field.trace(field.mul(1 << i,1 << j)) << j for j in range(field.r))
          for i in range(field.r)]
    return linear_map_gates(rows)+[('H',q) for q in range(field.r)]


def phase_gates(field,terms,start):
    """Out-of-place field arithmetic, phase, exact uncomputation."""
    r=field.r
    next_wire=start
    work=[]
    def allocate():
        nonlocal next_wire
        register=list(range(next_wire,next_wire+r))
        next_wire += r
        return register
    def linear_add(src,dest,multiplier=1,square=False):
        for i,q in enumerate(src):
            value=field.power(1 << i,2) if square else 1 << i
            value=field.mul(multiplier,value)
            for k in range(r):
                if value >> k & 1:
                    work.append(('CX',q,dest[k]))
    def multiply(a,b):
        out=allocate()
        for i,q in enumerate(a):
            for j,t in enumerate(b):
                value=field.mul(1 << i,1 << j)
                for k in range(r):
                    if value >> k & 1:
                        work.append(('CCX',q,t,out[k]))
        return out
    maxbit=max((e.bit_length() for e,a in terms),default=0)
    powers=[list(range(r))]
    for _ in range(1,maxbit):
        new=allocate()
        linear_add(powers[-1],new,square=True)
        powers.append(new)
    accumulator=allocate()
    for e,a in terms:
        if e==0:
            work += [('X',accumulator[k]) for k in range(r) if a >> k & 1]
            continue
        selected=[powers[i] for i in range(e.bit_length()) if e >> i & 1]
        register=selected[0]
        for factor in selected[1:]:
            register=multiply(register,factor)
        linear_add(register,accumulator,multiplier=a)
    middle=[('Z',accumulator[k]) for k in range(r) if field.trace(1 << k)]
    return work+middle+list(reversed(work)),next_wire


def header(desc):
    raw=json.dumps(desc,separators=(',',':')).encode('ascii')
    gates=[]
    for byte in raw:
        for shift in range(7,-1,-1):
            tag='Z' if byte >> shift & 1 else 'X'
            gates += [(tag,0),(tag,0)]
    return gates+[('H',0),('H',0)]


def compile_native(desc):
    desc,field=normalize_descriptor(desc)
    r,modulus,phases,basis,output=desc
    gates=header(desc)
    gates += fourier_gates(field)
    width=r
    for terms in phases:
        abstract,width=phase_gates(field,terms,width)
        for gate in abstract:
            gates.extend(toffoli_decomposition(*gate[1:]) if gate[0]=='CCX' else [gate])
        gates += fourier_gates(field)
    return dict(qubits=width,gates=gates,basis=basis,output=output,descriptor=desc,
                source_bits=8*len(json.dumps([width,gates,basis,output],separators=(',',':'))))


def recognize_native(n,gates,basis,output):
    bits=[]
    i=0
    while i+1<len(gates):
        a,b=tuple(gates[i]),tuple(gates[i+1])
        if a==b==('H',0):
            i+=2
            break
        if a!=b or a not in (('X',0),('Z',0)):
            raise ValueError('canonical identity header missing')
        bits.append(int(a[0]=='Z'))
        i+=2
    else:
        raise ValueError('unterminated header')
    if len(bits)%8:
        raise ValueError('incomplete header byte')
    raw=bytes(sum(bits[j+k] << (7-k) for k in range(8)) for j in range(0,len(bits),8))
    try:
        desc=json.loads(raw.decode('ascii'))
    except (ValueError,UnicodeError) as error:
        raise ValueError('invalid descriptor serialization') from error
    # Before recompilation, constrain malicious parameter/expansion requests.
    if not isinstance(desc,list) or len(desc)!=5 or type(desc[0]) is not int:
        raise ValueError('invalid descriptor')
    if desc[0]>len(gates)+1:
        raise ValueError('declared field too large for this source')
    canonical=compile_native(desc)
    if (canonical['qubits']!=n or canonical['basis']!=basis
            or canonical['output']!=output or canonical['gates']!=[tuple(g) for g in gates]):
        raise ValueError('native source differs from canonical expansion')
    return canonical['descriptor']


def add_term(poly,exponents,coefficient):
    if coefficient:
        poly[exponents]=poly.get(exponents,0)^coefficient
        if not poly[exponents]:
            del poly[exponents]


def mv_add(a,b):
    result=dict(a)
    for e,c in b.items():
        add_term(result,e,c)
    return result


def mv_mul(field,a,b):
    result={}
    for e,c in a.items():
        for f,d in b.items():
            add_term(result,tuple(x+y for x,y in zip(e,f)),field.mul(c,d))
    return result


def affine_power(field,variables,index,constant,exponent):
    # (X+a)^e in characteristic two: only binary submasks of e occur.
    if not constant:
        exps=[0]*variables
        exps[index]=exponent
        return {tuple(exps):1}
    result={}
    sub=exponent
    while True:
        exps=[0]*variables
        exps[index]=sub
        add_term(result,tuple(exps),field.power(constant,exponent-sub))
        if sub==0:
            break
        sub=(sub-1)&exponent
    return result


def output_polynomial(desc):
    desc,field=normalize_descriptor(desc)
    r,modulus,phases,basis,output=desc
    layers=len(phases)
    s=2*layers-1
    a=field.dual(output)
    zero=(0,)*s
    def variable(index,shift=0):
        powers=[0]*s
        powers[index]=1
        out={tuple(powers):1}
        if shift:
            out[zero]=shift
        return out
    ket=[variable(i) for i in range(layers)]
    bra=[variable(layers+i) for i in range(layers-1)]+[variable(layers-1,a)]
    phase={}
    for i,terms in enumerate(phases):
        for exponent,coefficient in terms:
            exps=[0]*s
            exps[i]=exponent
            add_term(phase,tuple(exps),coefficient)
            other=(layers+i) if i<layers-1 else layers-1
            expanded=affine_power(field,s,other,0 if i<layers-1 else a,exponent)
            for powers,c in expanded.items():
                add_term(phase,powers,field.mul(coefficient,c))
    for powers,c in mv_add(ket[0],bra[0]).items():
        add_term(phase,powers,field.mul(basis,c))
    for i in range(layers-1):
        phase=mv_add(phase,mv_mul(field,ket[i],ket[i+1]))
        phase=mv_add(phase,mv_mul(field,bra[i],bra[i+1]))
    aspoly={e+(0,):c for e,c in phase.items()}
    add_term(aspoly,(0,)*s+(2,),1)
    add_term(aspoly,(0,)*s+(1,),1)
    degree=max(sum(e) for e in aspoly)
    return dict(field=field,phase=phase,artin_schreier=aspoly,field_variables=s,
                count_variables=s+1,layers=layers,degree=degree,
                denominator=1 << (r*layers),padic_bits=r*(s+2),dual=a)


def evaluate_mv(field,poly,values):
    total=0
    for exponents,coefficient in poly.items():
        term=coefficient
        for x,e in zip(values,exponents):
            if e:
                term=field.mul(term,field.power(x,e))
        total ^= term
    return total


def enumerate_reduction(reduction):
    """Exponential verification only; NOT the Lauder-Wan backend."""
    field=reduction['field']
    image=[0]*field.q
    for y in range(field.q):
        image[field.mul(y,y)^y] += 1
    signed,points=0,0
    for values in product(range(field.q),repeat=reduction['field_variables']):
        z=evaluate_mv(field,reduction['phase'],values)
        signed += -1 if field.trace(z) else 1
        points += image[z]
    assert signed == points-field.q**reduction['field_variables']
    denominator=reduction['denominator']
    probability=Fraction(denominator-signed,2*denominator)
    assert 0 <= probability <= 1
    return probability,signed,points


def trace_reduce(field,terms):
    """Remove even exponents under the absolute trace; sparse, exact."""
    out={}
    for e,a in terms:
        while e and not e&1:
            e >>= 1
            a=field.power(a,1 << (field.r-1))
        out[e]=out.get(e,0)^a
    return [[e,a] for e,a in sorted(out.items()) if a]


def cyclotomic_orbit(r,exponent):
    modulus=(1 << r)-1
    value=((exponent-1)%modulus)+1
    start=value
    result=[]
    while True:
        result.append(value)
        value=((2*value-1)%modulus)+1
        if value==start:
            return result


def norm_phase(s):
    r=3*s
    exponent=1+(1 << s)+(1 << (2*s))
    orbit=cyclotomic_orbit(r,exponent)
    assert len(orbit)==s and min(orbit)==exponent
    return dict(extension_degree=r,exponent=exponent,minimum_trace_degree=exponent,
                signed_sum=-(1 << (2*s))-(1 << s),orbit_length=len(orbit))
