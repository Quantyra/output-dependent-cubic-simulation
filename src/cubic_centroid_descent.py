"""S173/R05-02: discover scalar fields from explicit native cubic phases.

All accepted phases and Fourier pairings are verified. Count construction only;
the external p-adic algorithm is not implemented here.
"""
import json
from itertools import combinations, product
import finite_field_acceptance as ff
from finite_field_descent import echelon, solve, xor_sum


def identity(n):
    return tuple(1 << i for i in range(n))


def action(columns,x):
    return xor_sum(c for j,c in enumerate(columns) if x >> j & 1)


def compose(a,b):
    return tuple(action(a,x) for x in b)


def transpose(a):
    n=len(a)
    return tuple(sum(((a[i] >> j)&1) << i for i in range(n)) for j in range(n))


def inverse(a):
    p=echelon(a)
    if len(p)!=len(a):
        raise ValueError('singular binary matrix')
    return tuple(solve(p,1 << i) for i in range(len(a)))


def flatten(a):
    n=len(a)
    return sum(c << (n*j) for j,c in enumerate(a))


def unflatten(value,n):
    return tuple((value >> (n*j)) & ((1 << n)-1) for j in range(n))


def nullspace(rows,width):
    pivots={}
    for row in rows:
        while row:
            j=row.bit_length()-1
            if j not in pivots:
                pivots[j]=row
                break
            row ^= pivots[j]
    free=[j for j in range(width) if j not in pivots]
    result=[]
    for j in free:
        value=1 << j
        for p in sorted(pivots):
            if (pivots[p]&value).bit_count()&1:
                value ^= 1 << p
        result.append(value)
    return result


def anf_masks(n,degree=3):
    return [sum(1 << j for j in indices) for d in range(degree+1)
            for indices in combinations(range(n),d)]


def anf_evaluate(masks,x):
    return sum((x&m)==m for m in masks)&1


def anf_from_function(n,function):
    masks=anf_masks(n)
    values={m:function(m) for m in masks}
    result=[]
    for m in masks:
        coefficient=0
        sub=m
        while True:
            coefficient ^= values[sub]
            if sub==0:
                break
            sub=(sub-1)&m
        if coefficient:
            result.append(m)
    return result


def centroid(n,phase):
    triples={m for m in phase if m.bit_count()==3}
    def value(i,j,k):
        return int(len({i,j,k})==3 and ((1 << i)|(1 << j)|(1 << k)) in triples)
    def equations():
        for i,j,k in product(range(n),repeat=3):
            first=sum(value(a,j,k) << (a+n*i) for a in range(n))
            second=sum(value(i,a,k) << (a+n*j) for a in range(n))
            third=sum(value(i,j,a) << (a+n*k) for a in range(n))
            yield first^second
            yield first^third
    return [unflatten(v,n) for v in nullspace(equations(),n*n)]


class TensorField:
    def __init__(self,n,field,generator,attempts,centroid_basis):
        self.n=n
        self.field=field
        self.s=field.r
        self.generator=generator
        self.attempts=attempts
        self.centroid_basis=centroid_basis
        self.powers=[identity(n)]
        for _ in range(1,self.s):
            self.powers.append(compose(generator,self.powers[-1]))
        columns=[]
        module=[]
        for _ in range(3):
            span=echelon(columns)
            v=next(1 << i for i in range(n) if solve(span,1 << i) is None)
            module.append(v)
            columns.extend(action(t,v) for t in self.powers)
        if len(echelon(columns))!=n:
            raise ValueError('field does not have a three-dimensional module')
        self.module_basis=module
        self.columns=tuple(columns)
        self.inverse=inverse(self.columns)
        self.dual=[field.dual(j) for j in range(self.s)]

    def coordinates(self,x):
        packed=action(self.inverse,x)
        return tuple((packed >> (i*self.s)) & (self.field.q-1) for i in range(3))

    def physical(self,values):
        return action(self.columns,sum(v << (i*self.s) for i,v in enumerate(values)))

    def linear_coefficients(self,mask):
        return [xor_sum(self.dual[j] for j in range(self.s)
                        if (mask&self.columns[i*self.s+j]).bit_count()&1)
                for i in range(3)]

    def pairing(self,J):
        for t in self.centroid_basis:
            if compose(transpose(t),J)!=compose(J,t):
                return None
        coefficients=[self.linear_coefficients(action(J,v)) for v in self.module_basis]
        # Independently verify every physical binary basis pair.
        for i in range(self.n):
            x=self.coordinates(1 << i)
            for j in range(self.n):
                y=self.coordinates(1 << j)
                z=xor_sum(self.field.mul(coefficients[a][b],self.field.mul(x[a],y[b]))
                          for a in range(3) for b in range(3))
                if self.field.trace(z)!=((J[j] >> i)&1):
                    raise AssertionError('pairing reconstruction failed')
        return coefficients


def discover_field(n,phase,h,rng):
    if n%3 or n<3 or type(h) is not int or h<1:
        return None,'dimension_or_confidence'
    basis=centroid(n,phase)
    s=n//3
    if len(basis)!=s:
        return None,'centroid_dimension'
    flat=[flatten(t) for t in basis]
    span=echelon(flat)
    unit=flatten(identity(n))
    if solve(span,unit) is None:
        return None,'missing_identity'
    for attempt in range(1,h+1):
        tape=rng.getrandbits(s) if s>1 else None
        value=xor_sum(t for j,t in enumerate(flat) if tape >> j & 1) if s>1 else unit
        generator=unflatten(value,n)
        powers=[identity(n)]
        for _ in range(s):
            powers.append(compose(generator,powers[-1]))
        columns=[flatten(t) for t in powers[:-1]]
        if any(solve(span,t) is None for t in columns):
            continue
        independent=echelon(columns)
        if len(independent)!=s:
            continue
        tail=solve(independent,flatten(powers[-1]))
        if tail is None or not ff.irreducible((1 << s)|tail):
            continue
        K=ff.Field((1 << s)|tail)
        return TensorField(n,K,generator,attempt,basis),'ok'
    return None,'bounded_generator_failure'


class PhaseReconstructor:
    def __init__(self,structure):
        self.structure=structure
        n,K=structure.n,structure.field
        self.masks=anf_masks(n)
        self.positions={m:i for i,m in enumerate(self.masks)}
        self.monomials=[e for e in product(range(4),repeat=3) if sum(e)<=3]
        self.specs=[(e,j) for e in self.monomials for j in range(K.r)]
        coordinates={m:structure.coordinates(m) for m in self.masks}
        columns=[]
        for e,j in self.specs:
            values={}
            for m,x in coordinates.items():
                value=1 << j
                for a,power in zip(x,e):
                    value=K.mul(value,K.power(a,power))
                values[m]=K.trace(value)
            packed=0
            for i,m in enumerate(self.masks):
                coefficient=0
                sub=m
                while True:
                    coefficient ^= values[sub]
                    if sub==0:break
                    sub=(sub-1)&m
                packed |= coefficient << i
            columns.append(packed)
        self.columns=columns
        self.span=echelon(columns)

    def reconstruct(self,masks):
        target=xor_sum(1 << self.positions[m] for m in masks)
        coeffs=solve(self.span,target)
        if coeffs is None:
            return None
        assert xor_sum(c for j,c in enumerate(self.columns) if coeffs >> j & 1)==target
        result={}
        for i,(e,j) in enumerate(self.specs):
            if coeffs >> i & 1:
                ff.add_term(result,e,1 << j)
        return result


def reconstruct_pairing(structure,J):
    """Exact cross-bilinear functions represented at K-degree at most three."""
    n,K=structure.n,structure.field
    coords=[structure.coordinates(1 << i) for i in range(n)]
    specs=[]
    columns=[]
    for a,b in product(range(3),repeat=2):
        for p,q in ((1,1),(2,1),(1,2)):
            powers=[0]*6
            powers[a]=p
            powers[3+b]=q
            for k in range(K.r):
                packed=0
                for i,x in enumerate(coords):
                    for j,y in enumerate(coords):
                        z=K.mul(1 << k,K.mul(K.power(x[a],p),K.power(y[b],q)))
                        packed |= K.trace(z) << (i+n*j)
                specs.append((tuple(powers),k))
                columns.append(packed)
    span=echelon(columns)
    target=flatten(J)
    solution=solve(span,target)
    if solution is None:
        return None,len(span)
    assert xor_sum(c for j,c in enumerate(columns) if solution >> j & 1)==target
    polynomial={}
    for j,(powers,k) in enumerate(specs):
        if solution >> j & 1:
            ff.add_term(polynomial,powers,1 << k)
    return polynomial,len(span)


def normalize_descriptor(desc):
    if not isinstance(desc,list) or len(desc)!=6 or desc[0]!='cubic-field-v1':
        raise ValueError('cubic native descriptor required')
    _,n,J,phases,basis,output=desc
    if (type(n) is not int or n<1 or not isinstance(J,list) or len(J)!=n
        or any(type(x) is not int or x<0 or x.bit_length()>n for x in J)
        or type(basis) is not int or basis<0 or basis.bit_length()>n
        or type(output) is not int or not 0<=output<n
        or not isinstance(phases,list) or not phases):
        raise ValueError('invalid native boundary')
    if tuple(J)!=transpose(J):
        raise ValueError('symmetric Fourier pairing required')
    inverse(J)
    normalized=[]
    for phase in phases:
        if not isinstance(phase,list):
            raise ValueError('ANF mask list required')
        terms=set()
        for m in phase:
            if type(m) is not int or m<0 or m.bit_length()>n or m.bit_count()>3:
                raise ValueError('only Boolean degree at most three admitted')
            if m in terms:terms.remove(m)
            else:terms.add(m)
        normalized.append(sorted(terms))
    return ['cubic-field-v1',n,list(J),normalized,basis,output]


def compile_native(desc):
    desc=normalize_descriptor(desc)
    _,n,J,phases,basis,output=desc
    gates=ff.header(desc)
    fourier=ff.linear_map_gates(J)+[('H',j) for j in range(n)]
    gates+=fourier
    for phase in phases:
        for mask in phase:
            wires=[j for j in range(n) if mask >> j & 1]
            if not wires:
                gates += [('X',0),('Z',0),('X',0),('Z',0)]
            elif len(wires)==1:
                gates.append(('Z',wires[0]))
            else:
                gates.append(('H',wires[-1]))
                gates.extend([('CX',*wires)] if len(wires)==2 else ff.toffoli_decomposition(*wires))
                gates.append(('H',wires[-1]))
        gates+=fourier
    return dict(qubits=n,gates=gates,basis=basis,output=output,descriptor=desc,
                source_bits=8*len(json.dumps([n,gates,basis,output],separators=(',',':'))))


def recognize_native(n,gates,basis,output):
    bits=[]
    for i in range(0,len(gates)-1,2):
        a,b=tuple(gates[i]),tuple(gates[i+1])
        if a==b==('H',0):break
        if a!=b or a not in (('X',0),('Z',0)):
            raise ValueError('canonical header missing')
        bits.append(int(a[0]=='Z'))
    else:raise ValueError('unterminated header')
    if len(bits)%8:raise ValueError('incomplete header')
    raw=bytes(sum(bits[j+k] << (7-k) for k in range(8)) for j in range(0,len(bits),8))
    try:desc=json.loads(raw.decode('ascii'))
    except (ValueError,UnicodeError) as error:raise ValueError('malformed header') from error
    if (not isinstance(desc,list) or len(desc)!=6 or type(desc[1]) is not int
        or desc[1]>len(gates)+1):
        raise ValueError('oversized or malformed descriptor')
    candidate=compile_native(desc)
    if (candidate['qubits']!=n or candidate['basis']!=basis or candidate['output']!=output
        or candidate['gates']!=[tuple(g) for g in gates]):
        raise ValueError('body differs from native expansion')
    return candidate['descriptor']


def discover_source(desc,h,rng):
    desc=normalize_descriptor(desc)
    _,n,J,phases,basis,output=desc
    anchor=next((p for p in phases if any(m.bit_count()==3 for m in p)),None)
    if anchor is None:return None,'no_cubic_anchor'
    structure,reason=discover_field(n,anchor,h,rng)
    if structure is None:return None,reason
    # Final-output orthogonality removes all internal pairings at L=1.
    pairing_needed=len(phases)>1
    pairing=structure.pairing(J) if pairing_needed else None
    pairing_polynomial,pairing_dimension=(reconstruct_pairing(structure,J)
                                         if pairing_needed else ({},0))
    if pairing_polynomial is None:return None,'pairing_outside_cubic_field_span'
    reconstructor=PhaseReconstructor(structure)
    polynomials=[reconstructor.reconstruct(p) for p in phases]
    if any(p is None for p in polynomials):return None,'phase_outside_cubic_field_span'
    return dict(descriptor=desc,structure=structure,pairing=pairing,
                pairing_needed=pairing_needed,
                pairing_polynomial=pairing_polynomial,
                pairing_span_dimension=pairing_dimension,
                polynomials=polynomials,phase_span_dimension=len(reconstructor.span)),'ok'


def count_polynomial(source):
    _,n,J,phases,basis,output=source['descriptor']
    D=source['structure']
    K=D.field
    L=len(phases)
    variables=3*(2*L-1)
    zero=(0,)*variables
    def variable(j,c=0):
        e=[0]*variables;e[j]=1
        p={tuple(e):1}
        if c:p[zero]=c
        return p
    ket=[tuple(variable(3*i+j) for j in range(3)) for i in range(L)]
    bra=[tuple(variable(3*(L+i)+j) for j in range(3)) for i in range(L-1)]
    shift=D.coordinates(action(inverse(J),1 << output))
    bra.append(tuple(variable(3*(L-1)+j,shift[j]) for j in range(3)))
    def scaled(p,c):
        return {e:K.mul(v,c) for e,v in p.items() if c}
    def substitute(poly,vector):
        result={}
        for powers,c in poly.items():
            term={zero:c}
            for p,x in zip(powers,vector):
                for _ in range(p):term=ff.mv_mul(K,term,x)
            result=ff.mv_add(result,term)
        return result
    phase={}
    for p,x,y in zip(source['polynomials'],ket,bra):
        phase=ff.mv_add(phase,substitute(p,x))
        phase=ff.mv_add(phase,substitute(p,y))
    for a,x,y in zip(D.linear_coefficients(action(J,basis)),ket[0],bra[0]):
        phase=ff.mv_add(phase,scaled(ff.mv_add(x,y),a))
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            phase=ff.mv_add(phase,substitute(source['pairing_polynomial'],x+y))
    aspoly={e+(0,):c for e,c in phase.items()}
    ff.add_term(aspoly,(0,)*variables+(1,),1)
    ff.add_term(aspoly,(0,)*variables+(2,),1)
    return dict(field=K,phase=phase,artin_schreier=aspoly,field_variables=variables,
                count_variables=variables+1,layers=L,degree=max(map(sum,aspoly)),
                denominator=1 << (n*L),padic_bits=K.r*(variables+2))


def reduce_native(n,gates,basis,output,h,rng):
    desc=recognize_native(n,gates,basis,output)
    source,reason=discover_source(desc,h,rng)
    return (count_polynomial(source),source) if source is not None else (None,reason)
