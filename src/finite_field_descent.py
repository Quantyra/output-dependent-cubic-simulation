"""Paid cubic subfield descent for the R05 norm-phase native family.

This constructs the count polynomial only. The Lauder-Wan backend remains
external; finite enumeration in the checker is not a polynomial-time solver.
"""
import finite_field_acceptance as ff


def xor_sum(values):
    out=0
    for value in values:
        out ^= value
    return out


def echelon(columns):
    pivots={}
    for j,column in enumerate(columns):
        value,mask=column,1 << j
        while value:
            top=value.bit_length()-1
            if top not in pivots:
                pivots[top]=(value,mask)
                break
            v,m=pivots[top]
            value ^= v
            mask ^= m
    return pivots


def solve(pivots,value):
    mask=0
    while value:
        top=value.bit_length()-1
        if top not in pivots:
            return None
        v,m=pivots[top]
        value ^= v
        mask ^= m
    return mask


def kernel(columns,n):
    rows=[sum(((column >> i)&1) << j for j,column in enumerate(columns))
          for i in range(n)]
    positions=[]
    used=0
    for col in range(n):
        pivot=next((i for i in range(used,n) if rows[i] >> col & 1),None)
        if pivot is None:
            continue
        rows[used],rows[pivot]=rows[pivot],rows[used]
        for i in range(n):
            if i!=used and rows[i] >> col & 1:
                rows[i] ^= rows[used]
        positions.append(col)
        used += 1
    free=[j for j in range(n) if j not in positions]
    return [(1 << j) ^ xor_sum(((rows[i] >> j)&1) << p
                              for i,p in enumerate(positions)) for j in free]


class CubicDescent:
    def __init__(self,extension,subfield,generator,theta,attempts):
        self.extension=extension
        self.field=subfield
        self.s=subfield.r
        self.generator=generator
        self.basis=[1,theta,extension.mul(theta,theta)]
        self.powers=[extension.power(generator,j) for j in range(self.s)]
        self.columns=[extension.mul(beta,g) for beta in self.basis for g in self.powers]
        self.pivots=echelon(self.columns)
        if len(self.pivots)!=extension.r:
            raise AssertionError('not an extension basis')
        self.attempts=attempts
        # Norm: multiply the three conjugate linear forms, then identify K.
        norm={(0,0,0):1}
        for j in range(3):
            linear={}
            for i,beta in enumerate(self.basis):
                exps=[0,0,0]
                exps[i]=1
                linear[tuple(exps)]=extension.power(beta,1 << (j*self.s))
            norm=ff.mv_mul(extension,norm,linear)
        self.norm={e:self.in_subfield(c) for e,c in norm.items()}
        self.pairing=[[self.relative_trace(extension.mul(a,b)) for b in self.basis]
                      for a in self.basis]

    def coordinates(self,value):
        packed=solve(self.pivots,value)
        if packed is None:
            raise AssertionError('outside extension span')
        return tuple((packed >> (i*self.s)) & (self.field.q-1) for i in range(3))

    def embed(self,value):
        return xor_sum(g for j,g in enumerate(self.powers) if value >> j & 1)

    def from_coordinates(self,values):
        return xor_sum(self.extension.mul(beta,self.embed(value))
                       for beta,value in zip(self.basis,values))

    def in_subfield(self,value):
        coords=self.coordinates(value)
        if coords[1:]!=(0,0):
            raise AssertionError('coefficient outside subfield')
        return coords[0]

    def relative_trace(self,value):
        E=self.extension
        return self.in_subfield(value ^ E.power(value,1 << self.s)
                                ^ E.power(value,1 << (2*self.s)))

    def linear_trace(self,value):
        return [self.relative_trace(self.extension.mul(value,b)) for b in self.basis]


def construct_descent(extension,h,rng):
    """Every tape uses at most s*h random bits; explicit failure <= 2**(-h)."""
    if extension.r%3 or type(h) is not int or h<1:
        raise ValueError('cubic extension and positive confidence required')
    E=extension
    s=E.r//3
    fixed=kernel([E.power(1 << i,1 << s) ^ (1 << i) for i in range(E.r)],E.r)
    assert len(fixed)==s
    for attempt in range(1,h+1):
        if s==1:
            generator=1
        else:
            tape=rng.getrandbits(s)
            generator=xor_sum(v for j,v in enumerate(fixed) if tape >> j & 1)
        powers=[E.power(generator,j) for j in range(s)]
        pivots=echelon(powers)
        if len(pivots)!=s:
            continue
        tail=solve(pivots,E.power(generator,s))
        assert tail is not None
        K=ff.Field((1 << s)|tail)
        theta=next(1 << i for i in range(E.r)
                   if E.power(1 << i,1 << s)!=(1 << i))
        return CubicDescent(E,K,generator,theta,attempt)
    return None


def norm_output_polynomial(desc,h,rng):
    desc,E=ff.normalize_descriptor(desc)
    r,modulus,phases,basis,output=desc
    if r%3:
        raise ValueError('field degree must be a positive multiple of three')
    s=r//3
    exponent=1+(1 << s)+(1 << (2*s))
    if any(e not in (0,1,exponent) for phase in phases for e,c in phase):
        raise ValueError('only constant, linear and relative-norm terms admitted')
    descent=construct_descent(E,h,rng)
    if descent is None:
        return None
    K=descent.field
    L=len(phases)
    variables=3*(2*L-1)
    zero=(0,)*variables
    def variable(j,constant=0):
        e=[0]*variables
        e[j]=1
        p={tuple(e):1}
        if constant:
            p[zero]=constant
        return p
    ket=[tuple(variable(3*i+j) for j in range(3)) for i in range(L)]
    shift=descent.coordinates(E.dual(output))
    bra=[tuple(variable(3*(L+i)+j) for j in range(3)) for i in range(L-1)]
    bra.append(tuple(variable(3*(L-1)+j,shift[j]) for j in range(3)))
    def scaled(poly,coefficient):
        return {e:K.mul(c,coefficient) for e,c in poly.items() if coefficient}
    def norm(vector):
        result={}
        for powers,c in descent.norm.items():
            term={zero:c}
            for p,t in zip(powers,vector):
                for _ in range(p):
                    term=ff.mv_mul(K,term,t)
            result=ff.mv_add(result,term)
        return result
    def phase_value(terms,vector):
        result={}
        for e,c in terms:
            if e==exponent:
                result=ff.mv_add(result,scaled(norm(vector),descent.relative_trace(c)))
            elif e==1:
                for t,a in zip(vector,descent.linear_trace(c)):
                    result=ff.mv_add(result,scaled(t,a))
            else:
                ff.add_term(result,zero,descent.relative_trace(c))
        return result
    phase={}
    for terms,x,y in zip(phases,ket,bra):
        phase=ff.mv_add(phase,phase_value(terms,x))
        phase=ff.mv_add(phase,phase_value(terms,y))
    for a,x,y in zip(descent.linear_trace(basis),ket[0],bra[0]):
        phase=ff.mv_add(phase,scaled(ff.mv_add(x,y),a))
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            for i in range(3):
                for j in range(3):
                    phase=ff.mv_add(phase,scaled(ff.mv_mul(K,x[i],y[j]),
                                                descent.pairing[i][j]))
    aspoly={e+(0,):c for e,c in phase.items()}
    ff.add_term(aspoly,(0,)*variables+(1,),1)
    ff.add_term(aspoly,(0,)*variables+(2,),1)
    return dict(field=K,phase=phase,artin_schreier=aspoly,field_variables=variables,
                count_variables=variables+1,layers=L,degree=max(map(sum,aspoly)),
                denominator=1 << (r*L),padic_bits=s*(variables+2),descent=descent)
