"""S173/R05-03: minimum numerical trace degree from explicit Boolean ANF.

All polynomial functions use reduced exponents 0,...,q-1, including at zero.
This constructs the full output count; it does not implement point counting.
"""
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
from finite_field_descent import echelon,solve


def reduced_exponent(e,q):
    return 0 if e==0 else 1+(e-1)%(q-1)


def reduced_product(K,left,right):
    out={}
    for a,c in left.items():
        for b,d in right.items():
            e=tuple(reduced_exponent(x+y,K.q) for x,y in zip(a,b))
            ff.add_term(out,e,K.mul(c,d))
    return out


def frobenius_exponent(K,e):
    return tuple(reduced_exponent(2*x,K.q) for x in e)


def square_function(K,poly):
    return {frobenius_exponent(K,e):K.mul(c,c) for e,c in poly.items()}


def trace_function(K,poly):
    current={}
    for e,c in poly.items():
        ff.add_term(current,tuple(reduced_exponent(x,K.q) for x in e),c)
    out={}
    for _ in range(K.r):
        out=ff.mv_add(out,current)
        current=square_function(K,current)
    return out


def trace_linear_form(K,coefficients):
    """Canonical K polynomial for Tr(sum_a coefficients[a] X_a)."""
    out={}
    m=len(coefficients)
    for a,c in enumerate(coefficients):
        for t in range(K.r):
            if c:
                e=[0]*m;e[a]=1 << t
                out[tuple(e)]=c
            c=K.mul(c,c)
    return out


def canonical_anf(K,masks,linear_forms,variables):
    """Expand an explicit cubic ANF through known trace-linear bit maps."""
    out={}
    zero=(0,)*variables
    for mask in masks:
        if type(mask) is not int or mask<0 or mask.bit_length()>len(linear_forms) or mask.bit_count()>3:
            raise ValueError('explicit Boolean ANF degree at most three required')
        term={zero:1}
        while mask:
            low=mask&-mask
            term=reduced_product(K,term,linear_forms[low.bit_length()-1])
            mask ^= low
        out=ff.mv_add(out,term)
    if square_function(K,out)!=out:
        raise ValueError('supplied bit maps do not produce a Boolean function')
    return out


def frobenius(K,value,power):
    for _ in range(power):
        value=K.mul(value,value)
    return value


def relative_trace(K,value,length):
    if length<1 or K.r%length:
        raise ValueError('orbit length must divide extension degree')
    answer=0
    for _ in range(K.r//length):
        answer ^= value
        value=frobenius(K,value,length)
    return answer


class RelativeTraceSolver:
    def __init__(self,K):
        self.K=K
        self.spans={}

    def preimage(self,value,length):
        K=self.K
        if length not in self.spans:
            columns=[relative_trace(K,1 << j,length) for j in range(K.r)]
            span=echelon(columns)
            assert len(span)==length
            self.spans[length]=span
        answer=solve(self.spans[length],value)
        if answer is None:
            raise ValueError('coefficient is outside the orbit subfield')
        assert relative_trace(K,answer,length)==value
        return answer


def optimize_trace(K,canonical,variables):
    """Exact minimum among all trace polynomials in these K coordinates."""
    if any(len(e)!=variables or any(type(x) is not int or not 0<=x<K.q for x in e)
           or type(c) is not int or not 0<c<K.q for e,c in canonical.items()):
        raise ValueError('canonical reduced polynomial required')
    if square_function(K,canonical)!=canonical:
        raise ValueError('polynomial function is not Boolean')
    remaining=set(canonical)
    solver=RelativeTraceSolver(K)
    polynomial={}
    orbits=[]
    for start in sorted(canonical):
        if start not in remaining:
            continue
        orbit=[]
        e=start
        while not orbit or e!=start:
            orbit.append(e)
            assert e in remaining
            remaining.remove(e)
            e=frobenius_exponent(K,e)
        representative=min(orbit,key=lambda x:(sum(x),x))
        coefficient=solver.preimage(canonical[representative],len(orbit))
        assert coefficient
        polynomial[representative]=coefficient
        orbits.append(dict(representative=list(representative),length=len(orbit),
                           degree=sum(representative),seed=canonical[representative],
                           trace_coefficient=coefficient))
    assert not remaining
    assert trace_function(K,polynomial)==canonical
    degree=max((sum(e) for e in polynomial),default=0)
    return dict(polynomial=polynomial,degree=degree,orbits=orbits,
                canonical_terms=len(canonical))


def toggle(target,value):
    if value in target:target.remove(value)
    else:target.add(value)


def affine_product(forms):
    """Each form is (one variable mask, constant bit), in the Boolean ring."""
    terms={0}
    for variable,constant in forms:
        following=set()
        for t in terms:
            toggle(following,t|variable)
            if constant:toggle(following,t)
        terms=following
    return terms


def output_anf(desc):
    """Construct the complete doubled physical-output phase before field conversion."""
    _,n,J,phases,basis,output=cc.normalize_descriptor(desc)
    L=len(phases)
    def vector(block,shift=0):
        return [(1 << (block*n+j),(shift >> j)&1) for j in range(n)]
    ket=[vector(i) for i in range(L)]
    bra=[vector(L+i) for i in range(L-1)]
    bra.append(vector(L-1,cc.action(cc.inverse(J),1 << output)))
    anf=set()
    def add_forms(forms):
        for term in affine_product(forms):toggle(anf,term)
    for phase,x,y in zip(phases,ket,bra):
        for mask in phase:
            indices=[j for j in range(n) if mask >> j & 1]
            add_forms([x[j] for j in indices])
            add_forms([y[j] for j in indices])
    linear=cc.action(J,basis)
    for j in range(n):
        if linear >> j & 1:
            add_forms([ket[0][j]])
            add_forms([bra[0][j]])
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            for j,column in enumerate(J):
                for i in range(n):
                    if column >> i & 1:add_forms([x[i],y[j]])
    assert all(mask.bit_count()<=3 for mask in anf)
    return sorted(anf)


def output_spectrum(desc,structure):
    n=structure.n
    K=structure.field
    L=len(desc[3])
    vectors=2*L-1
    variables=3*vectors
    local=[trace_linear_form(K,structure.linear_coefficients(1 << j)) for j in range(n)]
    forms=[]
    for block in range(vectors):
        for polynomial in local:
            forms.append({(0,)*(3*block)+e+(0,)*(3*(vectors-block-1)):c
                          for e,c in polynomial.items()})
    anf=output_anf(desc)
    canonical=canonical_anf(K,anf,forms,variables)
    certificate=optimize_trace(K,canonical,variables)
    return anf,canonical,certificate


def reduce_native(n,gates,basis,output,h,rng):
    desc=cc.recognize_native(n,gates,basis,output)
    anchor=next((phase for phase in desc[3] if any(m.bit_count()==3 for m in phase)),None)
    if anchor is None:return None,'no_cubic_anchor'
    structure,reason=cc.discover_field(n,anchor,h,rng)
    if structure is None:return None,reason
    anf,canonical,certificate=output_spectrum(desc,structure)
    K=structure.field
    L=len(desc[3])
    variables=3*(2*L-1)
    polynomial=certificate['polynomial']
    aspoly={e+(0,):c for e,c in polynomial.items()}
    ff.add_term(aspoly,(0,)*variables+(1,),1)
    ff.add_term(aspoly,(0,)*variables+(2,),1)
    reduction=dict(field=K,phase=polynomial,artin_schreier=aspoly,
                   field_variables=variables,count_variables=variables+1,layers=L,
                   degree=max(2,certificate['degree']),minimum_trace_degree=certificate['degree'],
                   denominator=1 << (n*L),padic_bits=K.r*(variables+2))
    details=dict(descriptor=desc,structure=structure,output_anf=anf,
                 canonical=canonical,certificate=certificate)
    return reduction,details
