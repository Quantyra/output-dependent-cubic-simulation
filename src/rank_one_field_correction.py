"""S173/R05-04: recover rank-one field defects and build exact cubic counts.

The affine point-count backend is an external theorem, not implemented here.
All source discovery and count-polynomial construction are explicit.
"""
from fractions import Fraction
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
from finite_field_descent import echelon, solve
from frobenius_trace_degree import affine_product
from magic_residual_counts import quadratic_sum


def matrix_add(a,b):
    return tuple(x^y for x,y in zip(a,b))


def outer(v,n):
    return tuple(v if v >> j & 1 else 0 for j in range(n))


def commutator(T,J):
    return matrix_add(cc.compose(cc.transpose(T),J),cc.compose(J,T))


def recover_correction(D,J):
    """Return a verified balanced J0 and rank <=1 binary defect, or refuse."""
    balanced=D.pairing(J)
    if balanced is not None:
        return dict(mask=0,balanced_matrix=tuple(J),pairing=balanced,
                    method='already_balanced',commutator_ranks=[0,0]),'ok'
    T=D.generator
    first=commutator(T,J)
    span=echelon(first)
    if len(span)!=2:
        return None,'first_commutator_not_rank_two'
    basis=[x[0] for x in span.values()]
    candidates=[basis[0],basis[1],basis[0]^basis[1]]
    second=commutator(cc.compose(T,T),J)
    second_span=echelon(second)
    if D.s>=3:
        candidates=[v for v in candidates if solve(second_span,v) is not None]
        if len(second_span)!=2 or len(candidates)!=1:
            return None,'commutator_intersection_not_a_line'
    elif D.s!=2:
        return None,'unsupported_field_degree'
    for v in candidates:
        J0=matrix_add(J,outer(v,D.n))
        pairing=D.pairing(J0)
        if pairing is not None:
            return dict(mask=v,balanced_matrix=J0,pairing=pairing,
                        method='two_commutator_line' if D.s>=3 else 'three_candidates',
                        commutator_ranks=[len(span),len(second_span)]),'ok'
    return None,'correction_not_balanced'


def pairing_polynomial(coefficients):
    poly={}
    for a in range(3):
        for b in range(3):
            e=[0]*6;e[a]=1;e[3+b]=1
            ff.add_term(poly,tuple(e),coefficients[a][b])
    return poly


def selector_quadratic(L,delta):
    """Ket and bra paths share the last vertex; the final bra is shifted."""
    ket=[(1 << j,0) for j in range(L)]
    bra=[(1 << (L+j),0) for j in range(L-1)]+[(1 << (L-1),delta)]
    terms=set()
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            terms ^= affine_product((x,y))
    return terms


def discover_source(desc,h,rng):
    desc=cc.normalize_descriptor(desc)
    _,n,J,phases,basis,output=desc
    anchor=next((p for p in phases if any(m.bit_count()==3 for m in p)),None)
    if anchor is None:return None,'no_cubic_anchor'
    D,reason=cc.discover_field(n,anchor,h,rng)
    if D is None:return None,reason
    reconstructor=cc.PhaseReconstructor(D)
    polynomials=[reconstructor.reconstruct(p) for p in phases]
    if any(p is None for p in polynomials):
        return None,'phase_outside_cubic_field_span'
    if len(phases)==1:
        correction=dict(mask=0,balanced_matrix=None,pairing=None,
                        method='unused_one_layer',commutator_ranks=[])
        pairpoly={}
    else:
        correction,reason=recover_correction(D,J)
        if correction is None:return None,reason
        pairpoly=pairing_polynomial(correction['pairing'])
    source=dict(descriptor=desc,structure=D,polynomials=polynomials,
                pairing_polynomial=pairpoly,correction=correction,
                phase_span_dimension=len(reconstructor.span))
    base=cc.count_polynomial(source)
    mask=correction['mask']
    shift=cc.action(cc.inverse(J),1 << output)
    L=len(phases)
    source.update(base=base,field=D.field,k=2*L-1,
                  ell=D.linear_coefficients(mask),
                  selector=selector_quadratic(L,(mask&shift).bit_count()&1) if mask else set())
    return source,'ok'


def reduce_native(n,gates,basis,output,h,rng):
    desc=cc.recognize_native(n,gates,basis,output)
    return discover_source(desc,h,rng)


def walsh_coefficient(terms,k,z):
    linear={i for i in range(k) if z >> i & 1}
    pairs=set()
    for mask in terms:
        indices=[i for i in range(k) if mask >> i & 1]
        if len(indices)==1:linear ^= {indices[0]}
        elif len(indices)==2:pairs.add(tuple(indices))
        elif len(indices)>2:raise ValueError('selector phase is not quadratic')
    return quadratic_sum(int(0 in terms),linear,pairs,k)


def cubic_branches(source):
    """Stream (selector frequency, integer Walsh weight, cubic count)."""
    base=source['base'];k=source['k'];m=base['field_variables']
    candidates=range(1 << k) if source['correction']['mask'] else (0,)
    for z in candidates:
        w=walsh_coefficient(source['selector'],k,z)
        if not w:continue
        phase=dict(base['phase'])
        for j in range(k):
            if z >> j & 1:
                for a,c in enumerate(source['ell']):
                    e=[0]*m;e[3*j+a]=1
                    ff.add_term(phase,tuple(e),c)
        aspoly={e+(0,):c for e,c in phase.items()}
        ff.add_term(aspoly,(0,)*m+(1,),1)
        ff.add_term(aspoly,(0,)*m+(2,),1)
        branch=dict(base,phase=phase,artin_schreier=aspoly,
                    degree=max(map(sum,aspoly)))
        yield z,w,branch


def exact_divide(a,b):
    q,r=divmod(a,b)
    if r:raise ValueError('count violates integral normalization')
    return q


def probability_from_signed(source,signed):
    denominator=source['base']['denominator']
    if abs(signed)>denominator:
        raise ValueError('signed sum outside physical output range')
    return Fraction(denominator-signed,2*denominator)


def combine_counts(source,weighted_counts):
    """Input has precisely the (weight, exact affine count) of every branch."""
    mass=source['field'].q**source['base']['field_variables']
    signed=exact_divide(sum(w*(count-mass) for w,count in weighted_counts),
                        1 << source['k'])
    return probability_from_signed(source,signed),signed


def auxiliary_count(source):
    """Return the complete equation system and its degree <=4 hypersurface."""
    K=source['field'];k=source['k'];m=source['base']['field_variables']
    v=m+2*k+1
    tau=next(1 << j for j in range(K.r) if K.trace(1 << j))
    def monomial(j,power=1,c=1):
        e=[0]*v;e[j]=power
        return {tuple(e):c} if c else {}
    equations=[]
    for j in range(k):
        bit=m+j;lift=m+k+j
        equations.append(ff.mv_add(monomial(bit,2),monomial(bit)))
        equation=ff.mv_add(monomial(lift,2),monomial(lift))
        equation=ff.mv_add(equation,monomial(bit,c=tau))
        for a,c in enumerate(source['ell']):
            equation=ff.mv_add(equation,monomial(3*j+a,c=c))
        equations.append(equation)
    phase={e+(0,)*(2*k+1):c for e,c in source['base']['phase'].items()}
    for mask in source['selector']:
        e=[0]*v
        for j in range(k):
            if mask >> j & 1:e[m+j]=1
        ff.add_term(phase,tuple(e),tau)
    final=ff.mv_add(phase,ff.mv_add(monomial(v-1,2),monomial(v-1)))
    equations.append(final)
    r=len(equations)
    hypersurface={}
    for j,equation in enumerate(equations):
        tail=tuple(int(j==i) for i in range(r))
        for exponent,c in equation.items():
            ff.add_term(hypersurface,exponent+tail,c)
    return dict(field=K,equations=equations,system_variables=v,equation_count=r,
                hypersurface=hypersurface,count_variables=v+r,
                degree=max(map(sum,hypersurface)),tau=tau,
                padic_bits=K.r*(v+r+1))


def auxiliary_readout(source,aux,count):
    q=source['field'].q
    v,r=aux['system_variables'],aux['equation_count']
    system=exact_divide(count-q**(v+r-1),(q-1)*q**(r-1))
    signed=exact_divide(system,1 << source['k'])-q**source['base']['field_variables']
    return probability_from_signed(source,signed),signed,system


def round_probability(probability,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision required')
    return Fraction((probability.numerator << bits)//probability.denominator,1 << bits)
