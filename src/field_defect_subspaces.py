"""S173/R05-05: source-derived rank-budgeted field-defect recovery.

Only construction and exact readout are implemented; the affine count backend
remains the published external theorem. No exponential candidate subspace search.
"""
from fractions import Fraction
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
import rank_one_field_correction as rc
from finite_field_descent import echelon,solve,xor_sum
from frobenius_trace_degree import affine_product
from magic_residual_counts import quadratic_sum


def image_basis(columns):
    return tuple(value for value,_ in echelon(columns).values())


def transpose_rect(columns,rows):
    return tuple(sum(((c >> i)&1) << j for j,c in enumerate(columns)) for i in range(rows))


def defect_matrix(U,H,n):
    return cc.compose(U,cc.compose(H,transpose_rect(U,n)))


def intersection(A,B,n):
    A=image_basis(A);B=image_basis(B)
    joined=A+B
    rows=transpose_rect(joined,n)
    relations=cc.nullspace(rows,len(joined))
    return image_basis(cc.action(A,z&((1 << len(A))-1)) for z in relations)


def recover_subspace(D,J,rank_limit):
    balanced=D.pairing(J)
    if balanced is not None:
        return dict(rank=0,columns=(),form=(),balanced_matrix=tuple(J),
                    pairing=balanced,method='balanced',triple_rank=0),'ok'
    T=D.generator;Tt=cc.transpose(T)
    first=rc.commutator(T,J)
    second=rc.commutator(cc.compose(T,T),J)
    dim1=len(echelon(first));dim2=len(echelon(second))
    if dim1%2 or dim1==0 or dim1!=dim2:
        return None,'unequal_or_zero_commutator_ranks'
    r=dim1//2
    if r>rank_limit:return None,'rank_budget_exceeded'
    U=intersection(first,second,D.n)
    if len(U)!=r:return None,'intersection_dimension'
    TU=cc.compose(Tt,U);T2U=cc.compose(Tt,TU)
    triple_rank=len(echelon(U+TU+T2U))
    if triple_rank!=3*r:return None,'dependent_field_translates'
    specs=[(i,j) for i in range(r) for j in range(i,r)]
    forms=[]
    commutators=[]
    for i,j in specs:
        H=[0]*r;H[j] ^= 1 << i
        if i!=j:H[i] ^= 1 << j
        forms.append(tuple(H))
        commutators.append(cc.flatten(rc.commutator(T,defect_matrix(U,H,D.n))))
    span=echelon(commutators)
    if len(span)!=len(specs):return None,'noninjective_form_system'
    solution=solve(span,cc.flatten(first))
    if solution is None:return None,'no_balanced_form'
    H=tuple(xor_sum(form[j] for i,form in enumerate(forms) if solution >> i & 1)
            for j in range(r))
    if H!=cc.transpose(H) or len(echelon(H))!=r:
        return None,'degenerate_recovered_form'
    defect=defect_matrix(U,H,D.n)
    J0=rc.matrix_add(J,defect)
    pairing=D.pairing(J0)
    if pairing is None:return None,'full_balance_failed'
    return dict(rank=r,columns=U,form=H,balanced_matrix=J0,pairing=pairing,
                method='commutator_subspace',triple_rank=triple_rank),'ok'


def certify_generator(n,basis,flat,span,tape,attempt):
    s=n//3
    value=xor_sum(t for j,t in enumerate(flat) if tape >> j & 1)
    generator=cc.unflatten(value,n)
    powers=[cc.identity(n)]
    for _ in range(s):powers.append(cc.compose(generator,powers[-1]))
    columns=[cc.flatten(t) for t in powers[:-1]]
    if any(solve(span,t) is None for t in columns):return None
    independent=echelon(columns)
    if len(independent)!=s:return None
    tail=solve(independent,cc.flatten(powers[-1]))
    if tail is None or not ff.irreducible((1 << s)|tail):return None
    return cc.TensorField(n,ff.Field((1 << s)|tail),generator,attempt,basis)


def joint_discovery(n,anchor,J,rank_limit,h,rng,pairing_needed=True):
    if (type(rank_limit) is not int or not 0<=rank_limit<=n
        or type(h) is not int or h<1 or n<3 or n%3):
        return None,None,dict(reason='invalid_parameters',trials=0,random_bits=0)
    basis=cc.centroid(n,anchor);s=n//3
    if len(basis)!=s:
        return None,None,dict(reason='centroid_dimension',trials=0,random_bits=0)
    flat=[cc.flatten(t) for t in basis];span=echelon(flat)
    if solve(span,cc.flatten(cc.identity(n))) is None:
        return None,None,dict(reason='missing_identity',trials=0,random_bits=0)
    reasons={}
    for attempt in range(1,3*h+1):
        tape=rng.getrandbits(s)
        D=certify_generator(n,basis,flat,span,tape,attempt)
        if D is None:
            reason='not_field_generator'
        else:
            if not pairing_needed:
                correction=dict(rank=0,columns=(),form=(),balanced_matrix=None,
                                pairing=None,method='unused_one_layer',triple_rank=0)
                reason='ok'
            else:
                correction,reason=recover_subspace(D,J,rank_limit)
            if correction is not None:
                return D,correction,dict(reason='ok',trials=attempt,random_bits=s*attempt,
                                        rejected=reasons,field_size_guarantee=s>=3*rank_limit+3)
        reasons[reason]=reasons.get(reason,0)+1
    return None,None,dict(reason='bounded_joint_failure',trials=3*h,random_bits=3*s*h,
                         rejected=reasons,field_size_guarantee=s>=3*rank_limit+3)


def selector_quadratic(L,H,delta):
    r=len(H)
    ket=[tuple((1 << (v*r+i),0) for i in range(r)) for v in range(L)]
    bra=[tuple((1 << ((L+v)*r+i),0) for i in range(r)) for v in range(L-1)]
    bra.append(tuple((1 << ((L-1)*r+i),(delta >> i)&1) for i in range(r)))
    terms=set()
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            for j,column in enumerate(H):
                for i in range(r):
                    if column >> i & 1:terms ^= affine_product((x[i],y[j]))
    return terms


def solve_affine(rows,rhs,width):
    """One solution of row dot z = rhs, or None; free coordinates are zero."""
    pivots={}
    variable_mask=(1 << width)-1
    for row,b in zip(rows,rhs):
        equation=row | (int(b) << width)
        while equation&variable_mask:
            j=(equation&variable_mask).bit_length()-1
            if j not in pivots:
                pivots[j]=equation;break
            equation ^= pivots[j]
        else:
            if equation >> width & 1:return None
    z=0
    for j in sorted(pivots):
        row=pivots[j]
        if ((row&z).bit_count()&1)^((row >> width)&1):z ^= 1 << j
    return z


def walsh_support(terms,t):
    polar=[0]*t
    for mask in terms:
        indices=[j for j in range(t) if mask >> j & 1]
        if len(indices)==2:
            i,j=indices;polar[i] ^= 1 << j;polar[j] ^= 1 << i
        elif len(indices)>2:raise ValueError('not quadratic')
    kernel=cc.nullspace(polar,t)
    base=solve_affine(kernel,[cc.anf_evaluate(terms,u)^int(0 in terms) for u in kernel],t)
    if base is None:raise AssertionError('quadratic kernel restriction not linear')
    return base,image_basis(polar)


def discover_source(desc,rank_limit,h,rng):
    desc=cc.normalize_descriptor(desc)
    _,n,J,phases,basis,output=desc
    anchor=next((p for p in phases if any(m.bit_count()==3 for m in p)),None)
    if anchor is None:return None,dict(reason='no_cubic_anchor')
    D,correction,details=joint_discovery(n,anchor,J,rank_limit,h,rng,len(phases)>1)
    if D is None:return None,details
    reconstructor=cc.PhaseReconstructor(D)
    polynomials=[reconstructor.reconstruct(p) for p in phases]
    if any(p is None for p in polynomials):
        return None,dict(details,reason='phase_outside_cubic_field_span')
    pairpoly=rc.pairing_polynomial(correction['pairing']) if len(phases)>1 else {}
    result=dict(descriptor=desc,structure=D,polynomials=polynomials,
                pairing_polynomial=pairpoly,correction=correction,discovery=details)
    base=cc.count_polynomial(result)
    r=correction['rank'];L=len(phases);k=2*L-1
    a=cc.action(cc.inverse(J),1 << output)
    U=correction['columns'];H=correction['form']
    delta=sum(((u&a).bit_count()&1) << i for i,u in enumerate(U))
    selector=selector_quadratic(L,H,delta)
    support=walsh_support(selector,k*r)
    if len(support[1])!=(k-1)*r:raise AssertionError('path tensor form rank')
    result.update(base=base,field=D.field,k=k,selector_bits=k*r,selector=selector,
                  ell=[D.linear_coefficients(u) for u in U],support=support,
                  rank_budget=rank_limit)
    return result,details


def reduce_native(n,gates,basis,output,rank_limit,h,rng):
    desc=cc.recognize_native(n,gates,basis,output)
    return discover_source(desc,rank_limit,h,rng)


def quadratic_parts(terms):
    linear=0;pairs=set()
    for mask in terms:
        degree=mask.bit_count()
        if degree==1:linear ^= mask
        elif degree==2:
            first=mask&-mask;second=mask^first
            pairs.add((first.bit_length()-1,second.bit_length()-1))
        elif degree>2:raise ValueError('not quadratic')
    return int(0 in terms),linear,pairs


def walsh_from_parts(parts,t,z):
    constant,linear,pairs=parts
    remaining=linear^z;indices=set()
    while remaining:
        first=remaining&-remaining
        indices.add(first.bit_length()-1);remaining ^= first
    return quadratic_sum(constant,indices,pairs,t)


def cubic_branches(result):
    """Enumerate only the affine Walsh support; no zero-weight candidates."""
    base=result['base'];k=result['k'];r=result['correction']['rank']
    t=k*r;m=base['field_variables'];origin,basis=result['support']
    parts=quadratic_parts(result['selector'])
    for selection in range(1 << len(basis)):
        z=origin^cc.action(basis,selection)
        w=walsh_from_parts(parts,t,z)
        if not w:raise AssertionError('constructed Walsh support contains zero')
        phase=dict(base['phase'])
        for v in range(k):
            for i,ell in enumerate(result['ell']):
                if z >> (v*r+i)&1:
                    for a,c in enumerate(ell):
                        e=[0]*m;e[3*v+a]=1;ff.add_term(phase,tuple(e),c)
        aspoly={e+(0,):c for e,c in phase.items()}
        ff.add_term(aspoly,(0,)*m+(1,),1)
        ff.add_term(aspoly,(0,)*m+(2,),1)
        yield z,w,dict(base,phase=phase,artin_schreier=aspoly,degree=max(map(sum,aspoly)))


def combine_counts(result,weighted_counts):
    mass=result['field'].q**result['base']['field_variables']
    signed=rc.exact_divide(sum(w*(count-mass) for w,count in weighted_counts),
                           1 << result['selector_bits'])
    return rc.probability_from_signed(result,signed),signed
