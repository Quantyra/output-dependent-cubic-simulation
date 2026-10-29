"""S173/R05-06: discover complete low-dimensional Boolean phase defects.

Tensor imbalance discovers cubic support; a field displacement polynomial handles
quadratic leftovers. The count backend remains an external theorem.
"""
from itertools import combinations
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
import field_defect_subspaces as ds
import rank_one_field_correction as rc
from finite_field_descent import echelon,solve,xor_sum

DISPLACEMENT_TERMS=((4,0),(2,1),(3,2),(1,3),(3,1),(1,2),(2,3),(0,4))
TRANSLATES=(0,1,2,3,4,6,8)


def bits(mask):
    while mask:
        first=mask&-mask
        yield first.bit_length()-1
        mask ^= first


def affine_product(forms):
    terms={0}
    for mask,constant in forms:
        factor={1 << j for j in bits(mask)}
        if constant:factor.add(0)
        following=set()
        for a in terms:
            for b in factor:
                key=a|b
                if key in following:following.remove(key)
                else:following.add(key)
        terms=following
    return terms


def substitute_boolean(poly,forms):
    result=set()
    for mask in poly:
        result ^= affine_product(forms[j] for j in bits(mask))
    return result


def cubic_tensor(phase,n):
    rows=[[0]*n for _ in range(n)]
    for mask in phase:
        if mask.bit_count()!=3:continue
        i,j,k=tuple(bits(mask))
        for a,b,c in ((i,j,k),(j,i,k),(i,k,j),(k,i,j),(j,k,i),(k,j,i)):
            rows[a][b] ^= 1 << c
    return rows


def cubic_imbalance_image(phase,D):
    rows=cubic_tensor(phase,D.n);T=D.generator
    return ds.image_basis(cc.action(rows[j],T[i])^cc.action(rows[i],T[j])
                          for i in range(D.n) for j in range(i+1,D.n))


def packed_anf(phase,rec):
    return xor_sum(1 << rec.positions[m] for m in phase)


def selector_columns(U,rec,exact_degree=None):
    specs=[];columns=[]
    degrees=range(4) if exact_degree is None else (exact_degree,)
    for degree in degrees:
        for indices in combinations(range(len(U)),degree):
            mask=sum(1 << j for j in indices)
            terms=affine_product((U[j],0) for j in indices)
            specs.append(mask);columns.append(packed_anf(terms,rec))
    return specs,columns


def full_fit(phase,rec,U):
    specs,columns=selector_columns(U,rec)
    all_columns=rec.columns+columns
    target=packed_anf(phase,rec)
    coefficients=solve(echelon(all_columns),target)
    if coefficients is None:return None
    assert xor_sum(c for j,c in enumerate(all_columns) if coefficients >> j & 1)==target
    field_poly={}
    for i,(e,j) in enumerate(rec.specs):
        if coefficients >> i & 1:ff.add_term(field_poly,e,1 << j)
    offset=len(rec.columns)
    residual={mask for j,mask in enumerate(specs) if coefficients >> (offset+j)&1}
    return dict(field_poly=field_poly,residual=residual,columns=tuple(U))


def cubic_remainder(phase,rec,U):
    positions=[j for j,(e,_) in enumerate(rec.specs) if e==(1,1,1)]
    _,selectors=selector_columns(U,rec,3)
    columns=[rec.columns[j] for j in positions]+selectors
    cubic_mask=sum(1 << j for j,m in enumerate(rec.masks) if m.bit_count()==3)
    target=packed_anf(phase,rec)
    solution=solve(echelon([c&cubic_mask for c in columns]),target&cubic_mask)
    if solution is None:return None
    remainder=target^xor_sum(c for j,c in enumerate(columns) if solution >> j & 1)
    if remainder&cubic_mask:raise AssertionError('cubic fit left a cubic term')
    return [m for j,m in enumerate(rec.masks) if remainder >> j & 1]


def quadratic_matrix(phase,n):
    matrix=[0]*n
    for mask in phase:
        if mask.bit_count()>2:raise ValueError('quadratic remainder required')
        if mask.bit_count()==2:
            i,j=tuple(bits(mask));matrix[i] ^= 1 << j;matrix[j] ^= 1 << i
    return tuple(matrix)


def scalar_powers(T):
    powers=[cc.identity(len(T))]
    for _ in range(8):powers.append(cc.compose(T,powers[-1]))
    return powers


def displacement(matrix,powers,step=1):
    result=(0,)*len(matrix)
    for i,j in DISPLACEMENT_TERMS:
        result=rc.matrix_add(result,cc.compose(cc.transpose(powers[step*i]),
                                              cc.compose(matrix,powers[step*j])))
    return result


def quadratic_defect_image(matrix,D,rank_limit):
    powers=scalar_powers(D.generator)
    first=displacement(matrix,powers);second=displacement(matrix,powers,2)
    d1,d2=len(echelon(first)),len(echelon(second))
    if d1==d2==0:return (),dict(reason='zero_displacement',rank=0)
    if d1==0 or d1!=d2 or d1%4:
        return None,dict(reason='quadratic_displacement_ranks',ranks=[d1,d2])
    r=d1//4
    if r>rank_limit:return None,dict(reason='quadratic_rank_budget')
    U=ds.intersection(first,second,D.n)
    if len(U)!=r:return None,dict(reason='quadratic_intersection_dimension')
    translated=tuple(v for j in TRANSLATES for v in cc.compose(cc.transpose(powers[j]),U))
    if len(echelon(translated))!=7*r:
        return None,dict(reason='dependent_seven_translates')
    return U,dict(reason='ok',rank=r,displacement_ranks=[d1,d2])


def recover_phase(phase,D,rec,rank_limit):
    pure=rec.reconstruct(phase)
    if pure is not None:
        return dict(field_poly=pure,residual=set(),columns=(),method='compatible',
                    cubic_rank=0,quadratic_rank=0),'ok'
    U3=cubic_imbalance_image(phase,D)
    if len(U3)>rank_limit:return None,'cubic_rank_budget'
    if len(echelon(U3+cc.compose(cc.transpose(D.generator),U3)))!=2*len(U3):
        return None,'dependent_cubic_translate'
    found=full_fit(phase,rec,U3)
    if found is not None:
        found.update(method='cubic_image',cubic_rank=len(U3),quadratic_rank=0)
        return found,'ok'
    remainder=cubic_remainder(phase,rec,U3)
    if remainder is None:return None,'cubic_part_not_reconstructed'
    U2,details=quadratic_defect_image(quadratic_matrix(remainder,D.n),D,rank_limit)
    if U2 is None:return None,details['reason']
    combined=ds.image_basis(U3+U2)
    if len(combined)>rank_limit:return None,'phase_union_rank_budget'
    found=full_fit(phase,rec,combined)
    if found is None:return None,'full_phase_not_reconstructed'
    found.update(method='cubic_and_quadratic_images',cubic_rank=len(U3),
                 quadratic_rank=len(U2),quadratic_details=details)
    return found,'ok'


def construct_output(desc,D,correction,phase_parts,details,rank_limit):
    _,n,J,phases,basis,output=desc
    U=ds.image_basis(tuple(correction['columns'])+tuple(u for p in phase_parts for u in p['columns']))
    if len(U)>rank_limit:return None,'global_rank_budget'
    L=len(phases);k=2*L-1;r=len(U)
    pairing_poly=rc.pairing_polynomial(correction['pairing']) if L>1 else {}
    result=dict(descriptor=desc,structure=D,polynomials=[p['field_poly'] for p in phase_parts],
                pairing_polynomial=pairing_poly,pairing_correction=correction,
                phase_parts=phase_parts,discovery=details)
    base=cc.count_polynomial(result);span=echelon(U)
    shifts=cc.action(cc.inverse(J),1 << output)
    delta=sum(((u&shifts).bit_count()&1) << i for i,u in enumerate(U))
    inclusion=tuple(solve(span,u) for u in correction['columns'])
    H=ds.defect_matrix(inclusion,correction['form'],r)
    residual=ds.selector_quadratic(L,H,delta)
    for i,part in enumerate(phase_parts):
        masks=[solve(span,u) for u in part['columns']]
        assert all(m is not None for m in masks)
        ket=[(m << (i*r),0) for m in masks]
        bra_block=L+i if i<L-1 else L-1
        bra=[(m << (bra_block*r),0 if i<L-1 else (m&delta).bit_count()&1) for m in masks]
        residual ^= substitute_boolean(part['residual'],ket)
        residual ^= substitute_boolean(part['residual'],bra)
    t=k*r
    active=tuple(bits(xor_or(residual)))
    degree=max((m.bit_count() for m in residual),default=0)
    result.update(base=base,field=D.field,k=k,columns=U,residual_rank=r,
                  selector=residual,selector_bits=t,ell=[D.linear_coefficients(u) for u in U],
                  active_bits=active,residual_degree=degree,
                  spectrum_method='quadratic_support' if degree<=2 else 'finite_walsh',
                  rank_budget=rank_limit)
    return result,'ok'


def xor_or(values):
    result=0
    for value in values:result |= value
    return result


def discover_source(desc,rank_limit,h,rng):
    desc=cc.normalize_descriptor(desc)
    _,n,J,phases,basis,output=desc
    if (n%3 or n<3 or type(rank_limit) is not int or not 0<=rank_limit<=n
        or type(h) is not int or h<1):
        return None,dict(reason='invalid_parameters',random_bits=0)
    s=n//3;rejected={};total_trials=0;anchors=0;seen=set()
    for anchor_index,anchor in enumerate(phases):
        if not any(m.bit_count()==3 for m in anchor) or tuple(anchor) in seen:continue
        seen.add(tuple(anchor))
        centroid=cc.centroid(n,anchor)
        if len(centroid)!=s:
            rejected['anchor_centroid_dimension']=rejected.get('anchor_centroid_dimension',0)+1
            continue
        flat=[cc.flatten(t) for t in centroid];span=echelon(flat)
        if solve(span,cc.flatten(cc.identity(n))) is None:continue
        anchors+=1
        for attempt in range(1,3*h+1):
            total_trials+=1;tape=rng.getrandbits(s)
            D=ds.certify_generator(n,centroid,flat,span,tape,attempt)
            reason='not_field_generator'
            if D is not None:
                if len(phases)>1:
                    correction,reason=ds.recover_subspace(D,J,rank_limit)
                else:
                    correction=dict(rank=0,columns=(),form=(),balanced_matrix=None,
                                    pairing=None,method='unused_one_layer')
                if correction is not None:
                    rec=cc.PhaseReconstructor(D);parts=[];combined=tuple(correction['columns'])
                    for phase in phases:
                        part,reason=recover_phase(phase,D,rec,rank_limit)
                        if part is None:break
                        parts.append(part);combined=ds.image_basis(combined+part['columns'])
                        if len(combined)>rank_limit:
                            reason='global_rank_budget';break
                    else:
                        details=dict(reason='ok',anchor_index=anchor_index,anchor_trials=attempt,
                                     centroid_candidates=anchors,total_trials=total_trials,
                                     random_bits=s*total_trials,rejected=dict(rejected),
                                     field_size_guarantee=s>=7*rank_limit+5)
                        result,reason=construct_output(desc,D,correction,parts,details,rank_limit)
                        if result is not None:return result,details
            rejected[reason]=rejected.get(reason,0)+1
    return None,dict(reason='bounded_phase_discovery_failure',centroid_candidates=anchors,
                     total_trials=total_trials,random_bits=s*total_trials,rejected=rejected,
                     field_size_guarantee=s>=7*rank_limit+5)


def reduce_native(n,gates,basis,output,rank_limit,h,rng):
    return discover_source(cc.recognize_native(n,gates,basis,output),rank_limit,h,rng)


def spectrum(result):
    t=result['selector_bits'];terms=result['selector']
    if result['residual_degree']<=2:
        origin,basis=ds.walsh_support(terms,t);parts=ds.quadratic_parts(terms)
        for selection in range(1 << len(basis)):
            z=origin^cc.action(basis,selection)
            w=ds.walsh_from_parts(parts,t,z)
            if not w:raise AssertionError('invalid quadratic support')
            yield z,w
        return
    active=result['active_bits'];a=len(active);positions={j:i for i,j in enumerate(active)}
    values=bytearray(1 << a)
    for mask in terms:
        compact=sum(1 << positions[j] for j in bits(mask))
        values[compact] ^= 1
    step=1
    while step<len(values):
        for start in range(0,len(values),2*step):
            for j in range(start,start+step):values[j+step] ^= values[j]
        step*=2
    weights=[-1 if b else 1 for b in values]
    del values
    step=1
    while step<len(weights):
        for start in range(0,len(weights),2*step):
            for j in range(start,start+step):
                x,y=weights[j],weights[j+step];weights[j],weights[j+step]=x+y,x-y
        step*=2
    scale=1 << (t-a)
    for compact,w in enumerate(weights):
        if w:
            z=sum(1 << active[j] for j in bits(compact))
            yield z,w*scale


def cubic_branches(result):
    base=result['base'];k=result['k'];r=result['residual_rank'];m=base['field_variables']
    for z,w in spectrum(result):
        phase=dict(base['phase'])
        for v in range(k):
            for i,ell in enumerate(result['ell']):
                if z >> (v*r+i)&1:
                    for a,c in enumerate(ell):
                        e=[0]*m;e[3*v+a]=1;ff.add_term(phase,tuple(e),c)
        aspoly={e+(0,):c for e,c in phase.items()}
        ff.add_term(aspoly,(0,)*m+(1,),1);ff.add_term(aspoly,(0,)*m+(2,),1)
        yield z,w,dict(base,phase=phase,artin_schreier=aspoly,degree=max(map(sum,aspoly)))


def combine_counts(result,weighted_counts):
    return ds.combine_counts(result,weighted_counts)
