"""S173/R05-29: bounded sector sampling with source-restricted cubic controls."""
from fractions import Fraction
import two_copy_control_anchors as tc
import affine_control_sampling as af
from two_copy_control_anchors import sc,od,cc,qr,pd,ds,echelon,solve,lf,require,draw,reduced_basis


def discover_cubic(poly,width,control_cap,failure_bits,coins,max_candidates=None):
    cubic={m for m in poly if m.bit_count()==3};T=pd.cubic_tensor(cubic,width)
    pencil=tuple(tuple(T[i][j] for i in range(width)) for j in range(width))
    # T[i][j] is the covector in the remaining argument, so these are the
    # coordinate contractions, represented as alternating matrix columns.
    model=dict(qubits=width,rank=width,directions=cc.identity(width))
    stats=dict(random_bits=0,random_calls=0,random_trials=0,
               trial_bound=(1 << (2*control_cap))*(failure_bits+1),
               rank_tests=0,anchor_attempts=0,candidates=0,skipped_high_rank=0,
               zero_anchors=0,linear_kernel_dimension=0,quadratic_kernel_dimension=0,
               wedge_candidates=0)
    common=dict(width=width,cubic=cubic,pencil=pencil,control_cap=control_cap,
                failure_bits=failure_bits,complete_candidate_budget=max_candidates is None,stats=stats)
    def refusal(reason):return dict(common,accepted=False,reason=reason)
    def verify(U):return tc.candidate_data(U,model,pencil)
    def success(U,reason,**extra):
        data=verify(U);require(data is not None,'invalid_restricted_cubic_controls')
        K=data['x_kernel']
        require(all(t.bit_count()<=2 for t in pd.substitute_boolean(cubic,qr.affine_forms(0,K,width))),
                'restricted_cubic_not_removed')
        return dict(common,accepted=True,reason=reason,controls=tuple(U),kernel=K,
                    control_rank=len(U),**extra)
    if not cubic:return success((),'zero_restricted_cubic',deterministic=True)
    if control_cap==0:return refusal('nonzero_restricted_cubic_at_zero_cap')
    linear=lf.linear_wedge_kernel(cubic,width);stats['linear_kernel_dimension']=len(linear)
    if linear:return success((linear[0],),'linear_exterior_control',deterministic=True)
    if control_cap==1:return refusal('empty_linear_exterior_kernel')
    pairs,second=lf.quadratic_wedge_kernel(cubic,width);stats['quadratic_kernel_dimension']=len(second)
    for word in second:
        stats['wedge_candidates']+=1
        U=tuple(ds.image_basis(lf.two_form_matrix(word,pairs,width)))
        if len(U)==2 and verify(U) is not None:
            return success(U,'quadratic_exterior_controls',deterministic=True)
    def rank_of(A):stats['rank_tests']+=1;return len(echelon(A))
    def inspect(A,rank,word):
        if rank==0:stats['zero_anchors']+=1;return None
        if rank>2*control_cap:stats['skipped_high_rank']+=1;return None
        stats['anchor_attempts']+=1;image=reduced_basis(A)
        for q in range(1,min(control_cap,len(image))+1):
            for basis in sc.subspaces(len(image),q):
                if max_candidates is not None and stats['candidates']>=max_candidates:
                    return refusal('candidate_budget_refused')
                stats['candidates']+=1;U=tuple(cc.action(image,v) for v in basis)
                if verify(U) is not None:
                    return success(U,'restricted_cubic_anchor',deterministic=False,
                                   anchor=A,anchor_direction=word)
        return None
    anchors=[(rank_of(A),j,A) for j,A in enumerate(pencil)];anchors.sort(key=lambda x:-x[0])
    for rank,j,A in anchors:
        answer=inspect(A,rank,1 << j)
        if answer is not None:return answer
    while stats['random_trials']<stats['trial_bound']:
        word=draw(coins,width,stats);stats['random_trials']+=1;A=[0]*width
        for j in pd.bits(word):A=[a^b for a,b in zip(A,pencil[j])]
        answer=inspect(tuple(A),rank_of(A),word)
        if answer is not None:return answer
    return refusal('no_restricted_cubic_control_within_trials')


def reduce_source(desc,control_cap,failure_bits,coins,max_candidates=None):
    if type(control_cap) is not int or control_cap<0:raise ValueError('nonnegative control cap required')
    if type(failure_bits) is not int or failure_bits<1:raise ValueError('positive confidence exponent required')
    if max_candidates is not None and (type(max_candidates) is not int or max_candidates<0):
        raise ValueError('nonnegative candidate cap required')
    desc=cc.normalize_descriptor(desc)
    common=dict(descriptor=desc,control_cap=control_cap,failure_bits=failure_bits)
    if len(desc[3])!=2:
        return dict(common,sector_cubic=dict(accepted=False,reason='requires_two_phase_layers',
                    complete_candidate_budget=max_candidates is None,stats=dict(random_bits=0,random_calls=0)))
    source=od.discover(desc);n=source['qubits'];r=source['rank']
    matching=af.matching_controls(desc);C=matching['controls'];c=len(C);S=source['directions']
    require(c+r==n and sc.annihilates(C,S),'sector_displacement_complement')
    require(af.signature(C,source['origin'])==matching['eta'],'displacement_origin_matching_character')
    restricted=pd.substitute_boolean(desc[3][0],qr.affine_forms(0,S,n))
    discovery=discover_cubic(restricted,r,control_cap,failure_bits+1,coins,max_candidates)
    common.update(displacement=source,matching=matching,restricted_phase=restricted,discovery=discovery)
    if not discovery['accepted']:
        return dict(common,sector_cubic=dict(accepted=False,reason=discovery['reason'],
                    complete_candidate_budget=discovery['complete_candidate_budget'],stats=discovery['stats']))
    U=discovery['controls'];k=len(U);K=discovery['kernel']
    Cright=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(C)],n)[0] for j in range(c))
    right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],r)[0] for j in range(k))
    columns=Cright+tuple(cc.action(S,v) for v in right)+tuple(v << n for v in right)
    columns+=tuple(cc.action(S,v) for v in K)+tuple(v << n for v in K)
    require(len(columns)==n+r and len(echelon(columns))==n+r,'invalid_sector_cubic_coordinate_frame')
    phase=pd.substitute_boolean(source['joint'],qr.affine_forms(0,columns,n+r))
    mask=(1 << (c+2*k))-1
    require(all(t&mask for t in phase if t.bit_count()==3),'nonquadratic_sector_control_fiber')
    eta=matching['eta'];pivot=(eta&-eta).bit_length()-1 if eta else None
    cert=dict(accepted=True,reason='source_restricted_cubic_sectors',columns=columns,phase=phase,
              control_count=c+2*k,sector_rank=c,restricted_control_rank=k,gaussians_per_sector=1 << (2*k),
              gaussian_width=2*r-2*k,branch_denominator=1 << (3*r//2),
              random_width=c-int(bool(eta)),orbit_pivot=pivot,
              original_quadratic=all(t.bit_count()<=2 for t in source['joint']),
              stats=discovery['stats'],complete_candidate_budget=discovery['complete_candidate_budget'])
    return dict(common,sector_cubic=cert)


def reduce_native(n,gates,basis,output,control_cap,failure_bits,coins,max_candidates=None):
    return reduce_source(cc.recognize_native(n,gates,basis,output),control_cap,failure_bits,coins,max_candidates)


def branch_sum(result,sector):
    c=result['sector_cubic'];rank=c['sector_rank']
    if type(sector) is not int or not 0<=sector<(1 << rank):raise ValueError('valid sector assignment required')
    value=sum(lf.quadratic_value(sc.fiber(c,sector|(b << rank)),c['gaussian_width'])
              for b in range(c['gaussians_per_sector']))
    require(abs(value)<=c['branch_denominator'],'whole_sector_unit_bound')
    return value


def evaluation_plan(result,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision exponent required')
    c=result['sector_cubic'];h=result['failure_bits']
    if not c['accepted']:
        return dict(mode='discovery_miss',reason=c['reason'],
                    conditional_failure_bound=(Fraction(1,1 << (h+1)) if c['complete_candidate_budget'] else None),
                    guarantee_requires='two_layers_with_shortcut_or_small_restricted_controls_and_full_rank_anchor')
    exact=c['original_quadratic'];N=0 if exact else 2*(h+2)*(1 << (2*bits))
    return dict(mode='exact_gaussian' if exact else 'sector_cubic_sampling',
                bits=bits,failure_bits=h,epsilon=Fraction(1,1 << bits),samples=N,
                random_width=c['random_width'],sample_random_bits=N*c['random_width'],
                discovery_random_bits=c['stats']['random_bits'],
                random_bit_bound=c['stats']['random_bits']+N*c['random_width'],
                gaussian_sum_bound=1 if exact else N*c['gaussians_per_sector'],
                gaussians_per_sector=c['gaussians_per_sector'],branch_denominator=c['branch_denominator'],
                sampling_failure_bound=Fraction(0) if exact else Fraction(1,1 << (h+1)),
                failure_probability=Fraction(0) if exact else Fraction(1,1 << h))


def finish(total,samples,den,bits):
    if samples<1 or abs(total)>samples*den:raise ValueError('valid bounded-sector total required')
    raw=Fraction(samples*den-total,2*samples*den);precision=bits+2
    estimate=Fraction((raw.numerator << precision)//raw.denominator,1 << precision)
    radius=Fraction(3,1 << (bits+2))
    return dict(estimate=estimate,error_bound=radius,
                interval=(max(Fraction(0),estimate-radius),min(Fraction(1),estimate+radius)))


def evaluate_source(result,bits,coins,max_samples=None,max_gaussians=None):
    plan=evaluation_plan(result,bits);c=result['sector_cubic']
    if plan['mode']=='discovery_miss':
        return dict(mode='discovery_miss',estimate=Fraction(1,2),probability=None,error_bound=None,
                    plan=plan,discovery_stats=c['stats'])
    for cap in (max_samples,max_gaussians):
        if cap is not None and (type(cap) is not int or cap<0):raise ValueError('nonnegative evaluation cap required')
    if ((max_samples is not None and plan['samples']>max_samples) or
        (max_gaussians is not None and plan['gaussian_sum_bound']>max_gaussians)):
        return dict(mode='budget_refused',estimate=None,probability=None,plan=plan,
                    stats=dict(random_bits=0,random_calls=0,gaussian_sums=0),discovery_stats=c['stats'])
    stats=dict(random_bits=0,random_calls=0,gaussian_sums=0)
    if plan['mode']=='exact_gaussian':
        source=result['displacement'];n=source['qubits'];r=source['rank']
        total=lf.quadratic_value(source['joint'],n+r);stats['gaussian_sums']=1
        p=(1-Fraction(total,1 << source['normalizer_exponent']))/2
        estimate=Fraction((p.numerator << bits)//p.denominator,1 << bits)
        answer=dict(estimate=estimate,error_bound=p-estimate,probability=p)
    else:
        total=0
        for _ in range(plan['samples']):
            word=af.orbit_representative(c,draw(coins,c['random_width'],stats))
            total+=branch_sum(result,word);stats['gaussian_sums']+=c['gaussians_per_sector']
        answer=dict(finish(total,plan['samples'],c['branch_denominator'],bits),probability=None)
    require(stats['random_bits']==plan['sample_random_bits'],'sample_random_bit_accounting')
    require(stats['gaussian_sums']==plan['gaussian_sum_bound'],'sector_gaussian_accounting')
    return dict(answer,mode=plan['mode'],route='sector_cubic',failure_probability=plan['failure_probability'],
                plan=plan,stats=stats,discovery_stats=c['stats'])


def simulate_native(n,gates,basis,output,bits,control_cap,failure_bits,coins,max_samples=None,max_gaussians=None):
    result=reduce_native(n,gates,basis,output,control_cap,failure_bits,coins)
    return evaluate_source(result,bits,coins,max_samples,max_gaussians)

