"""S173/R05-28: source-discovered controls on both displacement copies."""
from fractions import Fraction
import shared_control_anchors as sc
from shared_control_anchors import od,cc,qr,pd,ds,echelon,solve,lf,require,draw,reduced_basis


def displacement_rows(U,S):
    return tuple(sum(((u&v).bit_count()%2) << j for j,v in enumerate(S)) for u in U)


def candidate_data(U,source,pencil):
    n=source['qubits'];r=source['rank']
    if len(echelon(U))!=len(U):return None
    K=tuple(cc.nullspace(U,n));rows=reduced_basis(displacement_rows(U,source['directions']))
    W=tuple(cc.nullspace(rows,r));span=echelon(U)
    for word in W:
        A=[0]*n
        for j in pd.bits(word):A=[a^b for a,b in zip(A,pencil[j])]
        for v in K:
            if solve(span,cc.action(A,v)) is None:return None
    return dict(x_kernel=K,displacement_controls=rows,displacement_kernel=W)


def control_phase(source,U,data):
    n=source['qubits'];r=source['rank'];q=len(U)
    rows=data['displacement_controls'];k=len(rows)
    right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],n)[0] for j in range(q))
    zright=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(rows)],r)[0] for j in range(k))
    columns=right+tuple(v << n for v in zright)+data['x_kernel']+tuple(v << n for v in data['displacement_kernel'])
    require(len(columns)==n+r and len(echelon(columns))==n+r,'invalid_two_copy_coordinate_frame')
    phase=pd.substitute_boolean(source['joint'],qr.affine_forms(0,columns,n+r))
    mask=(1 << (q+k))-1
    require(all(t&mask for t in phase if t.bit_count()==3),'nonquadratic_two_copy_control_fiber')
    return dict(controls=tuple(U),columns=columns,phase=phase,control_count=q+k,
                x_control_count=q,displacement_control_count=k,gaussian_sums=1 << (q+k),
                gaussian_width=n+r-q-k,normalizer_exponent=source['normalizer_exponent'],**data)


def discover(source,control_cap,failure_bits,coins,max_candidates=None):
    n=source['qubits'];r=source['rank']
    pencil=tuple(sc.packed_matrix(v,n) for v in source['contraction_images'])
    stats=dict(random_bits=0,random_calls=0,random_trials=0,trial_bound=(1 << (2*control_cap))*(failure_bits+1),
               rank_tests=0,anchor_attempts=0,candidates=0,skipped_high_rank=0,zero_anchors=0,
               highest_sample_rank=0,accepted_anchor_rank=0)
    common=dict(source=source,pencil=pencil,control_cap=control_cap,failure_bits=failure_bits,
                complete_candidate_budget=max_candidates is None,stats=stats)
    def refusal(reason):return dict(common,accepted=False,reason=reason)
    def success(U,data,reason,**extra):
        return dict(common,**control_phase(source,U,data),accepted=True,reason=reason,**extra)
    empty=candidate_data((),source,pencil)
    if empty is not None:return success((),empty,'zero_two_copy_controls')
    if control_cap==0:return refusal('zero_control_cap_refused')
    def rank_of(A):
        rank=len(echelon(A));stats['rank_tests']+=1
        stats['highest_sample_rank']=max(stats['highest_sample_rank'],rank)
        return rank
    def inspect(A,rank,word):
        if not rank:stats['zero_anchors']+=1;return None
        if rank>2*control_cap:stats['skipped_high_rank']+=1;return None
        stats['anchor_attempts']+=1;image=reduced_basis(A);d=len(image)
        for q in range(1,min(control_cap,d)+1):
            for basis in sc.subspaces(d,q):
                if max_candidates is not None and stats['candidates']>=max_candidates:
                    return refusal('candidate_budget_refused')
                stats['candidates']+=1
                U=tuple(cc.action(image,v) for v in basis);data=candidate_data(U,source,pencil)
                if data is not None:
                    stats['accepted_anchor_rank']=rank
                    return success(U,data,'verified_two_copy_anchor',anchor=A,anchor_direction_word=word)
        return None
    # Only this polynomial-size deterministic list is stored; random probes stream.
    anchors=[(rank_of(A),j,A) for j,A in enumerate(pencil)]
    anchors.sort(key=lambda x:-x[0])
    for rank,j,A in anchors:
        answer=inspect(A,rank,1 << j)
        if answer is not None:return answer
    while stats['random_trials']<stats['trial_bound']:
        word=draw(coins,r,stats);stats['random_trials']+=1;A=[0]*n
        for j in pd.bits(word):A=[a^b for a,b in zip(A,pencil[j])]
        A=tuple(A);answer=inspect(A,rank_of(A),word)
        if answer is not None:return answer
    return refusal('no_verified_two_copy_control_within_trials')


def reduce_source(desc,control_cap,failure_bits,coins,max_candidates=None):
    if type(control_cap) is not int or control_cap<0:raise ValueError('nonnegative control cap required')
    if type(failure_bits) is not int or failure_bits<1:raise ValueError('positive failure bits required')
    if max_candidates is not None and (type(max_candidates) is not int or max_candidates<0):
        raise ValueError('nonnegative candidate cap required')
    result=od.reduce_source(desc)
    if result['displacement']['accepted']:
        cert=discover(result['displacement'],control_cap,failure_bits,coins,max_candidates)
    else:
        cert=dict(accepted=False,reason=result['displacement']['reason'],control_cap=control_cap,
                  failure_bits=failure_bits,complete_candidate_budget=max_candidates is None,
                  stats=dict(random_bits=0,random_calls=0))
    result['two_copy_controls']=cert;return result


def reduce_native(n,gates,basis,output,control_cap,failure_bits,coins,max_candidates=None):
    return reduce_source(cc.recognize_native(n,gates,basis,output),control_cap,failure_bits,coins,max_candidates)


fiber=sc.fiber


def evaluate_source(result,bits,max_sums=None,max_terms=None,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    c=result['two_copy_controls']
    if not c['accepted']:
        a=od.evaluate_source(result,bits,max_sums,max_terms,max_work)
        return dict(a,two_copy_refusal=c['reason'],discovery_stats=c['stats'])
    if max_sums is not None:
        if type(max_sums) is not int or max_sums<0:raise ValueError('nonnegative Gaussian cap required')
        if c['gaussian_sums']>max_sums:
            return dict(mode='budget_refused',route='two_copy_controls',probability=None,
                        required_sums=c['gaussian_sums'],discovery_stats=c['stats'])
    total=sum(lf.quadratic_value(fiber(c,a),c['gaussian_width']) for a in range(c['gaussian_sums']))
    E=Fraction(total,1 << c['normalizer_exponent']);p=(1-E)/2
    require(0<=p<=1,'original_acceptance_range')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(mode='exact',route='two_copy_controls',probability=p,estimate=rounded,rounded=rounded,
                error_bound=p-rounded,expectation=E,failure_probability=0,
                x_control_count=c['x_control_count'],displacement_control_count=c['displacement_control_count'],
                gaussian_sums=c['gaussian_sums'],gaussian_width=c['gaussian_width'],
                random_bits=c['stats']['random_bits'],discovery_stats=c['stats'])


def bounded_read(result,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    c=result['two_copy_controls']
    if c['accepted']:return evaluate_source(result,bits,max_sums=1 << (2*c['control_cap']))
    return dict(mode='discovery_miss',route='two_copy_controls',probability=None,estimate=Fraction(1,2),
                error_bound=None,reason=c['reason'],discovery_stats=c['stats'],
                conditional_failure_bound=(Fraction(1,1 << c['failure_bits']) if c['complete_candidate_budget'] else None),
                guarantee_requires='two_copy_controls_and_full_rank_anchor_inside_ker_controls_with_complete_candidate_budget')


def simulate_native(n,gates,basis,output,bits,control_cap,failure_bits,coins):
    return bounded_read(reduce_native(n,gates,basis,output,control_cap,failure_bits,coins),bits)

