"""S173/R05-27: source-discovered shared controls of derivative pencils."""
from fractions import Fraction
from itertools import combinations
import output_displacement_sums as od
from output_displacement_sums import cc,qr,pd,ds,echelon,solve,lf,require
from gaussian_relation_transfer import reduced_basis
from gaussian_mass_sampling import draw


def packed_matrix(value,n):
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)];A=[0]*n
    for b in pd.bits(value):
        i,j=pairs[b];A[i]^=1 << j;A[j]^=1 << i
    return tuple(A)


def subspaces(d,k):
    """Unique binary RREF bases, streamed without ambient-vector enumeration."""
    for pivots in combinations(range(d),k):
        positions=[(i,j) for i,p in enumerate(pivots) for j in range(p+1,d) if j not in pivots]
        for word in range(1 << len(positions)):
            rows=[1 << p for p in pivots]
            for b in pd.bits(word):
                i,j=positions[b];rows[i]^=1 << j
            yield tuple(rows)


def annihilates(U,S):
    return all(not((u&v).bit_count()%2) for u in U for v in S)


def valid_controls(U,pencil,S,n):
    if len(echelon(U))!=len(U) or not annihilates(U,S):return False
    K=cc.nullspace(U,n);span=echelon(U)
    return all(solve(span,cc.action(A,v)) is not None for A in pencil for v in K)


def control_phase(source,U):
    n=source['qubits'];r=source['rank'];q=len(U)
    right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],n)[0] for j in range(q))
    kernel=tuple(cc.nullspace(U,n));columns=right+kernel
    require(len(echelon(columns))==n,'invalid_control_coordinate_frame')
    forms=qr.affine_forms(0,columns,n)+[(1 << (n+j),0) for j in range(r)]
    phase=pd.substitute_boolean(source['joint'],forms);mask=(1 << q)-1
    require(all(t&mask for t in phase if t.bit_count()==3),'nonquadratic_shared_control_fiber')
    return dict(controls=tuple(U),columns=columns,phase=phase,control_count=q,
                gaussian_sums=1 << q,gaussian_width=n+r-q,
                normalizer_exponent=source['normalizer_exponent'])


def discover(source,control_cap,failure_bits,coins,max_candidates=None):
    n=source['qubits'];S=source['directions'];packed=tuple(ds.image_basis(source['contraction_images']))
    pencil=tuple(packed_matrix(v,n) for v in packed);s=len(pencil)
    stats=dict(random_bits=0,random_calls=0,rank_tests=0,random_trials=0,
               trial_bound=(1 << control_cap)*(failure_bits+1),candidates=0,
               forced_dimension=0,anchor_rank=0,anchor_image_dimension=0,
               feasible_image_dimension=0,quotient_dimension=0)
    common=dict(source=source,pencil=pencil,control_cap=control_cap,failure_bits=failure_bits,
                complete_candidate_budget=max_candidates is None,stats=stats)
    def refusal(reason,**extra):return dict(common,accepted=False,reason=reason,**extra)
    def success(U,method,**extra):
        phase=control_phase(source,U)
        return dict(common,**phase,accepted=True,reason=method,**extra)
    forced=reduced_basis(cc.action(A,v) for A in pencil for v in S)
    stats['forced_dimension']=len(forced)
    if not annihilates(forced,S):return refusal('nonzero_cubic_restriction_to_displacements',forced=forced)
    if len(forced)>control_cap:return refusal('forced_control_dimension_exceeds_cap',forced=forced)
    if valid_controls(forced,pencil,S,n):return success(forced,'forced_control_space',forced=forced)
    best=None;best_rank=0;word=0
    for j,A in enumerate(pencil):
        rank=len(echelon(A));stats['rank_tests']+=1
        if rank>2*control_cap:return refusal('rank_witness_exceeds_control_cap',witness=A,witness_rank=rank)
        if rank>best_rank:best,best_rank,word=A,rank,1 << j
        if best_rank==2*control_cap:break
    while stats['random_trials']<stats['trial_bound'] and best_rank<2*control_cap:
        bits=draw(coins,s,stats);A=[0]*n
        for j in pd.bits(bits):A=[a^b for a,b in zip(A,pencil[j])]
        A=tuple(A);rank=len(echelon(A));stats['rank_tests']+=1;stats['random_trials']+=1
        if rank>2*control_cap:return refusal('rank_witness_exceeds_control_cap',witness=A,witness_rank=rank)
        if rank>best_rank:best,best_rank,word=A,rank,bits
    assert best is not None
    image=reduced_basis(best);stats['anchor_rank']=best_rank;stats['anchor_image_dimension']=len(image)
    equations=[sum(((v&w).bit_count()%2) << j for j,v in enumerate(image)) for w in S]
    W=reduced_basis(cc.action(image,a) for a in cc.nullspace(equations,len(image)))
    stats['feasible_image_dimension']=len(W)
    if any(solve(echelon(W),u) is None for u in forced):
        return refusal('anchor_image_missing_forced_controls',forced=forced,anchor=best)
    complement=[];span=list(forced)
    for v in W:
        if solve(echelon(span),v) is None:complement.append(v);span.append(v)
    d=len(complement);stats['quotient_dimension']=d
    for k in range(1,min(control_cap-len(forced),d)+1):
        for basis in subspaces(d,k):
            if max_candidates is not None and stats['candidates']>=max_candidates:
                return refusal('candidate_budget_refused',forced=forced,anchor=best)
            stats['candidates']+=1
            U=forced+tuple(cc.action(complement,v) for v in basis)
            if valid_controls(U,pencil,S,n):
                return success(U,'verified_anchor_control_space',forced=forced,anchor=best,anchor_word=word)
    return refusal('no_verified_control_in_anchor_image',forced=forced,anchor=best,anchor_word=word)


def reduce_source(desc,control_cap,failure_bits,coins,max_candidates=None):
    if type(control_cap) is not int or control_cap<0:raise ValueError('nonnegative control cap required')
    if type(failure_bits) is not int or failure_bits<1:raise ValueError('positive failure bits required')
    if max_candidates is not None and (type(max_candidates) is not int or max_candidates<0):
        raise ValueError('nonnegative candidate cap required')
    result=od.reduce_source(desc)
    if not result['displacement']['accepted']:
        certificate=dict(accepted=False,reason=result['displacement']['reason'],control_cap=control_cap,
                         failure_bits=failure_bits,complete_candidate_budget=max_candidates is None,
                         stats=dict(random_bits=0,random_calls=0))
    else:certificate=discover(result['displacement'],control_cap,failure_bits,coins,max_candidates)
    result['shared_controls']=certificate;return result


def reduce_native(n,gates,basis,output,control_cap,failure_bits,coins,max_candidates=None):
    return reduce_source(cc.recognize_native(n,gates,basis,output),control_cap,failure_bits,coins,max_candidates)


def fiber(certificate,word):
    q=certificate['control_count'];mask=(1 << q)-1
    if type(word) is not int or not 0<=word<(1 << q):raise ValueError('valid shared-control word required')
    phase=set()
    for term in certificate['phase']:
        condition=term&mask
        if condition&word==condition:phase^={term >> q}
    assert all(t.bit_count()<=2 for t in phase)
    return phase


def evaluate_source(result,bits,max_sums=None,max_terms=None,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    c=result['shared_controls']
    if not c['accepted']:
        answer=od.evaluate_source(result,bits,max_sums,max_terms,max_work)
        return dict(answer,shared_control_refusal=c['reason'],discovery_stats=c['stats'])
    if max_sums is not None:
        if type(max_sums) is not int or max_sums<0:raise ValueError('nonnegative Gaussian cap required')
        if c['gaussian_sums']>max_sums:
            return dict(mode='budget_refused',route='shared_controls',probability=None,
                        required_sums=c['gaussian_sums'],discovery_stats=c['stats'])
    total=sum(lf.quadratic_value(fiber(c,a),c['gaussian_width']) for a in range(c['gaussian_sums']))
    E=Fraction(total,1 << c['normalizer_exponent']);p=(1-E)/2
    require(0<=p<=1,'original_acceptance_range')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(mode='exact',route='shared_controls',probability=p,rounded=rounded,estimate=rounded,
                error_bound=p-rounded,expectation=E,random_bits=c['stats']['random_bits'],
                failure_probability=0,control_count=c['control_count'],gaussian_sums=c['gaussian_sums'],
                gaussian_width=c['gaussian_width'],discovery_stats=c['stats'])


def bounded_read(result,bits):
    """No exponential fallback; conditional discovery guarantee is explicit."""
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    c=result['shared_controls']
    if c['accepted']:
        return evaluate_source(result,bits,max_sums=1 << c['control_cap'])
    return dict(mode='discovery_miss',route='shared_controls',probability=None,estimate=Fraction(1,2),
                error_bound=None,reason=c['reason'],discovery_stats=c['stats'],
                conditional_failure_bound=(Fraction(1,1 << c['failure_bits'])
                                           if c['complete_candidate_budget'] else None),
                guarantee_requires='compatible_common_controls_and_full_rank_anchor_with_complete_candidate_budget')


def simulate_native(n,gates,basis,output,bits,control_cap,failure_bits,coins):
    return bounded_read(reduce_native(n,gates,basis,output,control_cap,failure_bits,coins),bits)
