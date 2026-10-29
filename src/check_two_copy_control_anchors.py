"""S173/R05-28: source, two-copy discovery, promise and full-cost checks."""
import ast,hashlib,json,random
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import two_copy_control_anchors as tc
from two_copy_control_anchors import sc,od,cc,qr,pd,ds,echelon,solve,lf
import affine_control_sampling as af
from check_shared_control_anchors import matrix_family,ConstantCoins
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from check_output_displacement_sums import unbatched

ROOT=Path(__file__).resolve().parents[1];COUNTS={}
def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def coupled_family(q,L,flip=False):
    desc,_=matrix_family(q,L)
    u=1 << (2+q*L);v=1 << (2+q*L+q)
    desc[3][1]=sorted(set(desc[3][1])^{1|u|v}^({1} if flip else set()))
    E0=(1+Fraction(1,1 << (L//2)))/2
    Ea=Fraction(1,1 << L);Eb=Fraction(1,1 << q);Eab=Fraction(2,1 << (q+L))
    values=[]
    for a,b in ((0,0),(1,0),(0,1),(1,1)):
        total=0
        for U in range(1 << q):
            for V in range(1 << L):
                old=tuple(((U >> i)&1)*V for i in range(q))
                new=tuple((((U^a) >> i)&1)*(V^b) for i in range(q))
                if old!=new:continue
                exponent=sum(((row >> j)&1)*((row >> (j+1))&1) for row in old for j in range(0,L,2))
                total+=(-1)**exponent
        values.append(Fraction(total,1 << (q+L)))
    assert values==[E0,Ea,Eb,Eab];bump('independent_four_character_formula_checks',4)
    E=(E0+Ea+Eb-Eab)/2;p=(1-E)/2
    if q==2:
        expected=Fraction(5,16)-Fraction(1,1 << (L//2+3))-Fraction(1,1 << (L+3))
        assert p==expected<Fraction(5,16)<Fraction(1,3)
        bump('growing_symbolic_promise_controls')
    return desc,1-p if flip else p


def all_displacements(q,L):
    desc,_=matrix_family(q,L);n=desc[1]+((desc[1]-2)%2)
    last={3}|{1|(1 << j)|(1 << (j+1)) for j in range(2,n,2)}
    return ['cubic-field-v1',n,list(cc.identity(n)),[desc[3][0],sorted(last)],0,0]


def sector_extension_checks():
    # New prospective mechanism: compute the entire old bounded sector by four
    # Gaussians after finding one control in T restricted to its free space.
    records=[]
    for q,L,determinant in ((1,2,False),(2,2,False),(4,4,True)):
        desc,p=coupled_family(q,L)
        if determinant:
            last={3,1|(1 << (2+q*L))|(1 << (2+q*L+q))}
            for i in range(0,q,2):
                for j in range(0,L,2):
                    a=2+i*L+j;b=a+1;c=a+L;d=c+1
                    last^={1|(1 << a)|(1 << d),1|(1 << b)|(1 << c)}
            desc[3][1]=sorted(last)
            E=(1+Fraction(1,1 << L)+Fraction(1,1 << q)-Fraction(2,1 << (q+L)))/2
            p=(1-E)/2;assert p<Fraction(1,4)
        n=desc[1];phase,_=qr.original_output_phase(desc);matching=af.matching_controls(desc)
        C=matching['controls'];c=len(C);S=tuple(cc.nullspace(C,n));r=len(S)
        restricted=pd.substitute_boolean(desc[3][0],qr.affine_forms(0,S,n))
        factor=lf.discover_factor(restricted,r);assert factor is not None and factor['control_rank']==1
        U=factor['controls'];k=len(U);K=tuple(cc.nullspace(U,r))
        right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],r)[0] for j in range(k))
        shifted=af.dc.translate(phase,matching['offset'] << (2*n),3*n)
        joint=af.dc.shared_control_joint(desc,C,shifted)
        free=right+tuple(v << (r+n) for v in right)+K+tuple(1 << (r+j) for j in range(n))+tuple(v << (r+n) for v in K)
        columns=tuple(1 << j for j in range(c))+tuple(v << c for v in free)
        assert len(echelon(columns))==joint['n']
        transformed=pd.substitute_boolean(joint['phase'],qr.affine_forms(0,columns,joint['n']))
        assert all(t&((1 << (c+2*k))-1) for t in transformed if t.bit_count()==3)
        cert=dict(phase=transformed,control_count=c+2*k);den=1 << (2*n-c);values=[]
        for sector in range(1 << c):
            value=sum(lf.quadratic_value(tc.fiber(cert,sector|(branch << c)),joint['n']-c-2*k)
                      for branch in range(1 << (2*k)))
            assert abs(value)<=den;values.append(value);bump('prospective_whole_sector_bounds')
        assert all(values[a]==values[a^matching['eta']] for a in range(1 << c))
        assert (1-Fraction(sum(values),(1 << c)*den))/2==p
        if n<=12:assert p==fast_independent_probability(desc);bump('prospective_sector_independent_state_references')
        assert not af.discover(desc,phase)['accepted']
        records.append(dict(q=q,L=L,n=n,determinant=determinant,sector_controls=c,
                            restricted_cubic_controls=k,gaussians_per_sector=1 << (2*k),probability=str(p)))
        bump('prospective_complete_sector_mean_identities')
    return records


def phase_checks(c,rng):
    source=c['source'];n=source['qubits'];r=source['rank'];m=n+r
    q=c['x_control_count'];k=c['displacement_control_count'];Q=c['control_cap']
    U=c['controls'];assert len(echelon(U))==q
    data=tc.candidate_data(U,source,c['pencil']);assert data is not None
    assert len(tc.reduced_basis(tc.displacement_rows(U,source['directions'])))==k<=q
    assert c['control_count']==q+k and c['gaussian_sums']==1 << (q+k)
    for _ in range(12):
        word=rng.getrandbits(m);original=cc.action(c['columns'],word)
        assert cc.anf_evaluate(c['phase'],word)==cc.anf_evaluate(source['joint'],original)
        control=word&((1 << (q+k))-1)
        assert cc.anf_evaluate(tc.fiber(c,control),word >> (q+k))==cc.anf_evaluate(c['phase'],word)
        # Literal third finite difference of the original first phase.
        directions=[cc.action(data['x_kernel'],rng.getrandbits(len(data['x_kernel']))) for j in range(2)]
        z=cc.action(data['displacement_kernel'],rng.getrandbits(len(data['displacement_kernel'])))
        directions.append(cc.action(source['directions'],z));x=rng.getrandbits(n)
        third=sum(cc.anf_evaluate(source['descriptor'][3][0],x^cc.action(directions,a)) for a in range(8))%2
        assert third==0;bump('full_phase_and_literal_third_difference_checks')
    stats=c['stats'];N=(1 << (2*Q))*(c['failure_bits']+1)
    assert stats['trial_bound']==N and stats['random_trials']<=N
    assert stats['random_bits']==r*stats['random_trials']
    assert stats['rank_tests']<=r+N and stats['anchor_attempts']<=r+N
    assert stats['candidates']<=stats['anchor_attempts']*4*(Q+1)*(1 << (Q*Q))
    bump('complete_every_tape_cost_contracts')


def reframe_displacements(source,change):
    n=source['qubits'];r=source['rank']
    assert len(change)==r and len(echelon(change))==r
    forms=[(1 << j,0) for j in range(n)]
    forms.extend((row << n,c) for row,c in qr.affine_forms(0,change,r))
    return dict(source,directions=tuple(cc.action(source['directions'],v) for v in change),
                contraction_images=tuple(cc.action(source['contraction_images'],v) for v in change),
                joint=pd.substitute_boolean(source['joint'],forms))


def boundary_checks(rng):
    desc,p=coupled_family(2,4);source=od.discover(desc);n=desc[1];r=source['rank']
    U=(1 << 10,1 << 11);row=tc.reduced_basis(tc.displacement_rows(U,source['directions']))[0]
    pivot=qr.affine_space([(row,1)],r)[0];kernel=cc.nullspace([row],r)
    change=(pivot,)+tuple(pivot^v for v in kernel);framed=reframe_displacements(source,change)
    coins=ConstantCoins(0);c=tc.discover(framed,2,3,coins)
    assert not c['accepted'] and c['reason']=='no_verified_two_copy_control_within_trials'
    assert c['stats']['skipped_high_rank']==r and c['stats']['zero_anchors']==64
    assert c['stats']['random_trials']==coins.calls==64 and coins.bits==64*r
    result=dict(displacement=framed,two_copy_controls=c)
    with patch.object(od,'evaluate_source',side_effect=AssertionError('no hidden fallback')):
        a=tc.bounded_read(result,128)
        assert a['probability'] is None and a['estimate']==Fraction(1,2) and a['error_bound'] is None
        assert a['conditional_failure_bound']==Fraction(1,8)
    bump('adversarial_full_trial_cap_and_explicit_uncertified_miss')
    good=solve(echelon(framed['directions']),1 << 12);assert good is not None
    c=tc.discover(framed,2,3,ConstantCoins(good));assert c['accepted']
    assert c['stats']['skipped_high_rank']==r and c['stats']['random_trials']==1
    assert tc.bounded_read(dict(displacement=framed,two_copy_controls=c),128)['probability']==p
    phase_checks(c,rng);bump('high_rank_probes_do_not_refute_valid_controls')
    result=tc.reduce_source(desc,2,3,rng,max_candidates=0)
    assert result['two_copy_controls']['reason']=='candidate_budget_refused'
    assert tc.bounded_read(result,128)['conditional_failure_bound'] is None
    bump('truncated_search_has_no_confidence_claim')
    desc,p=coupled_family(1,2);result=tc.reduce_source(desc,0,3,rng)
    assert result['two_copy_controls']['reason']=='zero_control_cap_refused'
    assert tc.bounded_read(result,128)['probability'] is None
    answer=tc.evaluate_source(result,128,max_sums=16)
    assert answer['probability']==p and answer['two_copy_refusal']=='zero_control_cap_refused'
    bump('zero_cap_and_explicit_paid_displacement_fallback')
    for q,L in ((1,2),(2,2),(2,4)):
        desc,p=coupled_family(q,L);source=od.discover(desc);r=source['rank'];n=desc[1]
        U=tuple(1 << (2+q*L+i) for i in range(q))
        rows=tc.displacement_rows(U,source['directions']);k=len(echelon(rows));good=0;inside=0
        for word in range(1 << r):
            if any((row&word).bit_count()%2 for row in rows):continue
            inside+=1;packed=cc.action(source['contraction_images'],word)
            A=sc.packed_matrix(packed,n);rank=len(echelon(A))
            assert rank<=2*q
            if rank==2*q:
                assert all(solve(echelon(A),u) is not None for u in U);good+=1
        assert Fraction(inside,1 << r)==Fraction(1,1 << k)
        assert Fraction(good,inside)>=Fraction(1,1 << q)
        assert Fraction(good,1 << r)>=Fraction(1,1 << (q+k))>=Fraction(1,1 << (2*q))
        bump('exhaustive_conditional_source_anchor_density')
    for n in range(2,7):
        for _ in range(4):
            phases=[[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0] for j in range(2)]
            desc=['cubic-field-v1',n,list(cc.identity(n)),phases,rng.getrandbits(n),0]
            result=tc.reduce_source(desc,2,2,rng);c=result['two_copy_controls']
            if c['accepted']:
                assert tc.bounded_read(result,128)['probability']==fast_independent_probability(desc)
                phase_checks(c,rng);bump('independent_general_source_outputs')
            else:
                assert tc.bounded_read(result,128)['probability'] is None
                bump('explicit_general_source_discovery_misses')


def native_case(desc,p,Q,rng,label,compare=False,expect_old_refusal=False,full_old=False):
    native=cc.compile_native(desc)
    with patch.object(od.oc,'reduce_source',side_effect=AssertionError('retained source reader forbidden')):
        result=tc.reduce_native(desc[1],native['gates'],desc[4],desc[5],Q,5,rng)
    c=result['two_copy_controls'];assert c['accepted'],c['reason']
    with patch.object(od,'evaluate_source',side_effect=AssertionError('retained output reader forbidden')):
        for b in (1,7,257,4096):
            a=tc.bounded_read(result,b)
            assert a['probability']==p and a['failure_probability']==0
            assert a['error_bound']==p-a['rounded'] and 0<=a['error_bound']<Fraction(1,1 << b)
            bump('complete_native_precision_outputs')
    phase_checks(c,rng)
    with patch.object(lf,'quadratic_value',side_effect=AssertionError('cap before evaluation')):
        a=tc.evaluate_source(result,128,max_sums=c['gaussian_sums']-1)
        assert a['mode']=='budget_refused' and a['probability'] is None
        bump('pre_gaussian_budget_refusals')
    if desc[1]<=12:
        assert fast_independent_probability(desc)==p;bump('independent_native_state_outputs')
        if desc[1]<=8:check_native(native,p);bump('literal_native_gate_outputs')
    if result['displacement']['rank']<=6:
        assert unbatched(result['displacement'])==p;bump('independent_displacement_references')
    old=af.discover(desc,qr.original_output_phase(desc)[0])
    old_controls=sc.discover(result['displacement'],Q,3,rng)
    if expect_old_refusal:
        assert not old['accepted'] and old['reason']=='cubic_survives_affine_matching'
        assert not old_controls['accepted'] and old_controls['reason']=='nonzero_cubic_restriction_to_displacements'
        bump('strict_old_admission_barrier_crossings')
    comparison=dict(affine_accepted=old['accepted'],affine_reason=old['reason'],
                    one_copy_reason=old_controls['reason'])
    if compare:
        retained=od.oc.reduce_source(desc,4,67)
        answer=od.oc.evaluate_source(retained,128,max_sums=8193,max_terms=8193,max_work=8193)
        comparison.update(retained_mode=answer['mode'],retained_cost=retained.get('cost'),evaluation_cap=8193)
        if answer['probability'] is not None:assert answer['probability']==p
        if full_old:assert answer['probability']==p;bump('completed_retained_exact_reference')
        bump('unchanged_retained_reader_cost_comparisons')
    record=dict(label=label,n=desc[1],source_bits=native['source_bits'],native_records=len(native['gates']),
                probability=str(p),x_controls=c['x_control_count'],displacement_controls=c['displacement_control_count'],
                gaussian_sums=c['gaussian_sums'],gaussian_width=c['gaussian_width'],stats=c['stats'],
                previous_displacement_sums=result['displacement']['gaussian_sums'],comparison=comparison)
    print('Original source two-copy controls:',record,flush=True);bump('complete_original_native_outputs')
    return record


def main():
    rng=random.Random(1730538);boundary_checks(rng)
    sector_extension=sector_extension_checks()
    print('Two-copy source conditions, bounded randomness and conditional anchor densities pass',flush=True)
    cases=[]
    for q,L,hidden,flip in ((1,2,False,False),(2,2,False,False),(2,4,False,False),
                              (2,4,True,True),(2,6,False,False),(2,10,False,True)):
        desc,p=coupled_family(q,L,flip)
        if hidden:desc=transform_physical(desc,rng)
        cases.append((desc,p,q,'coupled_q%d_L%d_hidden%d_flip%d'%(q,L,hidden,flip),
                      not hidden and q==2,True,q==2 and L==2))
    cases.append((all_displacements(3,4),Fraction(435,1024),3,'all_displacements_q3_L4',False,True,False))
    desc,p=matrix_family(3,4,True)
    cases.append((desc,p,3,'previous_one_copy_matrix_family',False,False,False))
    cases.append((['cubic-field-v1',3,[1,2,4],[[7],[3]],0,0],Fraction(1,4),0,
                  'zero_controls_affine_origin',False,False,False))
    native=[native_case(desc,p,Q,rng,label,compare,refusal,full) for desc,p,Q,label,compare,refusal,full in cases]
    prior=ROOT/'artifacts/s173-shared-control-anchors-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/two_copy_control_anchors.py','src/check_two_copy_control_anchors.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730538,counts=COUNTS,native_sources=native,hashes=hashes,
                 next_sector_extension=sector_extension,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-recovered U with T(S intersect kerU,kerU,kerU)=0 gives at most4^Q Gaussian sums. Uniform source probes and small-image subspaces give every-tape 4^Q(h+1)2^O(Q^2) discovery under a full-rank anchor inside the unknown kernel. High-rank probes are skipped, never global impossibility witnesses. A growing promised q2 family crosses both previous admission barriers; retained exact costs are explicit. No arbitrary-source small-Q/full-anchor or BPP=BQP theorem.')
    target=ROOT/'artifacts/s173-two-copy-control-anchors-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()

