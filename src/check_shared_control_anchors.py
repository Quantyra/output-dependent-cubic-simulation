"""S173/R05-27: independent shared-control discovery and full-cost checks."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from unittest.mock import patch
import shared_control_anchors as sc
from shared_control_anchors import od,cc,qr,pd,ds,echelon,solve,lf
import gaussian_relation_transfer as gr
import affine_control_sampling as af
from check_output_displacement_sums import unbatched
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1];COUNTS={}
def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def matrix_family(q,L,cross=False,flip=False):
    assert L%2==0
    r=q*L;n=2+r+q+L;first={3};last={3};pairs=[]
    for i in range(q):
        for j in range(L):
            first^={(1 << (2+i*L+j))|(1 << (2+r+i))|(1 << (2+r+q+j))}
        pairs.extend((i*L+j,i*L+j+1) for j in range(0,L,2))
    if cross:
        assert q==3 and L>=4
        pairs.remove((0,1));pairs.remove((L,L+1));pairs.extend([(0,L+1),(1,L)])
    for a,b in pairs:last^={1|(1 << (2+a))|(1 << (2+b))}
    if flip:last^={1}
    desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]
    E=Fraction(3,8)*(1+Fraction(1,1 << (L//2-1))) if cross else (1+Fraction(1,1 << (L//2)))/2
    p=(1-E)/2
    # An independent logical sum, used only as a test reference.
    total=0
    for u in range(1 << q):
        for v in range(1 << L):
            outer=sum((((u >> i)&1)*((v >> j)&1)) << (i*L+j) for i in range(q) for j in range(L))
            total+=(-1)**sum(((outer >> a)&1)*((outer >> b)&1) for a,b in pairs)
    assert Fraction(total,1 << (q+L))==E;bump('independent_outer_product_character_sums')
    return desc,1-p if flip else p


def star(g):
    n=1+2*g;f=[1|(1 << (2*j+1))|(1 << (2*j+2)) for j in range(g)]
    return ['cubic-field-v1',n,list(cc.identity(n)),[f,f],0,0],Fraction(1,4)+Fraction(1,1 << (g+2))


def space_checks():
    for d in range(5):
        for k in range(d+1):
            seen=set()
            for basis in sc.subspaces(d,k):
                assert len(echelon(basis))==k
                points=frozenset(cc.action(basis,x) for x in range(1 << k))
                assert points not in seen;seen.add(points)
            count=Fraction(1)
            for j in range(k):count*=Fraction((1 << d)-(1 << j),(1 << k)-(1 << j))
            assert len(seen)==count
            if d<=3:
                brute={frozenset(cc.action(b,x) for x in range(1 << k))
                       for b in combinations(range(1,1 << d),k) if len(echelon(b))==k}
                assert seen==brute
            bump('rref_count_uniqueness_and_small_coverage')
    for q in range(1,4):
        d=2*q
        count=sum(sum(1 for _ in sc.subspaces(d,k)) for k in range(q+1))
        assert count<=4*(q+1)*(1 << (q*q));bump('candidate_count_bounds')


def phase_checks(c,rng):
    source=c['source'];n=source['qubits'];r=source['rank'];q=c['control_count']
    U=c['controls'];S=source['directions'];pencil=c['pencil']
    assert sc.valid_controls(U,pencil,S,n)
    assert all(solve(echelon(U),v) is not None for v in c['forced'])
    for _ in range(16):
        x=rng.getrandbits(n);z=rng.getrandbits(r);old=cc.action(c['columns'],x)
        assert cc.anf_evaluate(c['phase'],x|(z << n))==cc.anf_evaluate(source['joint'],old|(z << n))
        a=x&((1 << q)-1)
        free=(x >> q)|(z << (n-q))
        assert cc.anf_evaluate(sc.fiber(c,a),free)==cc.anf_evaluate(c['phase'],x|(z << n))
        bump('full_source_coordinate_and_conditioning_identities')
    stats=c['stats'];Q=c['control_cap']
    assert stats['random_bits']==stats['random_trials']*len(pencil)
    assert stats['random_trials']<=stats['trial_bound']==(1 << Q)*(c['failure_bits']+1)
    assert stats['candidates']<=4*(Q+1)*(1 << (Q*Q))
    assert stats['rank_tests']<=len(pencil)+stats['trial_bound']
    bump('complete_random_and_candidate_cost_contracts')


class ConstantCoins:
    def __init__(self,value):self.value=value;self.calls=0;self.bits=0
    def getrandbits(self,bits):self.calls+=1;self.bits+=bits;return self.value&((1 << bits)-1)


def forced_quotient_checks(rng):
    # A new mathematical claim for the next iteration, not an integrated reader:
    # restricting to ker(forced) removes exactly those known control dimensions.
    for f in (1,2,5):
        desc,_=matrix_family(2,2);base=desc[1];n=base+3*f
        first=set(desc[3][0]);last=set(desc[3][1]);direction=(1 << 2)|(1 << 5)
        for j in range(f):
            a=1 << (base+3*j);b=1 << (base+3*j+1);u=1 << (base+3*j+2)
            first^={a|b|u};last^={1|a|b};direction^=a
        desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]
        source=od.discover(desc);S=source['directions']
        pencil=[sc.packed_matrix(v,n) for v in ds.image_basis(source['contraction_images'])]
        F=sc.reduced_basis(cc.action(A,v) for A in pencil for v in S)
        assert len(F)==f and sc.annihilates(F,S)
        K=tuple(cc.nullspace(F,n))
        Pt=tuple(sum(((v >> i)&1) << j for j,v in enumerate(K)) for i in range(n));span=echelon(K)
        restricted=[cc.compose(Pt,cc.compose(A,K)) for A in pencil]
        Ssmall=tuple(solve(span,v) for v in S)
        assert all(v is not None for v in Ssmall)
        U=F+(1 << 6,1 << 7);smallU=tuple(cc.action(Pt,u) for u in U[f:])
        assert sc.valid_controls(U,pencil,S,n)
        assert sc.valid_controls(smallU,restricted,Ssmall,n-f)
        T=pd.cubic_tensor(first,n)
        anchor=tuple(sum(((T[i][j]&direction).bit_count()%2) << i for i in range(n)) for j in range(n))
        assert len(echelon(anchor))==2*(f+2)
        assert len(echelon(cc.compose(Pt,cc.compose(anchor,K))))==4
        for _ in range(8):
            extra=tuple(rng.getrandbits(n) for j in range(2))
            reduced=tuple(cc.action(Pt,u) for u in extra)
            if len(echelon(reduced))!=2:continue
            assert sc.valid_controls(F+extra,pencil,S,n)==sc.valid_controls(reduced,restricted,Ssmall,n-f)
            bump('forced_quotient_control_equivalences')
        bump('source_forced_quotient_full_rank_anchors')


def two_copy_control_checks():
    records=[]
    for q,L in ((1,2),(2,2),(3,4)):
        desc,_=matrix_family(q,L);n=desc[1]+((desc[1]-2)%2)
        last={3}|{1|(1 << j)|(1 << (j+1)) for j in range(2,n,2)}
        desc=['cubic-field-v1',n,list(cc.identity(n)),[desc[3][0],sorted(last)],0,0]
        source=od.discover(desc);r=source['rank'];S=source['directions']
        U=tuple(1 << (2+q*L+i) for i in range(q));K=tuple(cc.nullspace(U,n))
        rows=tuple(sum(((u&v).bit_count()%2) << j for j,v in enumerate(S)) for u in U)
        R=sc.reduced_basis(rows);k=len(R)
        right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],n)[0] for j in range(q))
        zright=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(R)],r)[0] for j in range(k))
        zkernel=tuple(cc.nullspace(R,r))
        columns=right+tuple(v << n for v in zright)+K+tuple(v << n for v in zkernel)
        assert len(echelon(columns))==n+r
        phase=pd.substitute_boolean(source['joint'],qr.affine_forms(0,columns,n+r));control=q+k
        assert all(t&((1 << control)-1) for t in phase if t.bit_count()==3)
        certificate=dict(control_count=control,phase=phase)
        total=sum(lf.quadratic_value(sc.fiber(certificate,a),n+r-control) for a in range(1 << control))
        p=(1-Fraction(total,1 << source['normalizer_exponent']))/2
        assert 0<=p<=1
        if n<=12:assert p==fast_independent_probability(desc);bump('two_copy_independent_state_references')
        current=sc.reduce_source(desc,q,3,ConstantCoins(0))['shared_controls']
        assert current['reason']=='nonzero_cubic_restriction_to_displacements'
        old=af.discover(desc,qr.original_output_phase(desc)[0])
        assert not old['accepted'] and old['reason']=='cubic_survives_affine_matching'
        T=pd.cubic_tensor(desc[3][0],n)
        direction=sum(1 << (2+i*L+i) for i in range(q))
        assert solve(echelon(S),direction) is not None and sc.annihilates(U,[direction])
        A=tuple(sum(((T[i][j]&direction).bit_count()%2) << i for i in range(n)) for j in range(n))
        assert len(echelon(A))==2*q and all(solve(echelon(A),u) is not None for u in U)
        records.append(dict(q=q,L=L,n=n,probability=str(p),supplied_control_sums=1 << control))
        bump('supplied_two_copy_source_phase_and_anchor_checks')
    return records


def boundary_checks(rng):
    desc,p=matrix_family(3,4,True)
    coins=ConstantCoins(0);result=sc.reduce_source(desc,3,4,coins);c=result['shared_controls']
    assert not c['accepted'] and c['reason']=='no_verified_control_in_anchor_image'
    assert c['stats']['random_trials']==40 and coins.calls==40 and coins.bits==480
    with patch.object(od,'evaluate_source',side_effect=AssertionError('no exponential fallback')):
        a=sc.bounded_read(result,128)
        assert a['probability'] is None and a['estimate']==Fraction(1,2)
        assert a['conditional_failure_bound']==Fraction(1,16) and a['error_bound'] is None
    bump('bounded_every_tape_miss_without_hidden_fallback')
    result=sc.reduce_source(desc,3,4,random.Random(27),max_candidates=0)
    assert result['shared_controls']['reason']=='candidate_budget_refused'
    assert sc.bounded_read(result,128)['conditional_failure_bound'] is None
    bump('truncated_search_has_no_confidence_claim')
    result=sc.reduce_source(desc,2,4,ConstantCoins((1 << 0)|(1 << 5)|(1 << 10)))
    assert result['shared_controls']['reason']=='rank_witness_exceeds_control_cap'
    assert result['shared_controls']['witness_rank']==6;bump('rank_witness_refutes_small_cap')
    desc,p=star(2);result=sc.reduce_source(desc,0,4,rng)
    assert result['shared_controls']['reason']=='forced_control_dimension_exceeds_cap'
    # Every evaluation on a miss is visibly charged to the retained displacement route.
    a=sc.evaluate_source(result,128,max_sums=16);assert a['probability']==p
    assert a['shared_control_refusal']=='forced_control_dimension_exceeds_cap'
    bump('forced_dimension_refusal_and_paid_exact_fallback')
    bad=['cubic-field-v1',6,list(cc.identity(6)),[[3,4|8|16],[3,1|4|8,1|16|32]],0,0]
    result=sc.reduce_source(bad,6,4,rng)
    assert result['shared_controls']['reason']=='nonzero_cubic_restriction_to_displacements'
    bump('nonannihilating_forced_space_refusal')
    # All alternating forms on three logical coordinates: compatible two-controls
    # exist, but the maximum pencil rank is two, not four. Full-rank promise fails.
    desc=['cubic-field-v1',9,list(cc.identity(9)),
          [[3,4|64|128,8|64|256,16|128|256],[3,1|4|8,1|16|32]],0,0]
    result=sc.reduce_source(desc,2,3,rng);c=result['shared_controls']
    assert c['accepted'] and c['control_count']==2 and c['stats']['anchor_rank']==2
    assert sc.bounded_read(result,128)['probability']==fast_independent_probability(desc)
    phase_checks(c,rng);bump('success_outside_sufficient_full_rank_promise')
    # Confirm the Pfaffian support lower bound on every binary source-pencil choice.
    for q,L in ((1,2),(2,2),(3,4)):
        desc,p=matrix_family(q,L,q==3)
        c=od.discover(desc);pencil=[sc.packed_matrix(v,desc[1]) for v in ds.image_basis(c['contraction_images'])]
        full=0
        for word in range(1 << len(pencil)):
            A=[0]*desc[1]
            for j in pd.bits(word):A=[x^y for x,y in zip(A,pencil[j])]
            rank=len(echelon(A));assert rank<=2*q;full+=rank==2*q
        assert Fraction(full,1 << len(pencil))>=Fraction(1,1 << q)
        bump('exhaustive_source_anchor_density')
    # Random small sources test accepted certificates without assuming a promise.
    for n in range(2,8):
        for _ in range(4):
            phases=[[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0] for j in range(2)]
            desc=['cubic-field-v1',n,list(cc.identity(n)),phases,rng.getrandbits(n),0]
            result=sc.reduce_source(desc,min(n,3),3,rng);c=result['shared_controls']
            if c['accepted']:
                assert sc.bounded_read(result,128)['probability']==fast_independent_probability(desc)
                phase_checks(c,rng);bump('independent_general_source_accepted_outputs')
            else:
                assert sc.bounded_read(result,128)['probability'] is None
                bump('explicit_general_source_misses')


def native_case(desc,p,Q,rng,label,compare=False,full_old=False):
    native=cc.compile_native(desc)
    with patch.object(od.oc,'reduce_source',side_effect=AssertionError('source fallback forbidden')):
        result=sc.reduce_native(desc[1],native['gates'],desc[4],desc[5],Q,6,rng)
    c=result['shared_controls'];assert c['accepted'],c['reason']
    with patch.object(od,'evaluate_source',side_effect=AssertionError('output fallback forbidden')):
        for b in (1,7,257,4096):
            a=sc.bounded_read(result,b)
            assert a['probability']==p and a['failure_probability']==0
            assert a['error_bound']==p-a['rounded'] and 0<=a['error_bound']<Fraction(1,1 << b)
            bump('complete_native_precision_outputs')
    phase_checks(c,rng)
    with patch.object(lf,'quadratic_value',side_effect=AssertionError('cap before evaluation')):
        a=sc.evaluate_source(result,128,max_sums=c['gaussian_sums']-1)
        assert a['mode']=='budget_refused' and a['probability'] is None
        bump('pre_gaussian_budget_refusals')
    if desc[1]<=15:
        assert fast_independent_probability(desc)==p;bump('independent_native_state_outputs')
        if desc[1]<=8:check_native(native,p);bump('literal_native_gate_outputs')
    if result['displacement']['rank']<=6:
        assert unbatched(result['displacement'])==p;bump('independent_displacement_references')
    comparison={}
    if compare:
        old=gr.reduce_source(desc,67);cap=600000 if full_old else 4096
        a=gr.evaluate_source(old,128,max_work=cap)
        comparison.update(relation_cost=old['cost'],relation_mode=a['mode'],evaluation_cap=cap)
        if a['probability'] is not None:assert a['probability']==p
        if full_old:assert a['probability']==p;bump('completed_exponential_reader_references')
        older=od.oc.reduce_source(desc,4,67)
        older_answer=od.oc.evaluate_source(older,128,max_sums=4096,max_terms=4096,max_work=4096)
        comparison['retained_latest_mode']=older_answer['mode']
        comparison['retained_latest_cost']=older.get('cost')
        if older_answer['probability'] is not None:assert older_answer['probability']==p
        sampled=af.reduce_source(desc);cert=sampled['affine_control']
        comparison.update(affine_accepted=cert['accepted'],affine_reason=cert['reason'])
        if cert['accepted']:
            plan=af.evaluation_plan(sampled,7,4,allow_envelope=False)
            comparison['affine_samples_b7_h4']=plan['samples']
            comparison['affine_control_rank']=plan['control_rank']
        bump('unchanged_exact_and_sampling_portfolio_comparisons')
    record=dict(label=label,n=desc[1],source_bits=native['source_bits'],native_records=len(native['gates']),
                probability=str(p),control_count=c['control_count'],method=c['reason'],stats=c['stats'],
                gaussian_sums=c['gaussian_sums'],gaussian_width=c['gaussian_width'],
                previous_displacement_sums=result['displacement']['gaussian_sums'],comparison=comparison)
    print('Original source shared controls:',record,flush=True);bump('complete_original_native_outputs')
    return record


def main():
    rng=random.Random(1730537);space_checks();boundary_checks(rng)
    forced_quotient_checks(random.Random(1730538))
    next_controls=two_copy_control_checks()
    print('RREF, source-anchor density, forced-space boundaries and every-tape checks pass',flush=True)
    cases=[]
    for q,L,hidden,flip in ((1,2,False,False),(2,2,False,False),(3,2,False,False),
                              (3,4,False,False),(3,4,True,False),(3,6,False,False),(3,8,False,True)):
        desc,p=matrix_family(q,L,q==3 and L>=4,flip)
        if hidden:desc=transform_physical(desc,rng)
        cases.append((desc,p,q,'matrix_q%d_L%d_hidden%d_flip%d'%(q,L,hidden,flip),
                      not hidden and L>=4,q==3 and L==4 and not hidden))
    for g,hidden in ((2,False),(12,True)):
        desc,p=star(g)
        if hidden:desc=transform_physical(desc,rng)
        cases.append((desc,p,1,'forced_star_g%d_hidden%d'%(g,hidden),not hidden,False))
    desc=['cubic-field-v1',3,[1,2,4],[[7],[3]],0,0]
    cases.append((desc,Fraction(1,4),0,'zero_linear_displacement_affine_origin',False,False))
    native=[native_case(desc,p,Q,rng,label,compare,full_old) for desc,p,Q,label,compare,full_old in cases]
    prior=ROOT/'artifacts/s173-output-displacement-sums-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/shared_control_anchors.py','src/check_shared_control_anchors.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730537,counts=COUNTS,native_sources=native,hashes=hashes,
                 next_supplied_two_copy_controls=next_controls,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Forced controls or capped random full-rank source anchors recover verified common controls; streamed quotient RREF search costs 2^O(Q^2), readout 2^Q Gaussian sums, with complete source/random/precision costs. Bounded misses have only a source-promise conditional guarantee. Growing promised matrix-tensor sources improve retained exact enumeration, while the old affine sampler already provides polynomial inverse-error evaluation. No universal small controls, arbitrary-depth converter, language equality or exact counting collapse.')
    target=ROOT/'artifacts/s173-shared-control-anchors-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()

