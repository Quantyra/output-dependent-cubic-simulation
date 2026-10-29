"""S173/R05-29: source, coherent-sector, sampling and full-cost checks."""
import ast,hashlib,json,random
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import sector_cubic_sampling as ss
from sector_cubic_sampling import tc,sc,od,af,cc,qr,pd,ds,echelon,solve,lf
from check_shared_control_anchors import matrix_family,ConstantCoins
from check_two_copy_control_anchors import coupled_family,all_displacements
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1];COUNTS={}
def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def determinant_family(t,flip=False,perturb=False):
    assert t>=2 and t%2==0
    r=t*t;n=2+r+2*t;first={3};last={3,1|(1 << (2+r))|(1 << (2+r+t))}
    for i in range(t):
        for j in range(t):first^={(1 << (2+i*t+j))|(1 << (2+r+i))|(1 << (2+r+t+j))}
    for i in range(0,t,2):
        for j in range(0,t,2):
            a=2+i*t+j;b=a+1;c=a+t;d=c+1
            last^={1|(1 << a)|(1 << d),1|(1 << b)|(1 << c)}
    if perturb:
        for j in range(t):
            first^={(1 << (3+r))|(1 << (2+j))|(1 << (2+t+(j+1)%t))}
        first^={(1 << (3+r))|(1 << (3+r+t)),(1 << 2)|(1 << (3+t))}
    if flip:last^={1}
    p=Fraction(1,4)-Fraction(2,1 << (t+2))+Fraction(1,1 << (2*t+1))
    desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]
    if perturb:p=None
    elif flip:p=1-p
    return desc,p


def complete_sector_reference(result):
    c=result['sector_cubic'];values=[ss.branch_sum(result,a) for a in range(1 << c['sector_rank'])]
    p=(1-Fraction(sum(values),(1 << c['sector_rank'])*c['branch_denominator']))/2
    return p,values


def old_sector_reference(result):
    desc=result['descriptor'];n=desc[1];matching=result['matching'];C=matching['controls'];c=len(C)
    phase,_=qr.original_output_phase(desc)
    shifted=af.dc.translate(phase,matching['offset'] << (2*n),3*n)
    joint=af.dc.shared_control_joint(desc,C,shifted)
    S=tuple(cc.nullspace(C,n));r=len(S);D=result['displacement']['directions']
    U=[]
    for u in result['discovery']['controls']:
        physical=qr.affine_space([(v,(u >> j)&1) for j,v in enumerate(D)],n)[0]
        U.append(sum(((physical&v).bit_count()%2) << j for j,v in enumerate(S)))
    k=len(U);K=tuple(cc.nullspace(U,r))
    right=tuple(qr.affine_space([(u,int(i==j)) for i,u in enumerate(U)],r)[0] for j in range(k))
    free=right+tuple(v << (r+n) for v in right)+K+tuple(1 << (r+j) for j in range(n))+tuple(v << (r+n) for v in K)
    columns=tuple(1 << j for j in range(c))+tuple(v << c for v in free)
    transformed=pd.substitute_boolean(joint['phase'],qr.affine_forms(0,columns,joint['n']))
    cert=dict(phase=transformed,control_count=c+2*k)
    multiplier=1 << (n-r//2);values=[]
    for sector in range(1 << c):
        value=sum(lf.quadratic_value(sc.fiber(cert,sector|(branch << c)),joint['n']-c-2*k)
                  for branch in range(1 << (2*k)))
        current=ss.branch_sum(result,sector)
        assert value==multiplier*current
        assert abs(current)<=result['sector_cubic']['branch_denominator']
        values.append(current);bump('old_full_phase_and_reduced_sector_normalization')
    assert all(values[a]==values[a^matching['eta']] for a in range(1 << c))
    p=(1-Fraction(sum(values),(1 << c)*result['sector_cubic']['branch_denominator']))/2
    return p,values


def certificate_checks(result,rng):
    cert=result['sector_cubic'];source=result['displacement'];n=source['qubits'];r=source['rank']
    c=cert['sector_rank'];k=cert['restricted_control_rank'];m=n+r
    assert c+r==n and cert['gaussian_width']==2*r-2*k
    assert cert['branch_denominator']==1 << (3*r//2)
    for _ in range(12):
        point=rng.getrandbits(m);original=cc.action(cert['columns'],point)
        assert cc.anf_evaluate(cert['phase'],point)==cc.anf_evaluate(source['joint'],original)
        a=point&((1 << (c+2*k))-1)
        assert cc.anf_evaluate(sc.fiber(cert,a),point >> (c+2*k))==cc.anf_evaluate(cert['phase'],point)
        bump('complete_source_sector_coordinate_identities')
    discovery=result['discovery'];stats=discovery['stats'];Q=result['control_cap'];h=result['failure_bits']
    assert stats['trial_bound']==(1 << (2*Q))*(h+2)
    assert stats['random_trials']<=stats['trial_bound']
    assert stats['random_bits']==r*stats['random_trials']
    assert stats['rank_tests']<=r+stats['trial_bound']
    assert stats['candidates']<=stats['anchor_attempts']*4*(Q+1)*(1 << (Q*Q))
    bump('complete_discovery_cost_contracts')


def discovery_checks(rng):
    # A genuine matrix cubic with no one/two-control factor, in coordinates
    # whose basis contractions all have rank above the cap.
    width=20;poly={(1 << (4*i+j))|(1 << (12+i))|(1 << (15+j)) for i in range(3) for j in range(4)}
    pivot=1 << 12;change=(pivot,)+tuple(pivot^(1 << j) for j in range(width) if j!=12)
    hidden=pd.substitute_boolean(poly,qr.affine_forms(0,change,width))
    coins=ConstantCoins(0);d=ss.discover_cubic(hidden,width,3,3,coins)
    assert not d['accepted'] and d['reason']=='no_restricted_cubic_control_within_trials'
    assert d['stats']['skipped_high_rank']==width
    assert d['stats']['random_trials']==coins.calls==256 and coins.bits==5120
    assert d['stats']['zero_anchors']==256;bump('restricted_anchor_adversarial_tape_cap')
    good=solve(echelon(change),1 << 15)
    d=ss.discover_cubic(hidden,width,3,3,ConstantCoins(good))
    assert d['accepted'] and d['control_rank']==3 and d['reason']=='restricted_cubic_anchor'
    assert d['stats']['random_trials']==1;bump('restricted_anchor_recovery_after_high_rank_skips')
    d=ss.discover_cubic(poly,width,3,3,rng,max_candidates=0)
    assert not d['accepted'] and d['reason']=='candidate_budget_refused'
    desc=all_displacements(3,4);result=ss.reduce_source(desc,3,2,rng,max_candidates=0)
    with patch.object(ss,'branch_sum',side_effect=AssertionError('no hidden branch access')):
        answer=ss.evaluate_source(result,128,rng)
        assert answer['mode']=='discovery_miss' and answer['probability'] is None
        assert answer['error_bound'] is None and answer['plan']['conditional_failure_bound'] is None
    bump('truncated_source_search_has_no_confidence_claim')
    desc=all_displacements(2,2)
    result=ss.reduce_source(desc,1,2,rng)
    assert result['sector_cubic']['reason']=='empty_linear_exterior_kernel'
    assert ss.evaluate_source(result,128,rng)['mode']=='discovery_miss'
    result=ss.reduce_source(desc,2,2,rng)
    assert result['discovery']['reason']=='quadratic_exterior_controls'
    assert result['discovery']['stats']['random_bits']==0;bump('deterministic_two_control_source_discovery')
    longer=['cubic-field-v1',3,[1,2,4],[[7],[7],[7]],0,0]
    with patch.object(od.oc,'reduce_source',side_effect=AssertionError('unsupported source must not compile fallback')):
        result=ss.reduce_source(longer,1,2,rng)
    assert ss.evaluate_source(result,128,rng)['mode']=='discovery_miss'
    assert result['sector_cubic']['reason']=='requires_two_phase_layers'
    bump('longer_word_bounded_explicit_refusal')
    for n in range(2,8):
        for _ in range(3):
            phases=[[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0] for j in range(2)]
            desc=['cubic-field-v1',n,list(cc.identity(n)),phases,rng.getrandbits(n),0]
            result=ss.reduce_source(desc,2,2,rng)
            assert result['sector_cubic']['accepted']
            p,values=complete_sector_reference(result)
            assert p==fast_independent_probability(desc)
            assert all(abs(v)<=result['sector_cubic']['branch_denominator'] for v in values)
            certificate_checks(result,rng);bump('independent_general_source_complete_sector_means')


def precision_checks(result,p,rng):
    cert=result['sector_cubic']
    for bits in (1,7,257,4096):
        plan=ss.evaluation_plan(result,bits)
        if plan['mode']=='exact_gaussian':
            answer=ss.evaluate_source(result,bits,rng)
            assert answer['probability']==p and 0<=p-answer['estimate']<Fraction(1,1 << bits)
            bump('complete_exact_shortcut_precision_outputs')
            continue
        N=2*(result['failure_bits']+2)*(1 << (2*bits))
        assert plan['samples']==N and plan['gaussian_sum_bound']==N*(1 << (2*cert['restricted_control_rank']))
        assert plan['random_bit_bound']==cert['stats']['random_bits']+N*cert['random_width']
        # This is an integer precision schedule audit, not execution of N draws.
        target=(1-2*p)*N*cert['branch_denominator'];total=target.numerator//target.denominator
        finished=ss.finish(total,N,cert['branch_denominator'],bits)
        assert abs(finished['estimate']-p)<Fraction(1,1 << bits)
        assert finished['error_bound']==Fraction(3,1 << (bits+2))
        with patch.object(ss,'branch_sum',side_effect=AssertionError('cap before Gaussian evaluation')):
            with patch.object(ss,'draw',side_effect=AssertionError('cap before random draws')):
                a=ss.evaluate_source(result,bits,rng,max_samples=N-1)
                assert a['mode']=='budget_refused' and a['estimate'] is None
        bump('integer_precision_schedules_and_pre_draw_caps')


def native_case(desc,expected,Q,rng,label,bits=3,compare=False,old_reference=False):
    native=cc.compile_native(desc);h=3
    with patch.object(od.oc,'reduce_source',side_effect=AssertionError('retained source route forbidden')):
        result=ss.reduce_native(desc[1],native['gates'],desc[4],desc[5],Q,h,rng)
    cert=result['sector_cubic'];assert cert['accepted'],cert['reason']
    table=None
    if old_reference:
        reference,table=old_sector_reference(result)
        if expected is not None:assert reference==expected
        expected=reference;bump('complete_independent_sector_reference_outputs')
    assert expected is not None
    certificate_checks(result,rng)
    if desc[1]<=12:
        assert fast_independent_probability(desc)==expected;bump('independent_native_state_outputs')
        if desc[1]<=8:check_native(native,expected);bump('literal_native_gate_outputs')
    coins=random.Random(1732900+COUNTS.get('complete_original_native_outputs',0))
    clone=random.Random();clone.setstate(coins.getstate())
    answer=ss.evaluate_source(result,bits,coins)
    plan=answer['plan'];assert answer['stats']['random_bits']==plan['sample_random_bits']
    assert answer['stats']['gaussian_sums']==plan['gaussian_sum_bound']
    if table is not None and plan['samples']:
        total=0;pivot=cert['orbit_pivot'];width=cert['random_width']
        for _ in range(plan['samples']):
            word=clone.getrandbits(width) if width else 0
            if pivot is not None:
                low=(1 << pivot)-1;word=(word&low)|((word&~low) << 1)
            total+=table[word]
        raw=(1-Fraction(total,plan['samples']*cert['branch_denominator']))/2
        exact_round=Fraction((raw.numerator << (bits+2))//raw.denominator,1 << (bits+2))
        assert answer['estimate']==exact_round;bump('independent_sample_tape_and_rounding_outputs')
    precision_checks(result,expected,rng)
    previous=af.discover(desc,qr.original_output_phase(desc)[0])
    comparison=dict(old_affine_accepted=previous['accepted'],old_affine_reason=previous['reason'])
    if compare:
        old=od.oc.reduce_source(desc,4,67)
        old_answer=od.oc.evaluate_source(old,128,max_sums=8193,max_terms=8193,max_work=8193)
        comparison.update(retained_mode=old_answer['mode'],retained_cost=old.get('cost'),evaluation_cap=8193)
        if old_answer['probability'] is not None:assert old_answer['probability']==expected
        bump('unchanged_retained_exact_comparisons')
    record=dict(label=label,n=desc[1],source_bits=native['source_bits'],native_records=len(native['gates']),
                probability=str(expected),estimate=str(answer['estimate']),observed_error=str(abs(expected-answer['estimate'])),
                within_reported_radius=abs(expected-answer['estimate'])<=answer['error_bound'],
                r=result['displacement']['rank'],sector_controls=cert['sector_rank'],
                restricted_controls=cert['restricted_control_rank'],method=result['discovery']['reason'],
                discovery_stats=cert['stats'],gaussians_per_sector=cert['gaussians_per_sector'],
                gaussian_width=cert['gaussian_width'],samples=plan['samples'],sampling_stats=answer['stats'],
                bits=bits,failure_bits=h,comparison=comparison)
    print('Original source cubic-sector sampling:',record,flush=True);bump('complete_original_native_outputs')
    return record


def conditional_fourier_checks(rng):
    # Supplied normal forms only: actual-source recovery remains the next task.
    records=[]
    for d,z,e in ((1,2,0),(2,2,1),(2,3,0)):
        n=2*d+e+z
        for trial in range(3):
            g={m for m in cc.anf_masks(d+z,3) if (m >> d).bit_count()<=2 and rng.randrange(2)}
            ell=rng.getrandbits(d);null_ell=rng.getrandbits(e)
            f={(1 << i)|(1 << (d+e+i)) for i in range(d)}^{m << (d+e) for m in g}
            f^={1 << i for i in pd.bits(ell)}^{1 << (d+i) for i in pd.bits(null_ell)}
            walsh=[(-1)**cc.anf_evaluate(f,x) for x in range(1 << n)]
            size=1
            while size<(1 << n):
                for start in range(0,1 << n,2*size):
                    for j in range(size):
                        a=walsh[start+j];b=walsh[start+j+size]
                        walsh[start+j]=a+b;walsh[start+j+size]=a-b
                size*=2
            law=[Fraction(0)]*(1 << n);fibers=[];ranks=set()
            for b in range(1 << d):
                forms=[(0,(b >> j)&1) for j in range(d)]+[(1 << j,0) for j in range(z)]
                gb=pd.substitute_boolean(g,forms);fibers.append(gb)
                coupled=gb^{(1 << j)|(1 << (z+j)) for j in range(z)}
                W=qr.quadratic_pushforward(coupled,tuple(1 << (z+j) for j in range(z)),2*z)
                assert not W['zero'];rho=len(W['columns']);ranks.add(rho)
                assert rho%2==0 and W['exponent']==z-rho//2
                for ub in range(1 << d):
                    for word in range(1 << rho):
                        uz=W['origin']^cc.action(W['columns'],word)
                        v=(b^ell)|(null_ell << d)|(ub << (d+e))|(uz << (2*d+e))
                        law[v]+=Fraction(1,1 << (2*d+rho))
            for v in range(1 << n):
                b=(v&((1 << d)-1))^ell;unull=(v >> d)&((1 << e)-1)
                ub=(v >> (d+e))&((1 << d)-1);uz=v >> (2*d+e)
                value=0
                if unull==null_ell:
                    phase=fibers[b]^{1 << j for j in pd.bits(uz)}
                    value=(1 << (d+e))*((-1)**((ub&b).bit_count()%2))*lf.quadratic_value(phase,z)
                assert value==walsh[v] and law[v]==Fraction(value*value,1 << (2*n))
                bump('conditional_fourier_point_and_law_identities')
            assert sum(law)==1
            phi1=[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0]
            desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(f),phi1],0,0]
            Q=od.derivative(phi1,1,n);mean=Fraction(0)
            for v,mass in enumerate(law):
                a=walsh[v];b=walsh[v^1];den=a*a+b*b
                statistic=Fraction(2*a*b,den)*((-1)**cc.anf_evaluate(Q,v)) if den else Fraction(0)
                assert abs(statistic)<=1;mean+=mass*statistic
            p=(1-mean)/2;assert p==fast_independent_probability(desc)
            records.append(dict(d=d,z=z,nullity=e,n=n,conditional_ranks=sorted(ranks),probability=str(p)))
            bump('conditional_fourier_partner_state_outputs')
    return records


def fourier_lead_family(t):
    """Growing source for testing conditional Fourier access beyond cubic controls."""
    assert t>=2 and t%2==0
    n=2+t*t+4*t;U=2+t*t;V=U+t;A=V+t;B=A+t
    first={3};last={3}
    for i in range(t):
        first^={(1 << (A+i))|(1 << (U+i)),(1 << (B+i))|(1 << (V+i))}
        last^={1|(1 << (U+i))|(1 << (2+i*t)),1|(1 << (V+i))|(1 << (2+i*t))}
        for j in range(t):
            first^={(1 << (2+i*t+j))|(1 << (U+i))|(1 << (V+j))}
    for i in range(0,t,2):
        for j in range(0,t,2):
            a=2+i*t+j;b=a+1;c=a+t;d=c+1
            last^={1|(1 << a)|(1 << d),1|(1 << b)|(1 << c)}
    return ['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]


def fourier_lead_checks(rng):
    records=[]
    for t in (2,4):
        desc=fourier_lead_family(t);n=desc[1];r=t*t;U=2+r;V=U+t;A=V+t;B=A+t
        source=od.discover(desc)
        graph=tuple((1 << (2+i*t+j))^
                    (((1 << (U+(i^1)))|(1 << (V+(i^1)))) if j==1 else 0)
                    for i in range(t) for j in range(t))
        assert source['rank']==r and len(echelon(graph+source['directions']))==r
        restricted=pd.substitute_boolean(desc[3][0],qr.affine_forms(0,graph,n))
        # Build the claimed complete polynomial, including Boolean diagonal terms.
        cubic=set();quadratic=set()
        for i in range(t):
            di=1 << ((i^1)*t+1)
            if i!=1:quadratic^={(1 << (i*t+i))|di}
            for j in range(i+1,t):
                dj=1 << ((j^1)*t+1)
                terms=([1 << (j*t+i)] if j==1 else
                       [1 << (i*t+j)] if i==1 else [1 << (i*t+j),1 << (j*t+i)])
                cubic^={x|di|dj for x in terms}
        assert restricted==cubic^quadratic
        assert all(m.bit_count()==3 for m in cubic)
        # Source-derived cubic radical and its quadratic refinement match the
        # proposed first-stage frame construction, but no general compiler is claimed.
        T=pd.cubic_tensor(desc[3][0],n)
        radical=tuple(cc.nullspace(tuple(v for row in T for v in row),n))
        wanted=tuple([1,2]+[1 << j for j in range(A,n)])
        assert len(radical)==len(wanted) and len(echelon(radical+wanted))==len(wanted)
        if t==4:
            refusal=ss.reduce_source(desc,1,3,rng)
            assert not refusal['sector_cubic']['accepted']
            assert refusal['sector_cubic']['reason']=='empty_linear_exterior_kernel'
            bump('next_family_current_one_control_refusal')
        target=Fraction(1,4)-Fraction(1,1 << (t+2))
        # Average the free u_U,u_V characters exactly, then enumerate only U,V.
        survivors=sum(all(not (((u >> i)&1)&(v&1)) for i in range(t))
                      for u in range(1 << t) for v in range(1 << t))
        assert (1-Fraction(survivors,1 << (2*t)))/2==target
        if t==2:
            assert fast_independent_probability(desc)==target
            walsh=[(-1)**cc.anf_evaluate(desc[3][0],x) for x in range(1 << n)]
            size=1
            while size<(1 << n):
                for start in range(0,1 << n,2*size):
                    for j in range(size):
                        a=walsh[start+j];b=walsh[start+j+size]
                        walsh[start+j]=a+b;walsh[start+j+size]=a-b
                size*=2
            mask=(1 << t)-1;mean=Fraction(0);Q=od.derivative(desc[3][1],1,n);support=0
            for frequency,value in enumerate(walsh):
                u=(frequency >> A)&mask;v=(frequency >> B)&mask
                matrix=sum((((u >> i)&1)*((v >> j)&1)) << (i*t+j)
                           for i in range(t) for j in range(t))
                expected=0
                if ((frequency >> 2)&((1 << r)-1))==matrix:
                    exponent=((frequency&1)*((frequency >> 1)&1)+
                              (((frequency >> U)&mask)&u).bit_count()+
                              (((frequency >> V)&mask)&v).bit_count())%2
                    expected=(-1)**exponent*(1 << (n-2*t-1));support+=1
                assert value==expected
                partner=walsh[frequency^1];den=value*value+partner*partner
                statistic=Fraction(2*value*partner,den)*((-1)**cc.anf_evaluate(Q,frequency)) if den else Fraction(0)
                mean+=Fraction(value*value,1 << (2*n))*statistic
                bump('next_family_full_walsh_point_identities')
            assert support==1 << (4*t+2) and (1-mean)/2==target
            bump('next_family_independent_state_and_partner_output')
        records.append(dict(t=t,n=n,displacement_rank=r,probability=str(target),
                            minimum_control_bound='choose(t-k,2)<=k',
                            source_recovery='pending; supplied Fourier law and source radical checked'))
        bump('next_family_source_graph_and_complete_restriction')
    return records


def main():
    rng=random.Random(1730539);discovery_checks(rng)
    next_fourier=conditional_fourier_checks(random.Random(1730540))
    next_family=fourier_lead_checks(random.Random(1730541))
    print('Restricted cubic discovery, adversarial tapes and general sector means pass',flush=True)
    cases=[]
    for t,hidden,flip,perturb in ((2,False,False,False),(4,False,False,False),(4,True,True,False),
                                    (6,False,False,False),(8,False,True,False),
                                    (2,False,False,True),(4,False,False,True)):
        desc,p=determinant_family(t,flip,perturb)
        if perturb and t==2:desc[4]=5;p=fast_independent_probability(desc)
        if hidden:desc=transform_physical(desc,rng)
        cases.append((desc,p,1,'det_t%d_hidden%d_flip%d_mixed%d'%(t,hidden,flip,perturb),
                      4 if t==2 and not perturb else (2 if hidden or t==8 else 3),
                      not hidden and not perturb and t<=4,t<=4))
    cases.append((all_displacements(2,2),Fraction(21,64),2,'two_restricted_controls',2,False,True))
    cases.append((all_displacements(3,4),Fraction(435,1024),3,'three_restricted_anchor_controls',2,False,True))
    desc,p=matrix_family(3,4,True)
    cases.append((desc,p,0,'old_affine_zero_restricted_cubic',3,False,False))
    cases.append((['cubic-field-v1',3,[1,2,4],[[7],[3]],0,0],Fraction(1,4),0,
                  'exact_affine_origin_shortcut',7,False,True))
    native=[native_case(desc,p,Q,rng,label,b,compare,reference)
            for desc,p,Q,label,b,compare,reference in cases]
    prior=ROOT/'artifacts/s173-two-copy-control-anchors-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/sector_cubic_sampling.py','src/check_sector_cubic_sampling.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730539,counts=COUNTS,native_sources=native,hashes=hashes,
                 next_supplied_conditional_fourier=next_fourier,
                 next_growing_fourier_family=next_family,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-restricted cubic controls give coherent whole-sector Gaussian access to the established bounded statistic. Middle-variable elimination pays the new denominator2^(3r/2). Deterministic exterior shortcuts and capped general anchors are integrated; discovery and sampling failure share an explicit budget. Complete inverse-error cost is polynomial for small restricted controls, bypassing a proved growing global-control requirement on promised sources. High-b checks audit integer schedules and refuse before exponential draws; they are not sampled polynomial-in-b simulation. No universal small restricted rank, arbitrary-depth conversion or BPP=BQP theorem.')
    target=ROOT/'artifacts/s173-sector-cubic-sampling-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()


