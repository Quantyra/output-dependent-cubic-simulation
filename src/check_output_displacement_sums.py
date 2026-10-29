"""Independent source, batching, precision and complexity-boundary checks."""
import ast,hashlib,json,random
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import output_displacement_sums as od
from output_displacement_sums import oc,ac,cc,qr,pd,ds,echelon,solve,lf
import gaussian_relation_transfer as gr
import affine_control_sampling as af
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from check_cubic_centroid_descent import boolean_output_phase
from check_linear_chain_counts import invertible

ROOT=Path(__file__).resolve().parents[1];COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def unbatched(c):
    n=c['qubits'];r=c['rank'];total=0
    for word in range(1 << r):
        forms=[(1 << j,0) for j in range(n)]+[(0,(word >> j)&1) for j in range(r)]
        f=pd.substitute_boolean(c['joint'],forms)
        total+=lf.quadratic_value(f,n);bump('independent_unbatched_gaussian_fibers')
    return Fraction((1 << c['normalizer_exponent'])-total,1 << (c['normalizer_exponent']+1))


def certificate_checks(c,rng):
    n=c['qubits'];r=c['rank'];s=c['active_rank'];desc=c['descriptor'];W=c['walsh']
    for v in c['kernel']:
        direction=cc.action(c['directions'],v)
        f=od.derivative(desc[3][0],direction,n)
        assert all(t.bit_count()<=1 for t in f);bump('exact_cubic_radical_kernel_identities')
    for _ in range(12):
        x=rng.getrandbits(n);z=rng.getrandbits(r)
        d=c['origin']^cc.action(c['directions'],z)
        expected=cc.anf_evaluate(desc[3][0],x)^cc.anf_evaluate(desc[3][0],x^d)^((x >> desc[5])&1)
        expected^=cc.anf_evaluate(W['phase'],z)^((d&((1 << desc[5])^cc.action(desc[2],desc[4]))).bit_count()%2)
        assert cc.anf_evaluate(c['joint'],x|(z << n))==expected
        zprime=cc.action(c['change'],z)
        assert cc.anf_evaluate(c['batched'],x|(z << n))==cc.anf_evaluate(c['joint'],x|(zprime << n))
        a=z&((1 << s)-1);free=x|((z >> s) << n)
        assert cc.anf_evaluate(od.fiber(c,a),free)==cc.anf_evaluate(c['batched'],x|(z << n))
        bump('full_displacement_and_batch_phase_identities')


def random_checks(rng):
    for n in range(2,9):
        for trial in range(8):
            phases=[[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0] for _ in range(2)]
            desc=['cubic-field-v1',n,list(cc.identity(n)),phases,rng.getrandbits(n),0]
            if trial%2:desc=transform_physical(desc,rng)
            result=od.reduce_source(desc);c=result['displacement']
            answer=od.evaluate_source(result,128,max_sums=256)
            assert answer['probability']==fast_independent_probability(desc)==unbatched(c)
            assert c['active_rank']<=c['rank']
            certificate_checks(c,rng);bump('independent_general_two_layer_state_outputs')


def batched_family(g,active=False,flip=False):
    n=4+2*g;first={14,9};last={9}
    for j in range(g):
        a=1 << (4+2*j);b=1 << (5+2*j)
        first^={a|2,b|4};last^={1|a|b}
    if active:first^={16|2|4}
    if flip:last^={1}
    return ['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]


def cubic_count_source(F,d):
    n=2+3*d;first={3};last={3}
    for i in range(d):
        a=1 << (2+d+2*i);b=1 << (3+d+2*i);z=1 << (2+i)
        first^={b|z};last^={1|a|b}
    for term in F:
        if term==0:last^={1};continue
        i=(term&-term).bit_length()-1
        first^={(1 << (2+d+2*i))|((term^(1 << i)) << 2)}
    return ['cubic-field-v1',n,list(cc.identity(n)),[sorted(first),sorted(last)],0,0]


def sat_cubic(n,clauses):
    m=len(clauses);F=set()
    for j,clause in enumerate(clauses):
        literals=[(1 << (abs(v)-1),int(v>0)) for v in clause]
        u=1 << (n+j)
        c0={u}^pd.affine_product(literals[:2])
        c1=pd.affine_product([(u,0),literals[2]])
        for z,c in ((n+m+2*j,c0),(n+m+2*j+1,c1)):
            F^={t|(1 << z) for t in c}
    return F,n+3*m


def sat_count(n,clauses):
    return sum(all(any(((x >> (abs(v)-1))&1)==int(v>0) for v in clause) for clause in clauses)
               for x in range(1 << n))


def counting_checks(rng):
    for d in range(1,5):
        for _ in range(4):
            F={m for m in cc.anf_masks(d,3) if rng.randrange(2)}
            desc=cubic_count_source(F,d)
            expected=Fraction(sum(cc.anf_evaluate(F,x) for x in range(1 << d)),1 << d)
            answer=od.evaluate_source(od.reduce_source(desc),128,max_sums=256)
            assert answer['probability']==expected==fast_independent_probability(desc)
            bump('cubic_count_embedding_state_outputs')
    for n,clauses in ((3,[(1,2,3)]),(3,[(1,2,3),(-1,-2,3)]),
                      (3,[(1,1,1),(-1,-1,-1)])):
        F,d=sat_cubic(n,clauses);count=sat_count(n,clauses)
        gap=sum((-1)**cc.anf_evaluate(F,x) for x in range(1 << d))
        assert gap==(1 << (2*len(clauses)))*count
        result=od.reduce_source(cubic_count_source(F,d))
        expected=(1-Fraction(count,1 << (n+len(clauses))))/2
        answer=od.evaluate_source(result,n+len(clauses)+3,max_sums=1024)
        assert answer['probability']==expected
        recovered=(1-2*answer['rounded'])*(1 << (n+len(clauses)))
        nearest=(2*recovered.numerator+recovered.denominator)//(2*recovered.denominator)
        assert nearest==count;bump('complete_3sat_count_and_precision_transfers')


def variance_checks():
    records=[]
    for g in range(1,8):
        n=2*g+1;f={(1 << 0)|(1 << (2*j+1))|(1 << (2*j+2)) for j in range(g)}
        desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(f),sorted(f)],0,0]
        c=od.discover(desc);assert c['rank']==c['active_rank']==2*g
        E=Fraction(1,2)*(1-Fraction(1,1 << g));p=(1-E)/2
        second=Fraction((1 << (2*g))-1,4);variance=second-E*E
        if g<=4:
            Ys=[]
            for z in range(1 << (2*g)):
                fz=pd.substitute_boolean(c['joint'],[(1 << i,0) for i in range(n)]
                                         +[(0,(z >> j)&1) for j in range(2*g)])
                Y=Fraction(lf.quadratic_value(fz,n),1 << (n-g));Ys.append(Y)
            assert sum(Ys)/len(Ys)==E and sum(y*y for y in Ys)/len(Ys)==second
            assert od.evaluate_source(dict(displacement=c),128)['probability']==p
            bump('exact_uniform_displacement_second_moments')
        if g>=2:assert p<=Fraction(5,16)<Fraction(1,3)
        records.append(dict(g=g,r=2*g,s=2*g,probability=str(p),second_moment=str(second),variance=str(variance)))
    return records


def compression_anchor_checks(rng):
    # Next supported discovery mechanism; no candidate control space is supplied
    # to a production reader yet. These checks test its anchor lemma/density.
    for q in range(1,5):
        n=2*q+3
        for _ in range(8):
            pencil=[]
            for j in range(5):
                A=[0]*n
                for a in range(q):
                    for b in range(a+1,n):
                        bit=int(b==q+a) if j==0 else rng.randrange(2)
                        if bit:A[a]^=1 << b;A[b]^=1 << a
                pencil.append(tuple(A))
            P=invertible(n,rng);Pt=cc.transpose(P)
            pencil=[cc.compose(Pt,cc.compose(A,P)) for A in pencil]
            U=tuple(cc.action(Pt,1 << i) for i in range(q))
            K=cc.nullspace(U,n)
            anchor=pencil[0];assert len(echelon(anchor))==2*q
            assert all(solve(echelon(anchor),u) is not None for u in U)
            assert all(not((x&cc.action(A,y)).bit_count()%2) for A in pencil for x in K for y in K)
            full=0
            for bits in range(1 << len(pencil)):
                A=[0]*n
                for j in pd.bits(bits):A=[x^y for x,y in zip(A,pencil[j])]
                rank=len(echelon(A));assert rank<=2*q;full+=rank==2*q
            assert Fraction(full,1 << len(pencil))>=Fraction(1,1 << q)
            bump('hidden_full_rank_compression_anchors_and_density')


def native_case(desc,expected,rng,label,compare=False):
    native=cc.compile_native(desc)
    with patch.object(oc,'reduce_source',side_effect=AssertionError('retained source reader forbidden')):
        result=od.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    c=result['displacement'];assert c['accepted']
    with patch.object(oc,'evaluate_source',side_effect=AssertionError('retained output reader forbidden')):
        answer=od.evaluate_source(result,128,max_sums=256)
        assert answer['probability']==expected
        for bits in (1,7,257,4096):
            a=od.evaluate_source(result,bits,max_sums=256)
            assert a['probability']==expected and 0<=expected-a['rounded']<Fraction(1,1 << bits)
            assert a['error_bound']==expected-a['rounded'] and a['random_bits']==a['failure_probability']==0
            bump('complete_native_precision_outputs')
    with patch.object(lf,'quadratic_value',side_effect=AssertionError('Gaussian cap must refuse first')):
        a=od.evaluate_source(result,128,max_sums=c['gaussian_sums']-1)
        assert a['mode']=='budget_refused' and a['probability'] is None
        bump('pre_evaluation_branch_budget_refusals')
    certificate_checks(c,rng)
    if c['rank']<=8:assert unbatched(c)==expected;bump('native_unbatched_references')
    if desc[1]<=15:
        assert fast_independent_probability(desc)==expected;bump('independent_native_state_outputs')
        if desc[1]<=8:check_native(native,expected);bump('literal_native_gate_outputs')
    phase,m=qr.original_output_phase(desc);n=desc[1]
    for _ in range(6):
        x=[rng.getrandbits(n) for _ in range(3)]
        assert cc.anf_evaluate(phase,sum(v << (j*n) for j,v in enumerate(x)))==boolean_output_phase(desc,x)
        bump('original_doubled_phase_identities')
    comparison={}
    if compare:
        old=gr.reduce_source(desc,67);oa=gr.evaluate_source(old,128,max_work=4096)
        comparison.update(relation_mode=oa['mode'],relation_cost=old['cost'],
                          relation_stats=[x['stats'] for x in old['relation_transfer']['certificates']])
        if oa['probability'] is not None:assert oa['probability']==expected
        previous=af.reduce_source(desc);a=previous['affine_control']
        comparison['affine_accepted']=a['accepted'];comparison['affine_reason']=a['reason']
        if a['accepted']:
            plan=af.evaluation_plan(previous,7,4,allow_envelope=False)
            comparison['affine_samples_b7_h4']=plan['samples']
            comparison['affine_control_rank']=plan['control_rank']
        bump('unchanged_historical_reader_comparisons')
    record=dict(label=label,n=n,source_bits=native['source_bits'],native_records=len(native['gates']),
                probability=str(expected),r=c['rank'],s=c['active_rank'],
                gaussian_sums=c['gaussian_sums'],unbatched_sums=c['unbatched_sums'],
                gaussian_width=c['gaussian_width'],comparison=comparison)
    print('Original source displacement:',record,flush=True);bump('complete_original_native_outputs')
    return record


def native_checks(rng):
    cases=[];quarter=['cubic-field-v1',4,[1,2,4,8],[[1,2,5,9,6,12,7,11,13,14],[2,4,6,12,7,14]],5,2]
    cases.append((quarter,Fraction(1,4),'cubic_promised_quarter',True))
    complement=cc.normalize_descriptor(quarter);complement[3][1]=sorted(set(complement[3][1])^{4})
    cases.append((complement,Fraction(3,4),'cubic_promised_complement',False))
    affine=['cubic-field-v1',3,[1,2,4],[[7],[3]],0,0]
    cases.append((affine,Fraction(1,4),'rank_zero_affine_origin',False))
    prior=['cubic-field-v1',5,[1,2,4,8,16],[[7,25,14],[7,25]],0,0]
    cases.append((prior,fast_independent_probability(prior),'old_affine_cubic_refusal',True))
    for g,active,hidden,flip in ((2,False,False,False),(3,True,True,True),
                                  (12,False,False,False),(11,True,False,True)):
        desc=batched_family(g,active,flip)
        assert (g+int(not active))%2==1
        expected=Fraction(3 if flip else 1,4)
        if hidden:desc=transform_physical(desc,rng)
        cases.append((desc,expected,'batch_g%d_active%d_hidden%d'%(g,active,hidden),not hidden))
    g=3;n=7;f=[1|(1 << (2*j+1))|(1 << (2*j+2)) for j in range(g)]
    cases.append((['cubic-field-v1',n,list(cc.identity(n)),[f,f],0,0],
                  Fraction(1,4)+Fraction(1,1 << (g+2)),'promised_large_active_rank',True))
    F={7,28,49};d=6
    cases.append((cubic_count_source(F,d),Fraction(sum(cc.anf_evaluate(F,x) for x in range(1 << d)),1 << d),
                  'general_cubic_count_embedding',True))
    records=[native_case(desc,p,rng,label,compare) for desc,p,label,compare in cases]
    longer=['cubic-field-v1',3,[1,2,4],[[7],[7],[7]],0,0]
    r=od.reduce_source(longer,rank_cap=0,state_cap=1)
    assert r['displacement']==dict(accepted=False,reason='requires_two_phase_layers')
    ans=od.evaluate_source(r,128,max_sums=0,max_terms=0,max_work=0)
    assert ans['mode']=='budget_refused';bump('longer_word_explicit_fallback_budget_refusal')
    return records


def main():
    rng=random.Random(1730536);random_checks(rng);counting_checks(rng)
    variance=variance_checks();compression_anchor_checks(rng)
    print('Source batching, cubic/SAT transfers, promised variance counterexamples and compression anchors pass',flush=True)
    native=native_checks(rng)
    prior=ROOT/'artifacts/s173-one-sided-regular-cancellation-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/output_displacement_sums.py','src/check_output_displacement_sums.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730536,counts=COUNTS,native_sources=native,
                 uniform_displacement_variance=variance,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='General explicit two-cubic-layer sources have exact displacement readout in 2^s polynomial source/precision cost, with s the cubic-contraction image rank on computed output Walsh support. Kernel fibers are Gaussian-batched. Promised outputs retained; no universal small-s or all-portfolio gain. Cubic/#SAT transfer distinguishes exact precision-bit simulation from BPP language equality. Uniform displacement variance can be exponential on promised sources. Source compression anchors support the next control-search mechanism.')
    target=ROOT/'artifacts/s173-output-displacement-sums-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
