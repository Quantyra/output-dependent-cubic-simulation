"""Exact invariant spaces, off-diagonal cancellation and native Gaussian sampling."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from unittest.mock import patch
import diagonal_control_sampling as dc
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import gaussian_boundary_factorization as gb
import gaussian_mass_sampling as gs
import gaussian_block_cuts as bc
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_gaussian_message_norms import all_aux_cycle,graph_probability,cluster_reference
from check_gaussian_mass_sampling import NoCoins
from check_gaussian_block_cuts import dense_source
from check_cubic_centroid_controls import transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}
WITNESS_ROWS=(1314,2188,1779,550,3526,1369,3229,2333,3147,3080,2088,711)


def bump(name,n=1):COUNTS[name]=COUNTS.get(name,0)+n


def signature(rows,x):
    return sum(((r&x).bit_count()%2) << j for j,r in enumerate(rows))


def all_aux_graph(k,g,edges):
    desc=dense_source(k,g,edges=[]);w=2*k+1
    desc[3][0]=sorted(set(desc[3][0])^{(1 << (w*a+2*i+1))|(1 << (w*b+2*i+2))
                                  for a,b in edges for i in range(k)})
    return desc


def invariant_checks(rng):
    for n in range(1,7):
        for _ in range(4):
            P=hidden_basis(n,rng) if n>1 else cc.identity(n)
            J=cc.compose(cc.transpose(P),P);f=[m for m in cc.anf_masks(n,3) if rng.getrandbits(1)]
            desc=['cubic-field-v1',n,list(J),[[],f],rng.randrange(1 << n),rng.randrange(n)]
            inv=dc.invariant_controls(desc);span=echelon(inv['controls']);q=inv['phase']
            table=[cc.anf_evaluate(q,x) for x in range(1 << n)]
            for v in range(1 << n):
                expected=all(table[x]==table[x^v] for x in range(1 << n))
                assert (solve(span,cc.action(J,v)) is not None)==expected
                bump('complete_invariant_covector_memberships')
            assert solve(span,1 << desc[5]) is not None
    # A zero polar form is insufficient: a linear derivative can change by one.
    d=['cubic-field-v1',2,[1,2],[[],[3]],0,0]
    inv=dc.invariant_controls(d)
    assert len(inv['radical'])==2 and len(inv['controls'])==1
    assert solve(echelon(inv['controls']),2) is None
    bump('constant_derivative_guard')


def fiber_checks(rng):
    accepted=refused=0
    for n in (2,3,4):
        for _ in range(4):
            P=hidden_basis(n,rng);J=cc.compose(cc.transpose(P),P)
            phases=[[m for m in cc.anf_masks(n,3) if rng.randrange(3)==0] for _ in range(2)]
            desc=['cubic-field-v1',n,list(J),phases,rng.randrange(1 << n),rng.randrange(n)]
            phase,m=qr.original_output_phase(desc);certificate=dc.discover(desc,phase)
            inv=dc.invariant_controls(desc);controls=inv['controls'];q=len(controls);blocks={}
            for x in range(1 << n):
                for z in range(1 << n):
                    a=signature(controls,x);b=signature(controls,z)
                    value=sum((-1)**cc.anf_evaluate(phase,x|(y << n)|(z << (2*n))) for y in range(1 << n))
                    if a!=b:
                        assert value==0;bump('off_diagonal_point_pair_cancellations')
                    blocks[a,b]=blocks.get((a,b),0)+value
            if certificate['accepted']:
                accepted+=1
                for word in range(1 << q):
                    value=dc.branch_sum(certificate,word)
                    assert value==blocks.get((word,word),0)
                    assert abs(value)<=certificate['branch_denominator']
                    bump('independent_conditional_gaussian_sums')
                probability=Fraction((1 << (2*n))-sum(blocks.values()),1 << (2*n+1))
                assert probability==fast_independent_probability(desc)
                bump('small_independent_state_outputs')
            else:
                refused+=1
                assert (certificate['witness'] >> q).bit_count()==3
    # Conditioning arbitrary cubic-removing controls is wrong without invariance.
    desc=['cubic-field-v1',3,[1,2,4],[[7,0,2,4,5],[7,1,4,5,6]],7,2]
    phase,m=qr.original_output_phase(desc);bad=dc.shared_control_joint(desc,(1,),phase)
    assert all((term >> 1).bit_count()<=2 for term in bad['phase'])
    summed=sum(lf.quadratic_value(cb.restricted_quadratic(bad,t),7) for t in (0,1))
    diagonal=Fraction(64-summed,128);actual=fast_independent_probability(desc)
    assert diagonal==Fraction(5,8) and actual==Fraction(3,8)
    good=dc.reduce_source(desc)['diagonal_control']
    assert good['accepted'] and solve(echelon(good['invariant']['controls']),1) is None
    bump('omitted_invariance_wrong_answer')
    return dict(accepted=accepted,refused=refused,omitted_guard=dict(diagonal=str(diagonal),actual=str(actual)))


def pair_obstruction():
    g=len(WITNESS_ROWS);full=(1 << g)-1
    for size in (1,2):
        for S in combinations(range(g),size):
            outside=full^sum(1 << i for i in S)
            assert len(echelon(WITNESS_ROWS[i]&outside for i in S))==size
            columns=[sum(((WITNESS_ROWS[j] >> i)&1) << j for j in range(g))&outside for i in S]
            assert len(echelon(columns))==size
            bump('full_auxiliary_cut_rank_witnesses')
    edges=[(i,j) for i,row in enumerate(WITNESS_ROWS) for j in range(g) if row >> j&1]
    desc=all_aux_graph(2,g,edges);old=gs.reduce_source(desc)
    pending=[old['tree']];leaves=[]
    while pending:
        v=pending.pop()
        if v['kind']=='controls':leaves.append(v)
        elif v['kind']=='push':pending.append(v['child'])
        elif v['kind']=='product':pending.extend(v['children'])
    assert len(leaves)==1
    source=leaves[0]['source'];C,masks,_=bc.cross_matrix(source)
    assert len(masks)==g
    for pair in combinations(range(g),2):
        norm,phase,rows=cluster_reference(source,pair)
        assert len(rows)==16 and norm['value']==240**2
        bump('exact_pair_norms_without_gain')
    K=Fraction(old['proposal']['root']['mass'],1 << (2*desc[1]))
    assert K==Fraction(15,8)**g
    oldplan=gs.evaluation_plan(old,3,3)
    return desc,edges,dict(rows=list(WITNESS_ROWS),g=g,k=2,old_K=str(K),
                          old_samples=oldplan['samples'],pair_norm=240**2)


def check_native_source(desc,rng,bits=3,h=3,expected=None,label='native'):
    native=cc.compile_native(desc);result=dc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    certificate=result['diagonal_control'];assert certificate['accepted']
    q=certificate['control_rank']
    if desc[1]<=15:
        state=fast_independent_probability(desc)
        if expected is not None:assert state==expected
        expected=state;bump('native_independent_state_references')
        if desc[1]<=12:check_native(native,state);bump('literal_native_references')
    if q<=5:
        total=sum(dc.branch_sum(certificate,t) for t in range(1 << q))
        diagonal=Fraction(certificate['normalizer']-total,2*certificate['normalizer'])
        if expected is not None:assert diagonal==expected
        expected=diagonal;bump('exhaustive_native_control_references')
    with patch.object(gs,'evaluate_source',side_effect=AssertionError('forbidden local mass fallback')),\
         patch.object(cb,'evaluate_controls',side_effect=AssertionError('forbidden exponential joint readout')):
        answer=dc.evaluate_source(result,bits,h,rng,max_samples=1000)
    assert answer['mode']=='diagonal_gaussian' and answer['probability'] is None
    assert answer['stats']['gaussian_sums']==2*(h+1)*(1 << (2*bits))
    assert answer['stats']['random_bits']==answer['stats']['gaussian_sums']*q
    for b,h0 in ((1,1),(bits,h),(180,7),(4096,65)):
        plan=dc.evaluation_plan(result,b,h0)
        assert plan['samples']==2*(h0+1)*(1 << (2*b))
        assert plan['random_bit_bound']==plan['samples']*q
        bump('complete_integer_precision_schedules')
    refused=dc.evaluate_source(result,180,7,NoCoins(),max_samples=0)
    assert refused['mode']=='budget_refused' and not refused['stats']['gaussian_sums']
    bump('bounded_precision_refusals')
    for _ in range(8):
        xs=[rng.getrandbits(desc[1]) for _ in range(3)]
        assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
        bump('original_source_phase_identities')
    record=dict(label=label,n=desc[1],source_bits=native['source_bits'],native_records=len(native['gates']),
                controls=q,free_width=certificate['free_width'],bits=bits,h=h,
                probability=None if expected is None else str(expected),estimate=str(answer['estimate']),
                error_bound=str(answer['error_bound']),failure_probability=str(answer['failure_probability']),
                realized_error=None if expected is None else str(abs(answer['estimate']-expected)),
                realized_covered=None if expected is None else abs(answer['estimate']-expected)<=answer['error_bound'],
                stats=answer['stats'])
    bump('complete_original_native_outputs')
    print('Diagonal-control native output:',record,flush=True)
    return record


def native_checks(rng):
    records=[]
    for k,g,hidden,flip in ((1,4,False,False),(2,3,True,False),(3,4,False,True),(8,3,False,False)):
        desc=all_aux_cycle(k,g)
        expected=graph_probability(k,g,[(j,(j+1)%g) for j in range(g)],all_aux=True)
        if flip:
            desc[3][1]=sorted(set(desc[3][1])^{1 << j for j in pd.bits(desc[2][0])});expected=1-expected
        if hidden:desc=transform_physical(desc,rng)
        records.append(check_native_source(desc,rng,expected=expected,label=f'all_aux_k{k}_g{g}_hidden{hidden}_flip{flip}'))
    # Arbitrary physical quadratic terms include controls and all auxiliary types.
    desc=dense_source(2,3,edges=[])
    desc[3][0]=sorted(set(desc[3][0])^{m for m in cc.anf_masks(desc[1],2) if rng.randrange(4)==0})
    desc[4]=rng.getrandbits(desc[1])
    records.append(check_native_source(desc,rng,label='arbitrary_quadratic_and_nonzero_input'))
    witness,edges,obstruction=pair_obstruction()
    expected=graph_probability(2,12,edges,all_aux=True)
    records.append(check_native_source(witness,rng,expected=expected,label='all_pair_obstruction_graph'))
    # Growing g: only sampled branch Gaussian values, source identities and proven bound.
    desc=all_aux_cycle(2,24)
    records.append(check_native_source(desc,rng,bits=2,h=2,label='growing_24_controls'))
    # Original quadratic sources retain an exact no-coin Gaussian branch.
    desc=['cubic-field-v1',3,[1,2,4],[[3],[7]],0,0];native=cc.compile_native(desc)
    result=dc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    answer=dc.evaluate_source(result,4096,65,NoCoins())
    assert answer['mode']=='exact_gaussian' and answer['probability']==fast_independent_probability(desc)
    assert answer['stats']==dict(gaussian_sums=1,random_bits=0,random_calls=0)
    bump('complete_exact_gaussian_output')
    # Refused mechanisms keep the prior evaluator; neither refusal is a hardness claim.
    desc=['cubic-field-v1',5,[1,2,4,8,16],[[7,25,14],[7,25]],0,0]
    native=cc.compile_native(desc);result=dc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert result['diagonal_control']['reason']=='cubic_survives_invariant_conditioning'
    answer=dc.evaluate_source(result,180,7,NoCoins())
    assert answer['route']=='retained_mass_sampler' and answer['probability']==fast_independent_probability(desc)
    bump('surviving_cubic_fallback_output')
    desc=['cubic-field-v1',3,[1,2,4],[[7],[7],[7]],0,0]
    result=dc.reduce_source(desc);answer=dc.evaluate_source(result,2,2,NoCoins(),max_samples=0)
    assert not result['diagonal_control']['accepted'] and answer['mode']=='budget_refused'
    assert answer['route']=='retained_mass_sampler'
    bump('longer_word_paid_refusal')
    return records,obstruction


def affine_matching_references():
    """Supported next operation; not an integrated matched-sector reader."""
    records=[]
    for first in ([14],[7,14],[7,14,9],[7,14,9,8]):
        desc=['cubic-field-v1',4,[1,2,4,8],[list(first),[7,9]],0,0]
        phase,m=qr.original_output_phase(desc);old=dc.discover(desc,phase)
        invariant=dc.invariant_controls(desc);radical=invariant['radical']
        controls=tuple(cc.action(desc[2],v) for v in radical)
        offset_bits=sum((cc.anf_evaluate(invariant['phase'],v)^int(0 in invariant['phase'])) << j
                        for j,v in enumerate(radical))
        offset=qr.affine_space([(c,(offset_bits >> j)&1) for j,c in enumerate(controls)],4)[0]
        shifted=dc.translate(phase,offset << 8,12)
        joint=dc.shared_control_joint(desc,controls,shifted);q=len(controls)
        assert not old['accepted'] and q==2 and offset_bits==2
        assert all((mask >> q).bit_count()<=2 for mask in joint['phase'])
        sums=[lf.quadratic_value(cb.restricted_quadratic(joint,t),12-2*q) for t in range(1 << q)]
        expected=fast_independent_probability(desc);actual=Fraction(256-sum(sums),512)
        assert actual==expected and all(abs(x)<=64 for x in sums)
        records.append(dict(first_phase=list(first),controls=list(controls),offset_bits=offset_bits,
                            branch_sums=sums,probability=str(actual)))
        bump('next_affine_matching_references')
    return records


def main():
    rng=random.Random(1730527);invariant_checks(rng);small=fiber_checks(rng)
    print('Invariant completeness, off-diagonal cancellations and omitted-guard counterexample pass',flush=True)
    native,obstruction=native_checks(rng);affine=affine_matching_references()
    prior=ROOT/'artifacts/s173-gaussian-mass-sampling-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/diagonal_control_sampling.py','src/check_diagonal_control_sampling.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730527,counts=COUNTS,small_fibers=small,native_sources=native,
                 pair_obstruction=obstruction,next_affine_matching=affine,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-derived maximal invariant controls and bounded global Gaussian branches yield complete two-layer acceptance sampling. Arbitrary quadratic-coupled stars are admitted, including odd cycles and a graph where every pair norm has no gain. General cubic fibers and longer words remain unresolved; seeded outputs are not the confidence proof. No universal or hard-language claim.')
    target=ROOT/'artifacts/s173-diagonal-control-sampling-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
