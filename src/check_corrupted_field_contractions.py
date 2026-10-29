"""Finite claims checks for source-derived corrupted contraction discovery."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import corrupted_field_contractions as cf
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
import phase_combination_anchors as pa
import field_defect_subspaces as ds
import finite_field_acceptance as ff
import rank_one_field_correction as rc
from finite_field_descent import echelon,solve
from check_phase_combination_anchors import native_source,ZeroTape
from check_field_defect_subspaces import complete_two_layer_counts,span_equal
from check_cubic_centroid_descent import boolean_output_phase,hidden_basis
from check_frobenius_trace_degree import fast_independent_probability
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


class Tape:
    def __init__(self,values):self.values=iter(values);self.bits=0
    def getrandbits(self,k):
        value=next(self.values)
        assert 0<=value<1 << k
        self.bits+=k
        return value


def good_fixture_tape(desc,D,U,rng):
    """Only the checker knows K/U. The reader receives ordinary integer draws."""
    annihilator=cc.nullspace(U,D.n)
    tensor=pd.cubic_tensor(desc[3][0],D.n)
    for _ in range(256):
        vectors=[cc.action(annihilator,rng.getrandbits(len(annihilator))) for _ in range(4)]
        balances=cf.common_balance([cf.contraction(tensor,v) for v in vectors])
        if len(balances)!=D.s:continue
        flat=[cc.flatten(t) for t in balances]
        scalar=solve(echelon(flat),cc.flatten(D.generator))
        if scalar is None:continue
        result,details=cf.discover_source(desc,len(U),1,Tape(vectors+[scalar]))
        assert result is not None,details
        return vectors+[scalar],result,details
    raise AssertionError('fixture has no good four-form tape')


def probability_bounds():
    checked=0
    for R in range(13):
        for s in range(7*R+5,7*R+13):
            q=1 << s
            tau=sum(1 << d for d in range(1,s) if s%d==0)
            beta=(1 << R)*(Fraction(1+q+q*q,q**3)+Fraction(tau,q))
            assert beta<Fraction(1,2)
            # Full generation minus the seven-translate union bound.
            position=Fraction(1,2)-Fraction(8*((1 << (7*R))-1),q)
            assert position>=Fraction(1,4)
            assert (1-beta)*position/(1 << (4*R))>=Fraction(1,1 << (4*R+3))
            checked+=1
    bump('exact_rational_success_bound_cases',checked)
    q=1 << 9
    assert 8*(Fraction(1+q+q*q,q**3)+Fraction(10,q))<Fraction(1,2)
    bump('k_independent_sampling_bound_cases')
    # Actual probabilities on small hidden spaces: count clean vectors and
    # bad fourth coefficients; no asymptotic conclusion inferred from a sample.
    rng=random.Random(1730512);records=[]
    for s in (2,3,4):
        desc,D,U,_=native_source(s,2,rng)
        A=cc.nullspace(U,D.n);clean=[cc.action(A,z) for z in range(1 << len(A))]
        assert len(clean)==(1 << D.n)//8
        tensor=pd.cubic_tensor(desc[3][0],D.n)
        defect=pd.cubic_tensor(sorted(pd.substitute_boolean({7},[(u,0) for u in U])),D.n)
        for v in clean:
            assert all(x==0 for x in cf.contraction(defect,v))
            bump('clean_vector_defect_annihilation')
        # Select at most eight K-independent triples, then count all v4.
        counts=[]
        for _ in range(128):
            triple=rng.sample(clean,3)
            columns=tuple(D.physical(tuple(D.field.mul(a,1 << j) for a in D.coordinates(v)))
                          for v in triple for j in range(s))
            if len(echelon(columns))!=D.n:continue
            inverse=cc.inverse(columns);bad=0;certified=0
            tau=sum(1 << d for d in range(1,s) if s%d==0)
            for v in clean:
                a=cc.action(inverse,v)&(D.field.q-1)
                degree=1;value=D.field.mul(a,a)
                while value!=a:value=D.field.mul(value,value);degree+=1
                bad+=degree<s
                if degree==s:
                    # Check a few full balance spaces, rather than only masks.
                    if certified<3:
                        forms=[cf.contraction(tensor,x) for x in triple+[v]]
                        found=cf.common_balance(forms)
                        assert span_equal([cc.flatten(t) for t in found],
                                          [cc.flatten(t) for t in D.centroid_basis])
                        bump('clean_quadruple_actual_field_identities')
                    certified+=1
            assert Fraction(bad,len(clean))<=Fraction(8*tau,D.field.q)
            counts.append(dict(clean_vectors=len(clean),nongenerating_fourth=bad,
                               qualifying_fourth=certified))
            if len(counts)==8:break
        if s==2:
            assert counts and all(item['qualifying_fourth']==0 for item in counts)
            bump('small_field_clean_sampling_boundary')
        records.append(dict(s=s,rank=3,conditional_counts=counts,
                            scope='finite conditional counts, not a uniform probability estimate'))
    return records


def check_phase_and_output(result,rng):
    desc=result['descriptor'];_,n,J,phases,basis,output=desc
    k=result['k'];r=result['residual_rank'];field_route=result['method']=='four_contractions'
    if field_route:
        D=result['structure'];K=D.field
        for phase,part in zip(phases,result['phase_parts']):
            for x in range(1 << n) if n<=9 else [rng.getrandbits(n) for _ in range(32)]:
                z=sum(((u&x).bit_count()&1) << i for i,u in enumerate(part['columns']))
                value=K.trace(ff.evaluate_mv(K,part['field_poly'],D.coordinates(x)))
                assert value^cc.anf_evaluate(part['residual'],z)==cc.anf_evaluate(phase,x)
                bump('full_original_phase_values')
    else:
        for phase,part in zip(phases,result['phase_parts']):
            for x in range(1 << n):
                z=sum(((u&x).bit_count()&1) << i for i,u in enumerate(result['columns']))
                value=cc.anf_evaluate(part['quadratic'],x)^cc.anf_evaluate(part['residual'],z)
                assert value==cc.anf_evaluate(phase,x)
                bump('full_original_phase_values')
    for _ in range(24):
        xs=[rng.getrandbits(n) for _ in range(k)]
        z=sum(((u&x).bit_count()&1) << (v*r+j)
              for v,x in enumerate(xs) for j,u in enumerate(result['columns']))
        if field_route:
            xx=tuple(a for x in xs for a in D.coordinates(x))
            base=K.trace(ff.evaluate_mv(K,result['base']['phase'],xx))
        else:base=cc.anf_evaluate(result['quadratic'],sum(x << (v*n) for v,x in enumerate(xs)))
        assert boolean_output_phase(desc,xs)==base^cc.anf_evaluate(result['selector'],z)
        bump('complete_output_pointwise_identities')


def check_native(native,probability):
    gates=[('X',j) for j in range(native['qubits']) if native['basis'] >> j & 1]+native['gates']
    state,h,_=sparse_native(gates);p=ZERO
    for x,a in state.items():
        if x >> native['output'] & 1:p=add(p,mul(a,conjugate(a)))
    assert scale(p,Fraction(1,1 << h))==scale(ONE,probability)
    bump('independent_native_output_probabilities')


def field_cases(rng):
    records=[]
    for s,L,kind in ((3,2,'equal_cubics'),(3,3,'no_clean_echo'),(9,2,'equal_cubics')):
        desc,D,U,_=native_source(s,L,rng,'no_clean_echo' if L==3 else 'common')
        if kind=='equal_cubics':
            extra=cc.anf_from_function(D.n,lambda x:D.field.trace(ff.evaluate_mv(
                D.field,{(0,1,1):3},D.coordinates(x))))
            desc[3][1]=sorted(set(desc[3][0])^set(extra)^{1,0})
        assert len(pa.source_tensor_basis(desc[3])['columns'])==1
        old,why=pa.discover_source(desc,3,1,rng)
        assert old is None and why['total_trials']==0,why
        bump('no_clean_span_old_reader_refusals')
        values,_,_=good_fixture_tape(desc,D,U,rng)
        native=cc.compile_native(desc)
        tape=Tape(values)
        result,details=cf.reduce_native(native['qubits'],native['gates'],native['basis'],
                                       native['output'],3,1,tape)
        assert result is not None and result['method']=='four_contractions',details
        assert details['total_trials']==1 and details['random_bits']==tape.bits==4*D.n+D.s
        assert result['discovery']['observed_defect_span_dimension']==1
        if s==9:
            bad=list(desc);bad[3]=[list(p) for p in desc[3]]
            bad[3][1]=sorted(set(desc[3][0])^{1,3,0})
            refused,why=pa.verify_original_source(bad,result['structure'],3,L,{})
            assert refused is None and why.startswith('quadratic_'),why
            bump('unsupported_added_quadratic_refusals')
        check_phase_and_output(result,rng)
        counts=[];p=None;branches=[]
        if L==2:
            branches=list(pd.cubic_branches(result))
            assert all(b['degree']<=3 for _,_,b in branches)
            assert sum(w for _,w,_ in branches)==(-1 if 0 in result['selector'] else 1)*(1 << result['selector_bits'])
        if s==3 and L==2:
            counts=complete_two_layer_counts(dict(result,correction=dict(rank=result['residual_rank'])),branches)
            p,signed=pd.combine_counts(result,counts)
            assert p==fast_independent_probability(desc)
            bump('complete_finite_cubic_counts',len(counts))
            bump('full_field_output_counts')
            for b in (3,192,4096):
                assert 0<=p-rc.round_probability(p,b)<Fraction(1,1 << b)
                bump('precision_cases')
            check_native(native,p)
            altered=list(native['gates'])+[('Z',0)]
            try:cf.reduce_native(native['qubits'],altered,native['basis'],native['output'],3,1,Tape(values))
            except ValueError:bump('modified_native_source_refusals')
            else:raise AssertionError('modified source accepted')
        if L==3:
            for value in (0,1):
                desc[4]=(desc[4]&~(1 << desc[5]))|(value << desc[5])
                other,more=cf.discover_source(desc,3,1,Tape(values))
                assert other is not None
                assert fast_independent_probability(desc)==value
                # For echoes every scalar branch is not individually needed:
                # replay the original source/whole-phase certificate both times.
                check_phase_and_output(other,rng)
                bump('promised_no_clean_echo_discoveries')
        records.append(dict(n=D.n,layers=L,kind=kind,source_bits=native['source_bits'],
                            native_records=len(native['gates']),discovery=details,
                            residual_rank=result['residual_rank'],branches=len(branches),
                            complete_counts=len(counts),probability=str(p) if p is not None else None,
                            tape_scope='scripted clean-vector draws; no K/U supplied to reader'))
        print('Corrupted native source verified:',D.n,L,len(counts),flush=True)
    # A separate unscripted recovery on the actual corrupted tensor.
    random_tape=random.Random(1730511)
    desc,D,U,_=native_source(3,3,random_tape,'no_clean_echo')
    answer,details=cf.discover_source(desc,3,1,random_tape)
    assert answer is not None and details['total_trials']<=details['max_total_trials']
    check_phase_and_output(answer,rng)
    bump('unscripted_corrupted_source_recoveries')
    records.append(dict(n=D.n,layers=3,kind='ordinary_random_tape',discovery=details,
                        scope='finite success, outside uniform field-size guarantee'))
    # Every-tape cap is checked with R=0, avoiding a meaningless costly zero run.
    phase=cc.anf_from_function(D.n,lambda x:D.field.trace(ff.evaluate_mv(
        D.field,{(1,1,1):1},D.coordinates(x))))
    clean=['cubic-field-v1',D.n,list(cc.identity(D.n)),[phase],0,0]
    zero=ZeroTape();answer,details=cf.discover_source(clean,0,2,zero)
    assert answer is None and details['total_trials']==16
    assert zero.bits==details['random_bits']==16*(4*D.n+D.s)
    bump('bounded_zero_tape_failures')
    return records


def small_image_cases(rng):
    records=[]
    for n,L,r,kind in ((4,2,3,'general'),(6,2,3,'general'),(6,3,4,'general'),
                       (5,1,3,'single'),(5,5,0,'quadratic'),(6,3,3,'echo')):
        P=hidden_basis(n,rng);J=cc.compose(cc.transpose(P),P);U=hidden_basis(n,rng)[:r]
        phases=[]
        for _ in range(L):
            q={sum(1 << j for j in ids) for d in range(3) for ids in combinations(range(n),d)
               if rng.getrandbits(1)}
            g={sum(1 << j for j in ids) for ids in combinations(range(r),3)
               if rng.getrandbits(1)}
            if r>=3:g.add(7)
            phases.append(sorted(q^pd.substitute_boolean(g,[(u,0) for u in U])))
        if kind=='echo':phases=[phases[0],[],phases[0]]
        desc=['cubic-field-v1',n,list(J),phases,rng.getrandbits(n),rng.randrange(n)]
        values=(0,1) if kind=='echo' else (None,)
        for value in values:
            if value is not None:desc[4]=(desc[4]&~(1 << desc[5]))|(value << desc[5])
            native=cc.compile_native(desc)
            result,details=cf.reduce_native(n,native['gates'],desc[4],desc[5],r,1,Tape([]))
            assert result is not None and result['method']=='small_cubic_image'
            assert details['random_bits']==0
            check_phase_and_output(result,rng)
            result['descriptor']=list(desc)
            answer=cf.evaluate_small_image(result,192);p=answer['probability']
            assert p==fast_independent_probability(desc)
            if value is not None:assert p==value
            bump('full_small_image_outputs')
            bump('binary_quadratic_branch_sums',answer['branches'])
            for b in (2,192,4096):
                assert 0<=p-rc.round_probability(p,b)<Fraction(1,1 << b)
                bump('precision_cases')
            assert answer['rounded']==rc.round_probability(p,192)
            if n==4 or kind=='echo':check_native(native,p)
            # Exact brute-force Gaussian branches on the single-layer instance.
            if L==1:
                for z,w,gauss in cf.quadratic_branches(result):
                    added=cc.action(result['columns'],z)
                    brute=sum((-1)**(cc.anf_evaluate(result['quadratic'],x)^((added&x).bit_count()&1))
                              for x in range(1 << n))
                    assert brute==gauss
                    bump('independent_binary_gauss_sums')
            records.append(dict(n=n,layers=L,kind=kind,rank_budget=r,
                                recovered_rank=result['residual_rank'],source_bits=native['source_bits'],
                                native_records=len(native['gates']),selector_bits=result['selector_bits'],
                                active_bits=len(result['active_bits']),selector_constant=int(0 in result['selector']),
                                branches=answer['branches'],probability=str(p)))
            print('Small-image full output:',n,L,p,answer['branches'],flush=True)
    return records


def main():
    rng=random.Random(1730513)
    conditional=probability_bounds()
    print('Exact sampling bounds and clean-contraction identities pass',flush=True)
    field=field_cases(rng)
    small=small_image_cases(rng)
    prior=ROOT/'artifacts/s173-phase-combination-anchor-checks.json'
    old=json.loads(prior.read_text())
    paths=['src/corrupted_field_contractions.py','src/check_corrupted_field_contractions.py']+list(old['hashes'])
    hashes={}
    for path in paths:
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730513,counts=COUNTS,conditional_sampling=conditional,
                 field_sources=field,small_image_sources=small,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Corrupted-source discovery and direct small-image evaluator. Scripted and ordinary random tapes distinguished; complete finite field counts only on the n=9 two-layer source. Large sources use full source and pointwise checks, no large count or p-adic backend implementation.')
    target=ROOT/'artifacts/s173-corrupted-field-contraction-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
