"""Finite tests of new subspace recovery, joint trial bounds and rank-cost transfer."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import product
from pathlib import Path
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
import field_defect_subspaces as ds
import rank_one_field_correction as rc
from finite_field_descent import echelon,solve,xor_sum
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import field,fast_independent_probability,source as prior_source
from check_rank_one_field_correction import table_evaluator,complete_count
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def span_equal(A,B):
    return len(echelon(A))==len(echelon(B))==len(echelon(tuple(A)+tuple(B)))


def build_source(s,r,L,rng,mode='one_coordinate',alternating=False,make_phases=True):
    K=field(s,rng);n=3*s
    P=hidden_basis(n,rng);invP=cc.inverse(P);dualP=cc.transpose(invP)
    def coordinates(x):
        packed=cc.action(invP,x)
        return tuple((packed >> (a*s)) & (K.q-1) for a in range(3))
    G=tuple(sum((int(i//s==j//s)*K.trace(K.mul(1 << (i%s),1 << (j%s)))) << i
                for i in range(n)) for j in range(n))
    J0=cc.compose(dualP,cc.compose(G,invP))
    mul_theta=tuple(K.mul(2,1 << (j%s)) << ((j//s)*s) for j in range(n))
    T=cc.compose(P,cc.compose(mul_theta,invP))
    powers=[cc.identity(n)]
    for _ in range(1,s):powers.append(cc.compose(T,powers[-1]))
    D=cc.TensorField(n,K,T,1,powers)
    if mode=='one_coordinate':
        rows=[sum(K.trace(K.mul(1 << bit,K.power(2,j))) << bit for bit in range(s))
              for j in range(2*r-1)]
        nonzero=cc.nullspace(rows,s)
        assert nonzero
        a=K.power(nonzero[0],1 << (s-1))
        coefficients=[(0,K.mul(a,K.power(2,i))) for i in range(r)]
    else:
        assert r<=3
        a=cc.nullspace([sum(K.trace(1 << j) << j for j in range(s))],s)[0]
        coefficients=[(i,a) for i in range(r)]
    U=tuple(cc.action(dualP,sum(K.trace(K.mul(c,1 << j)) << (s*block+j)
                               for j in range(s))) for block,c in coefficients)
    assert len(echelon(U))==r
    invJ0=cc.inverse(J0)
    assert all((u&cc.action(invJ0,v)).bit_count()%2==0 for u in U for v in U)
    H0=tuple(1 << (i^1) for i in range(r)) if alternating else cc.identity(r)
    if alternating:assert r%2==0
    change=hidden_basis(r,rng) if r>1 else (1,)
    H=cc.compose(cc.transpose(change),cc.compose(H0,change))
    J=rc.matrix_add(J0,ds.defect_matrix(U,H,n))
    cc.inverse(J)
    phases=[]
    if make_phases:
        for _ in range(L):
            poly={(1,1,1):1,(1,0,0):rng.randrange(K.q),(0,1,1):rng.randrange(K.q)}
            phases.append(sorted(cc.anf_from_function(n,lambda x:K.trace(ff.evaluate_mv(K,poly,coordinates(x))))))
    desc=['cubic-field-v1',n,list(J),phases,rng.randrange(1 << n),rng.randrange(n)]
    return desc,D,U,H


def frobenius_degree(K,a):
    value=K.mul(a,a);degree=1
    while value!=a:
        value=K.mul(value,value);degree+=1
    return degree


def scalar_matrix(D,a):
    return tuple(xor_sum(power[j] for i,power in enumerate(D.powers) if a >> i & 1)
                 for j in range(D.n))


def verify_correction(D,J,U,H,answer):
    assert answer['rank']==len(U)
    assert span_equal(U,answer['columns'])
    assert ds.defect_matrix(answer['columns'],answer['form'],D.n)==ds.defect_matrix(U,H,D.n)
    assert D.pairing(answer['balanced_matrix']) is not None


def test_probability_and_recovery(rng):
    records=[]
    for s,r,mode,alternating in [(3,2,'independent_coordinates',False),
                                 (3,3,'independent_coordinates',False),
                                 (6,1,'one_coordinate',False),
                                 (9,2,'one_coordinate',True)]:
        desc,D,U,H=build_source(s,r,2,rng,mode,alternating,False)
        generated=position=joint=checked=0;bad_generator=None;good_generator=None
        for a in range(D.field.q):
            T=scalar_matrix(D,a);Tt=cc.transpose(T)
            TU=cc.compose(Tt,U);T2U=cc.compose(Tt,TU)
            good=len(echelon(U+TU+T2U))==3*r
            gen=frobenius_degree(D.field,a)==s
            generated+=gen;position+=good;joint+=gen and good
            if gen and not good:bad_generator=a
            if gen and good and checked<20:
                flat=[cc.flatten(t) for t in D.centroid_basis]
                E=ds.certify_generator(D.n,D.centroid_basis,flat,echelon(flat),a,1)
                answer,reason=ds.recover_subspace(E,desc[2],r)
                assert answer is not None,reason
                verify_correction(D,desc[2],U,H,answer)
                checked+=1;good_generator=a;bump('verified_good_generator_recoveries')
            bump('exhaustive_scalar_position_cases')
        if s>=3*r+3:
            assert D.field.q-position<=2*((1 << (3*r))-1)
            assert 4*joint>=D.field.q
            bump('uniform_joint_success_bound_cases')
        if mode=='independent_coordinates':
            assert joint==generated
            bump('independent_coordinate_all_generators')
        if s==9:assert bad_generator is not None and good_generator is not None
        records.append(dict(s=s,rank=r,mode=mode,field_size=D.field.q,full_generators=generated,
                            good_positions=position,joint_successes=joint,verified_recoveries=checked,
                            bad_full_generator=bad_generator))
    # Larger structured matrices, not full native sources or computed outputs.
    larger=[]
    for r in (4,8):
        s=3*r+3
        desc,D,U,H=build_source(s,r,2,rng,'one_coordinate',r%2==0,False)
        theta_power=D.field.power(2,r)
        assert frobenius_degree(D.field,theta_power)==s
        flat=[cc.flatten(t) for t in D.centroid_basis]
        E=ds.certify_generator(D.n,D.centroid_basis,flat,echelon(flat),theta_power,1)
        answer,reason=ds.recover_subspace(E,desc[2],r)
        assert answer is not None,reason
        verify_correction(D,desc[2],U,H,answer)
        terms=ds.selector_quadratic(2,answer['form'],(1 << r)-1)
        origin,support=ds.walsh_support(terms,3*r)
        assert len(support)==2*r
        larger.append(dict(s=s,rank=r,n=D.n,walsh_support_dimension=len(support),
                           cubic_counts=1 << len(support),scope='structured matrix construction only'))
        bump('growing_rank_matrix_recoveries')
    return records,larger


def test_walsh(rng):
    for r,L,alternating in [(1,1,False),(1,3,False),(2,2,False),
                            (2,2,True),(2,3,True),(3,2,False)]:
        H=tuple(1 << (i^1) for i in range(r)) if alternating else cc.identity(r)
        for delta in (0,(1 << r)-1):
            k=2*L-1;t=k*r
            terms=ds.selector_quadratic(L,H,delta)
            origin,basis=ds.walsh_support(terms,t)
            support={origin^cc.action(basis,a) for a in range(1 << len(basis))}
            assert len(basis)==(k-1)*r and len(support)==1 << ((k-1)*r)
            values=[-1 if cc.anf_evaluate(terms,b) else 1 for b in range(1 << t)]
            parts=ds.quadratic_parts(terms)
            for z in range(1 << t):
                w=sum(v*(-1 if (z&b).bit_count()&1 else 1) for b,v in enumerate(values))
                assert (w!=0)==(z in support)
                assert w==ds.walsh_from_parts(parts,t,z)
                if w:assert abs(w)==1 << (L*r)
                bump('independent_walsh_support_and_weights')
            bump('rank_tensor_path_cases')


def walsh_in_place(values):
    values=list(values);step=1
    while step<len(values):
        for start in range(0,len(values),2*step):
            for j in range(start,start+step):
                a,b=values[j],values[j+step]
                values[j],values[j+step]=a+b,a-b
        step*=2
    return values


def complete_two_layer_counts(result,branches):
    """Exact finite sum over ALL points, factored across two independent sides.

    This verifier still costs q^6 operations. It is not the p-adic backend.
    """
    assert result['k']==3
    K=result['field'];r=result['correction']['rank'];mask=(1 << r)-1
    left={};right={};middle={}
    for e,c in result['base']['phase'].items():
        a,b=any(e[:3]),any(e[6:])
        assert not (a and b)
        (left if a else right if b else middle)[e]=c
    A=table_evaluator(K,left);B=table_evaluator(K,right);C=table_evaluator(K,middle)
    vectors=list(product(range(K.q),repeat=3));zero=(0,0,0)
    selectors={}
    for x in vectors:
        bits=0
        for i,ell in enumerate(result['ell']):
            value=xor_sum(K.mul(c,a) for c,a in zip(ell,x))
            bits |= K.trace(value) << i
        selectors[x]=bits
    sums=[0]*len(branches)
    for mid in vectors:
        a=[0]*(1 << r);b=[0]*(1 << r)
        for side in vectors:
            bucket=selectors[side]
            a[bucket] += -1 if K.trace(A(side+mid+zero)) else 1
            b[bucket] += -1 if K.trace(B(zero+mid+side)) else 1
        a=walsh_in_place(a);b=walsh_in_place(b)
        c=K.trace(C(zero+mid+zero));bits=selectors[mid]
        for j,(z,w,branch) in enumerate(branches):
            sign=-1 if c^(((z >> r)&bits).bit_count()&1) else 1
            sums[j] += sign*a[z&mask]*b[(z >> (2*r))&mask]
    return [(w,K.q**9+signed) for (_,w,_),signed in zip(branches,sums)]


def main():
    rng=random.Random(1730506)
    probabilities,larger=test_probability_and_recovery(rng)
    print('Probability and source-subspace core checks passed',flush=True)
    test_walsh(rng)
    print('Direct Walsh-support checks passed',flush=True)
    records=[]
    for s,r,L,mode,alternating in [(3,2,2,'independent_coordinates',False),
                                   (3,2,2,'independent_coordinates',True),
                                   (3,3,2,'independent_coordinates',False),
                                   (3,2,3,'independent_coordinates',True),
                                   (9,2,2,'one_coordinate',True)]:
        desc,known,U,H=build_source(s,r,L,rng,mode,alternating)
        if L==3:
            desc[3]=[desc[3][0],[],desc[3][0]]
            desc[4] |= 1 << desc[5]
        native=cc.compile_native(desc)
        audit=None
        if s==9:
            centroid=cc.centroid(desc[1],desc[3][0]);span=echelon([cc.flatten(t) for t in centroid])
            bad=solve(span,cc.flatten(known.generator))
            good=solve(span,cc.flatten(cc.compose(known.generator,known.generator)))
            class ScriptedTape:
                def __init__(self,values):self.values=iter(values);self.bits=0
                def getrandbits(self,width):self.bits+=width;return next(self.values,0)
            tape=ScriptedTape([bad,good])
            result,details=ds.reduce_native(native['qubits'],native['gates'],native['basis'],native['output'],r,1,tape)
            assert result is not None,details
            assert details['trials']==2 and tape.bits==2*s
            assert details['rejected'] and 'not_field_generator' not in details['rejected']
            bump('bad_full_generator_then_success')
            refused,failure=ds.discover_source(desc,r-1,2,ScriptedTape([good]*6))
            assert refused is None and failure['trials']==6 and failure['random_bits']==6*s
            assert failure['rejected']=={'rank_budget_exceeded':6}
            bump('rank_budget_bounded_failure')
            refused,failure=ds.discover_source(desc,r,2,ScriptedTape([0]*6))
            assert refused is None and failure['random_bits']==6*s
            assert failure['rejected']=={'not_field_generator':6}
            bump('zero_tape_bounded_failure')
            audit=dict(discovery=details,scripted_bad_generator=bad,scripted_good_generator=good)
        else:
            result,details=ds.reduce_native(native['qubits'],native['gates'],native['basis'],native['output'],r,32,rng)
            assert result is not None,details
        verify_correction(known,desc[2],U,H,result['correction'])
        branches=list(ds.cubic_branches(result))
        k=2*L-1
        assert len(branches)==1 << ((k-1)*r)
        assert len({z for z,_,_ in branches})==len(branches)
        assert sum(w for _,w,_ in branches)==1 << (k*r)
        assert all(abs(w)==1 << (L*r) and b['degree']<=3 for _,w,b in branches)
        D=result['structure'];K=D.field;n=desc[1]
        for _ in range(16 if L==3 else 64):
            physical=[rng.randrange(1 << n) for _ in range(k)]
            x=tuple(a for v in physical for a in D.coordinates(v))
            expected=boolean_output_phase(desc,physical)
            selector=sum(((u&v).bit_count()&1) << (j*r+i)
                         for j,v in enumerate(physical) for i,u in enumerate(result['correction']['columns']))
            assert expected==K.trace(ff.evaluate_mv(K,result['base']['phase'],x))^cc.anf_evaluate(result['selector'],selector)
            actual=sum(w*(-1 if K.trace(ff.evaluate_mv(K,b['phase'],x)) else 1) for _,w,b in branches)
            assert actual==(-1 if expected else 1)*(1 << (k*r))
            bump('full_output_pointwise_rank_identities')
        counts=[];p=None
        if s==3 and r==2 and L==2:
            print('Complete separated cubic counts:',n,r,alternating,len(branches),flush=True)
            counts=complete_two_layer_counts(result,branches)
            p,signed=ds.combine_counts(result,counts)
            assert p==fast_independent_probability(desc)
            bump('complete_separated_affine_counts',len(counts))
            bump('complete_rank_two_output_counts')
            for bits in (3,128,8192):
                rounded=rc.round_probability(p,bits)
                assert 0<=p-rounded<Fraction(1,1 << bits)
                bump('rank_two_precision_cases')
            if alternating:
                gates=[('X',j) for j in range(n) if native['basis'] >> j & 1]+native['gates']
                state,h,_=sparse_native(gates);np=ZERO
                for x,a in state.items():
                    if x >> native['output'] & 1:np=add(np,mul(a,conjugate(a)))
                assert scale(np,Fraction(1,1 << h))==scale(ONE,p)
                bump('independent_native_rank_two_output')
        if L==3:
            p=fast_independent_probability(desc)
            assert p==1
            zero_desc=list(desc);zero_desc[4] ^= 1 << desc[5]
            assert fast_independent_probability(zero_desc)==0
            bump('three_layer_promised_echo_controls',2)
        records.append(dict(n=n,s=s,rank=r,layers=L,mode=mode,alternating=alternating,
                            native_records=len(native['gates']),source_bits=native['source_bits'],
                            discovery=details,scripted_audit=audit,cubic_counts=len(branches),
                            count_variables=6*L-2,complete_counts=counts,probability=str(p) if p is not None else None))
        print('Native rank-dependent source passes:',n,r,flush=True)
    for L in (1,2):
        desc=prior_source(2,L,rng,perturb=L==1)
        result,details=ds.discover_source(desc,0,32,rng)
        assert result is not None and result['correction']['rank']==0,details
        branches=list(ds.cubic_branches(result));assert len(branches)==1
        if L==2:counts=complete_two_layer_counts(result,branches)
        else:
            _,w,branch=branches[0]
            counts=[(w,complete_count(result['field'],branch['phase'],branch['field_variables']))]
        p,_=ds.combine_counts(result,counts)
        assert p==fast_independent_probability(desc)
        bump('zero_rank_or_unused_pairing_full_count_controls')
    desc=prior_source(3,3,rng,perturb=True,arbitrary_second=True)
    refused,details=ds.discover_source(desc,1,32,rng)
    assert refused is None and details['reason']=='phase_outside_cubic_field_span'
    bump('unsupported_full_phase_refusal')
    paths=['src/field_defect_subspaces.py','src/check_field_defect_subspaces.py',
           'src/rank_one_field_correction.py','src/check_rank_one_field_correction.py',
           'src/cubic_centroid_descent.py','src/check_cubic_centroid_descent.py',
           'src/finite_field_acceptance.py','src/finite_field_descent.py',
           'src/frobenius_trace_degree.py','src/check_frobenius_trace_degree.py',
           'src/magic_residual_counts.py','src/check_bordered_rank_fourier.py',
           'src/check_acceptance_estimator.py','src/check_eth_acceptance_transfer.py',
           'src/quartic_pfaffian_moments.py','src/eth_acceptance_encoding.py',
           'src/bordered_rank_fourier.py','src/rank_orbit_fourier.py']
    hashes={}
    for path in paths:
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
    prior=ROOT/'artifacts/s173-rank-one-field-correction-checks.json'
    receipt=dict(status='pass',seed=1730506,counts=COUNTS,probability_cases=probabilities,
                 larger_structured_matrices=larger,native_sources=records,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Unknown subspace and symmetric-form recovery, bounded joint discovery, affine Walsh support and full rank-dependent output transfer. Exact q^6 separated verification only on two nine-qubit rank-two sources. No external p-adic backend implementation or universal compiler.')
    target=ROOT/'artifacts/s173-field-defect-subspace-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
