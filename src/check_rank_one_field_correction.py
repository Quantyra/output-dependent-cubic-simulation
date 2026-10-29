"""Independent finite checks of rank-one discovery and complete count identities."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import product
from pathlib import Path
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
import frobenius_trace_degree as ft
import rank_one_field_correction as rc
from finite_field_descent import echelon
from check_frobenius_trace_degree import source,fast_independent_probability
from check_cubic_centroid_descent import boolean_output_phase
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def table_evaluator(K,poly):
    """Finite-check accelerator: tabulate each monomial on its own support."""
    terms=[]
    for powers,c in poly.items():
        support=tuple(j for j,e in enumerate(powers) if e)
        table={}
        for x in product(range(K.q),repeat=len(support)):
            value=c
            for j,a in zip(support,x):value=K.mul(value,K.power(a,powers[j]))
            table[x]=value
        terms.append((support,table))
    def evaluate(x):
        value=0
        for support,table in terms:
            value ^= table[tuple(x[j] for j in support)]
        return value
    return evaluate


def complete_count(K,poly,variables):
    image=[0]*K.q
    for y in range(K.q):image[K.mul(y,y)^y] += 1
    evaluate=table_evaluator(K,poly)
    return sum(image[evaluate(x)] for x in product(range(K.q),repeat=variables))


def check_walsh():
    for L in range(1,6):
        k=2*L-1
        for delta in (0,1):
            terms=rc.selector_quadratic(L,delta)
            values=[-1 if cc.anf_evaluate(terms,b) else 1 for b in range(1 << k)]
            weights=[rc.walsh_coefficient(terms,k,z) for z in range(1 << k)]
            for z,w in enumerate(weights):
                direct=sum(v*(-1 if (z&b).bit_count()&1 else 1) for b,v in enumerate(values))
                assert w==direct
                bump('quadratic_walsh_direct_coefficients')
            assert sum(w!=0 for w in weights)==1 << (k-1)
            assert {abs(w) for w in weights if w}=={1 << L}
            assert sum(weights)==1 << k
            for b,v in enumerate(values):
                assert sum(w*(-1 if (z&b).bit_count()&1 else 1)
                           for z,w in enumerate(weights))==v*(1 << k)
                bump('complete_walsh_inversions')
            bump('path_rank_support_and_magnitude_cases')


def check_discovery(rng):
    records=[]
    for s in (2,3,4,6):
        desc=source(s,2,rng,block_basis=False)
        D,reason=cc.discover_field(desc[1],desc[3][0],32,rng)
        assert D is not None,reason
        J0=tuple(desc[2]);assert D.pairing(J0) is not None
        n=D.n
        vectors=list(range(1,1 << n)) if s<=3 else [rng.randrange(1,1 << n) for _ in range(64)]
        for v in vectors:
            J=rc.matrix_add(J0,rc.outer(v,n))
            correction,reason=rc.recover_correction(D,J)
            assert correction is not None,reason
            if s>=3:assert correction['mask']==v
            assert D.pairing(correction['balanced_matrix']) is not None
            assert rc.matrix_add(correction['balanced_matrix'],rc.outer(correction['mask'],n))==J
            bump('hidden_rank_one_recoveries')
        balanced,_=rc.recover_correction(D,J0)
        assert balanced['mask']==0
        bump('balanced_discovery_controls')
        refused=None
        for _ in range(64):
            u,v=rng.randrange(1,1 << n),rng.randrange(1,1 << n)
            J=rc.matrix_add(rc.matrix_add(J0,rc.outer(u,n)),rc.outer(v,n))
            if len(echelon(rc.commutator(D.generator,J)))!=4:continue
            try:cc.inverse(J)
            except ValueError:continue
            result,reason=rc.recover_correction(D,J)
            assert result is None and reason=='first_commutator_not_rank_two'
            refused=reason;bump('invertible_rank_two_defect_refusals');break
        assert refused is not None
        records.append(dict(field_degree=s,hidden_basis=True,recoveries=len(vectors),
                            rank_two_refusal=refused))
    return records


def main():
    rng=random.Random(1730505)
    check_walsh()
    discovery=check_discovery(rng)
    records=[]
    # s,L,perturb,block_basis,requested_delta (None preserves random output)
    cases=[(1,1,True,False,None),(1,2,True,False,None),(1,3,True,False,None),
           (2,2,True,False,None),(3,2,True,False,0),(3,2,True,False,1),
           (3,3,True,False,1),(4,2,True,True,1),(6,2,True,True,0),
           (3,2,False,False,None),(4,1,True,True,None)]
    for s,L,perturb,block,requested_delta in cases:
        desc=source(s,L,rng,perturb=perturb,block_basis=block)
        if requested_delta is not None:
            discovered,reason=rc.discover_source(desc,32,rng)
            assert discovered is not None,reason
            v=discovered['correction']['mask']
            invJ=cc.inverse(desc[2])
            options=[j for j in range(desc[1]) if (v&invJ[j]).bit_count()%2==requested_delta]
            assert options
            desc[5]=options[0]
        native=cc.compile_native(desc)
        result,reason=rc.reduce_native(native['qubits'],native['gates'],
                                       native['basis'],native['output'],32,rng)
        assert result is not None,reason
        D=result['structure'];K=result['field'];n=desc[1];k=result['k']
        branches=list(rc.cubic_branches(result))
        expected=1 << (k-1) if result['correction']['mask'] else 1
        assert len(branches)==expected and all(b['degree']<=3 for _,_,b in branches)
        aux=rc.auxiliary_count(result)
        assert aux['system_variables']==5*k+1 and aux['equation_count']==2*k+1
        assert aux['count_variables']==7*k+2 and aux['degree']<=4
        image=[[] for _ in range(K.q)]
        for y in range(K.q):image[K.mul(y,y)^y].append(y)
        mask=result['correction']['mask']
        points=range(1 << (n*k)) if n*k<=9 else [rng.randrange(1 << (n*k)) for _ in range(128)]
        for packed in points:
            physical=[(packed >> (n*j))&((1 << n)-1) for j in range(k)]
            x=tuple(a for v in physical for a in D.coordinates(v))
            bits=[(mask&v).bit_count()&1 for v in physical]
            selector=sum(b << j for j,b in enumerate(bits))
            base_value=ff.evaluate_mv(K,result['base']['phase'],x)
            original=boolean_output_phase(desc,physical)
            assert original==K.trace(base_value)^cc.anf_evaluate(result['selector'],selector)
            walsh=sum(w*(-1 if K.trace(ff.evaluate_mv(K,b['phase'],x)) else 1)
                      for _,w,b in branches)
            assert walsh==(-1 if original else 1)*(1 << k)
            bump('complete_output_pointwise_walsh_identities')
            # Directly enumerate every lift of this fixed original point.
            ell=[0]*k
            for j in range(k):
                for a,c in enumerate(result['ell']):ell[j] ^= K.mul(c,x[3*j+a])
            lifts=[image[e^(aux['tau'] if b else 0)] for e,b in zip(ell,bits)]
            assert all(len(u)==2 for u in lifts)
            for e,expected_bit in zip(ell,bits):
                fiber_sizes=[len(image[e^K.mul(aux['tau'],b)])
                             if K.mul(b,b)^b==0 else 0 for b in range(K.q)]
                assert fiber_sizes==[2 if b==expected_bit else 0 for b in range(K.q)]
                bump('all_selector_values_checked')
            target=base_value^(aux['tau'] if cc.anf_evaluate(result['selector'],selector) else 0)
            witnesses=0
            for u in product(*lifts):
                for z in image[target]:
                    assignment=x+tuple(bits)+u+(z,)
                    assert all(ff.evaluate_mv(K,e,assignment)==0 for e in aux['equations'])
                    witnesses += 1
            assert witnesses==(0 if original else 1 << (k+1))
            bump('complete_auxiliary_point_fibers')
        probability=fast_independent_probability(desc) if n<=12 else None
        counts=[]
        if s==1 or (s==2 and L==2):
            print('Complete cubic branch counts:',n,L,len(branches),flush=True)
            for z,w,branch in branches:
                count=complete_count(K,branch['phase'],branch['field_variables'])
                counts.append((w,count))
                bump('complete_affine_branch_counts')
            p,signed=rc.combine_counts(result,counts)
            assert p==probability
            for bits in (3,128,8192):
                rounded=rc.round_probability(p,bits)
                assert 0<=p-rounded<Fraction(1,1 << bits)
                bump('exact_readout_precision_cases')
            bump('complete_physical_output_counts')
            if L==2:
                gates=[('X',j) for j in range(n) if native['basis'] >> j & 1]+native['gates']
                state,h,_=sparse_native(gates)
                native_p=ZERO
                for x,a in state.items():
                    if x >> native['output'] & 1:native_p=add(native_p,mul(a,conjugate(a)))
                assert scale(native_p,Fraction(1,1 << h))==scale(ONE,p)
                bump('independent_exact_native_outputs')
            if s==1 and L<=2:
                functions=[table_evaluator(K,e) for e in aux['equations']]
                system=sum(all(f(x)==0 for f in functions)
                           for x in product(range(K.q),repeat=aux['system_variables']))
                assert system==(1 << k)*(K.q**(3*k)+signed)
                bump('complete_auxiliary_system_counts')
                if L==1:
                    evaluate=table_evaluator(K,aux['hypersurface'])
                    hyper=sum(evaluate(x)==0 for x in product(range(K.q),repeat=aux['count_variables']))
                    p2,s2,sys2=rc.auxiliary_readout(result,aux,hyper)
                    assert (p2,s2,sys2)==(p,signed,system)
                    bump('complete_auxiliary_hypersurface_counts')
        old_degree=None
        if s in (4,6) and L==2:
            old,details=ft.reduce_native(native['qubits'],native['gates'],
                                         native['basis'],native['output'],32,rng)
            assert old is not None
            old_degree=old['minimum_trace_degree']
            assert old_degree==1+(1 << (s//2))
            bump('exponential_degree_family_replaced')
        records.append(dict(n=n,layers=L,source_bits=native['source_bits'],
                            native_records=len(native['gates']),method=result['correction']['method'],
                            correction_mask=mask,requested_output_shift_bit=requested_delta,
                            cubic_counts=len(branches),count_variables=3*k+1,
                            auxiliary_variables=aux['count_variables'],prior_minimum_degree=old_degree,
                            independent_probability=str(probability) if probability is not None else None,
                            complete_counts=counts))
        print('Native source and correction pass:',n,L,result['correction']['method'],flush=True)
    # A rank-one pairing defect cannot repair an unsupported full phase.
    desc=source(3,3,rng,perturb=True,arbitrary_second=True)
    unsupported,reason=rc.discover_source(desc,32,rng)
    assert unsupported is None and reason=='phase_outside_cubic_field_span'
    bump('noncubic_phase_refusal')
    class ZeroTape:
        def getrandbits(self,k):return 0
    desc=source(3,2,rng,perturb=True)
    refused,reason=rc.discover_source(desc,4,ZeroTape())
    assert refused is None and reason=='bounded_generator_failure'
    bump('bounded_field_failure')
    paths=['src/rank_one_field_correction.py','src/check_rank_one_field_correction.py',
           'src/magic_residual_counts.py','src/cubic_centroid_descent.py',
           'src/check_cubic_centroid_descent.py','src/finite_field_acceptance.py',
           'src/finite_field_descent.py','src/frobenius_trace_degree.py',
           'src/check_frobenius_trace_degree.py','src/check_bordered_rank_fourier.py',
           'src/check_acceptance_estimator.py','src/check_eth_acceptance_transfer.py',
           'src/quartic_pfaffian_moments.py','src/eth_acceptance_encoding.py',
           'src/bordered_rank_fourier.py','src/rank_orbit_fourier.py']
    hashes={}
    for name in paths:
        raw=(ROOT/name).read_bytes();ast.parse(raw.decode('utf-8'))
        hashes[name]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
    previous=ROOT/'artifacts/s173-frobenius-trace-degree-checks.json'
    receipt=dict(status='pass',seed=1730505,counts=COUNTS,discovery=discovery,
                 native_sources=records,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(previous.read_bytes()).hexdigest(),
                 scope='Rank-one discovery, exact auxiliary fibers, and streamed cubic-count output. Complete enumeration only on stated small sources. No p-adic backend implementation, benchmark or universal compiler.')
    target=ROOT/'artifacts/s173-rank-one-field-correction-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
