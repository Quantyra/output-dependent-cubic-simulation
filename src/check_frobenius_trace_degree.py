"""New-claim checks for exact Frobenius degree optimization and full output descent."""
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
from finite_field_descent import echelon,solve
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale,round_probability

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def field(s,rng):
    K,_=ff.find_field(s,32,rng)
    assert K is not None
    return K


def truth_vector(K,poly,m):
    return sum(K.trace(ff.evaluate_mv(K,poly,x)) << j
               for j,x in enumerate(product(range(K.q),repeat=m)))


def below_degree_span(K,m,degree):
    columns=[]
    for e in product(range(degree+1),repeat=m):
        if sum(e)>degree:continue
        for j in range(K.r):
            columns.append(truth_vector(K,{e:1 << j},m))
    return echelon(columns)


def source(s,L,rng,offset=None,perturb=False,block_basis=False,arbitrary_second=False):
    K=field(s,rng)
    n=3*s
    if block_basis:
        blocks=[hidden_basis(s,rng) if s>1 else (1,) for _ in range(3)]
        P=tuple(x << (a*s) for a,A in enumerate(blocks) for x in A)
    else:
        P=hidden_basis(n,rng)
    invP=cc.inverse(P)
    def coords(x):
        packed=cc.action(invP,x)
        return tuple((packed >> (a*s)) & (K.q-1) for a in range(3))
    G=tuple(sum((int(i//s==j//s)*K.trace(K.mul(1 << (i%s),1 << (j%s)))) << i
                for i in range(n)) for j in range(n))
    J=cc.compose(cc.transpose(invP),cc.compose(G,invP))
    if perturb:
        invJ=cc.inverse(J)
        candidates=[1 << j for j in range(n)]+[(1 << i)|(1 << j)
                                              for i in range(n) for j in range(i)]
        v=next(x for x in candidates if not (x&cc.action(invJ,x)).bit_count()&1)
        J=tuple(c^(v if v >> j & 1 else 0) for j,c in enumerate(J))
        cc.inverse(J)
    phases=[]
    for layer in range(L):
        poly={(1,1,1):1,(1,0,0):rng.randrange(K.q),(0,1,1):rng.randrange(K.q)}
        poly={e:c for e,c in poly.items() if c}
        if offset is not None and layer==0:
            ff.add_term(poly,(1,1 << offset,0),1)
        if arbitrary_second and layer==1:
            ff.add_term(poly,(1,2,4),rng.randrange(1,K.q))
        phase=cc.anf_from_function(n,lambda x:K.trace(ff.evaluate_mv(K,poly,coords(x))))
        phases.append(sorted(phase))
    return ['cubic-field-v1',n,list(J),phases,rng.randrange(1 << n),rng.randrange(n)]


def fast_independent_probability(desc):
    _,n,J,phases,basis,output=desc
    size=1 << n
    state=[0]*size;state[basis]=1
    permutation=[cc.action(J,x) for x in range(size)]
    def fourier(vector):
        result=[0]*size
        for x,a in enumerate(vector):result[permutation[x]]=a
        step=1
        while step<size:
            for start in range(0,size,2*step):
                for j in range(start,start+step):
                    a,b=result[j],result[j+step]
                    result[j],result[j+step]=a+b,a-b
            step *= 2
        return result
    state=fourier(state)
    for phase in phases:
        state=[-a if cc.anf_evaluate(phase,x) else a for x,a in enumerate(state)]
        state=fourier(state)
    norm=1 << (n*(len(phases)+1))
    assert sum(a*a for a in state)==norm
    return Fraction(sum(a*a for x,a in enumerate(state) if x >> output & 1),norm)


def main():
    rng=random.Random(1730504)
    offsets=[]
    for s in range(1,13):
        K=field(s,rng)
        for t in range(s):
            c=rng.randrange(1,K.q)
            original={(1,1 << t):c}
            canonical=ft.trace_function(K,original)
            answer=ft.optimize_trace(K,canonical,2)
            expected=1+(1 << min(t,s-t))
            assert answer['degree']==expected
            assert ft.trace_function(K,answer['polynomial'])==canonical
            bump('single_offset_degree_identities')
            if s<=4:
                assert truth_vector(K,original,2)==truth_vector(K,answer['polynomial'],2)
                bump('exhaustive_offset_function_comparisons')
            if s in (2,3,4) and t==s//2:
                target=truth_vector(K,original,2)
                assert solve(below_degree_span(K,2,expected-1),target) is None
                assert solve(below_degree_span(K,2,expected),target) is not None
                bump('independent_full_monomial_span_minimality')
            offsets.append(dict(s=s,t=t,minimum=answer['degree']))
    short=[]
    for s in (2,4,6):
        K=field(s,rng)
        ell=s//2
        a=next(1 << j for j in range(s) if ft.relative_trace(K,1 << j,ell))
        canonical=ft.trace_function(K,{(1+(1 << ell),):a})
        answer=ft.optimize_trace(K,canonical,1)
        assert len(answer['orbits'])==1 and answer['orbits'][0]['length']==ell
        rep=tuple(answer['orbits'][0]['representative'])
        # Using the subfield seed as an absolute-trace coefficient gives zero.
        naive={rep:canonical[rep]}
        assert not ft.trace_function(K,naive) and canonical
        assert truth_vector(K,answer['polynomial'],1)==sum(
            ff.evaluate_mv(K,canonical,(x,)) << x for x in range(K.q))
        short.append(dict(s=s,orbit_length=ell,degree=answer['degree']))
        bump('short_orbit_relative_trace_repairs')
    for s in range(1,9):
        K=field(s,rng)
        answer=ft.optimize_trace(K,{(0,):1},1)
        assert answer['degree']==0 and ft.trace_function(K,answer['polynomial'])=={(0,):1}
        bump('constant_trace_preimages')
    native_records=[]
    cases=[(1,1,None,False,False,False),(1,2,None,False,False,False),
           (1,3,None,False,False,False),(2,2,None,False,False,False),
           (3,2,None,False,False,True),(3,3,None,False,False,True),
           (4,2,2,False,True,False),
           (6,2,3,False,True,False),(4,2,None,True,True,False),
           (6,2,None,True,True,False),(6,1,3,True,True,False)]
    for s,L,offset,perturb,block_basis,arbitrary_second in cases:
        desc=source(s,L,rng,offset,perturb,block_basis,arbitrary_second)
        native=cc.compile_native(desc)
        reduction,details=ft.reduce_native(native['qubits'],native['gates'],
                                          native['basis'],native['output'],32,rng)
        assert reduction is not None,details
        D=details['structure'];K=D.field;n=desc[1]
        if L==2 and offset is not None:
            assert reduction['minimum_trace_degree']==max(3,1+(1 << min(offset,s-offset)))
            bump('native_remainder_optimum')
        if L==2 and perturb:
            assert reduction['minimum_trace_degree']==max(3,1+(1 << (s//2)))
            bump('native_pairing_optimum')
        if L==3 and arbitrary_second:
            assert reduction['minimum_trace_degree']==7
            old,reason=cc.discover_source(desc,32,rng)
            assert old is None and reason=='phase_outside_cubic_field_span'
            bump('native_internal_cubic_orbit_optimum')
            bump('prior_cubic_gate_rescued')
        if L==1:
            assert reduction['minimum_trace_degree']<=2
            bump('whole_output_derivative_degree_reduction')
        if L==2 and ((offset is not None and s>=4) or (perturb and s>=4)):
            old,reason=cc.discover_source(desc,32,rng)
            assert old is None and reason in ('phase_outside_cubic_field_span','pairing_outside_cubic_field_span')
            bump('prior_cubic_gate_rescued')
        free=n*(2*L-1)
        points=range(1 << free) if free<=9 else [rng.randrange(1 << free) for _ in range(128)]
        for packed in points:
            values=[(packed >> (n*i)) & ((1 << n)-1) for i in range(2*L-1)]
            coordinate=tuple(a for x in values for a in D.coordinates(x))
            expected=boolean_output_phase(desc,values)
            assert cc.anf_evaluate(details['output_anf'],packed)==expected
            assert ff.evaluate_mv(K,details['canonical'],coordinate)==expected
            assert K.trace(ff.evaluate_mv(K,reduction['phase'],coordinate))==expected
            bump('whole_output_pointwise_identities')
        p=fast_independent_probability(desc) if n<=12 else None
        counted=None
        if s<=2:
            print('Full optimized count:',n,L,flush=True)
            value,_,counted=ff.enumerate_reduction(reduction)
            assert value==p
            for bits in (3,128):
                rounded=round_probability(scale(ONE,p),bits)
                assert 0<=p-rounded<Fraction(1,1 << bits)
                bump('count_readout_precision')
            bump('full_optimized_count_outputs')
            if L==2:
                gates=[('X',j) for j in range(n) if native['basis'] >> j & 1]+native['gates']
                state,h,peak=sparse_native(gates)
                result=ZERO
                for x,a in state.items():
                    if x >> native['output'] & 1:result=add(result,mul(a,conjugate(a)))
                assert scale(result,Fraction(1,1 << h))==scale(ONE,p)
                bump('independent_native_outputs')
        native_records.append(dict(n=n,layers=L,offset=offset,rank_one_pairing=perturb,
                                   arbitrary_second_cubic=arbitrary_second,
                                   minimum_degree=reduction['minimum_trace_degree'],
                                   count_degree=reduction['degree'],count_variables=reduction['count_variables'],
                                   output_anf_terms=len(details['output_anf']),
                                   canonical_terms=len(details['canonical']),
                                   trace_terms=len(reduction['phase']),
                                   native_records=len(native['gates']),source_bits=native['source_bits'],
                                   independent_probability=str(p) if p is not None else None,
                                   complete_point_count=counted))
        print('Native optimum and full phase pass:',n,L,reduction['minimum_trace_degree'],flush=True)
    # Purely algebraic large-degree controls, not constructed large native circuits.
    distant=[dict(s=s,t=s//2,minimum=1+(1 << (s//2))) for s in (16,32,64,128)]
    for item in distant:
        s,t=item['s'],item['t']
        orbit=[(1 << j)+(1 << ((t+j)%s)) for j in range(s)]
        assert min(orbit)==item['minimum']
        bump('large_exponent_parameter_controls')
    class ZeroTape:
        def getrandbits(self,k):return 0
    desc=source(2,1,rng)
    native=cc.compile_native(desc)
    reduction,reason=ft.reduce_native(native['qubits'],native['gates'],native['basis'],native['output'],4,ZeroTape())
    assert reduction is None and reason=='bounded_generator_failure'
    bump('bounded_field_failure')
    paths=['src/frobenius_trace_degree.py','src/check_frobenius_trace_degree.py',
           'src/cubic_centroid_descent.py','src/check_cubic_centroid_descent.py',
           'src/finite_field_acceptance.py','src/finite_field_descent.py',
           'src/check_bordered_rank_fourier.py','src/check_acceptance_estimator.py',
           'src/check_eth_acceptance_transfer.py','src/quartic_pfaffian_moments.py',
           'src/eth_acceptance_encoding.py','src/bordered_rank_fourier.py','src/rank_orbit_fourier.py']
    hashes={}
    for name in paths:
        raw=(ROOT/name).read_bytes();ast.parse(raw.decode('utf-8'))
        hashes[name]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
    old_receipt=ROOT/'artifacts/s173-cubic-centroid-descent-checks.json'
    result=dict(status='pass',seed=1730504,counts=COUNTS,single_offsets=offsets,
                short_orbits=short,native_sources=native_records,large_parameters=distant,
                hashes=hashes,prior_receipt_sha256=hashlib.sha256(old_receipt.read_bytes()).hexdigest(),
                scope='Minimum numerical trace degree in fixed field coordinates, including complete native output construction. Finite counts only on stated small cases; no p-adic backend or universal compiler.')
    out=ROOT/'artifacts/s173-frobenius-trace-degree-checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(out)),indent=2))


if __name__=='__main__':
    main()
