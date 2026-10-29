"""Independent tests of source-derived cubic centroid descent and its two gates."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import product
from pathlib import Path
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
from finite_field_descent import echelon,solve,xor_sum
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale,round_probability

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}

def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n

def hidden_basis(n,rng):
    columns=list(cc.identity(n))
    for _ in range(4*n):
        a,b=rng.sample(range(n),2)
        columns=[x^(((x >> a)&1) << b) for x in columns]
    return tuple(columns)

def source(s,L,rng,bad_remainder=False):
    K,_=ff.find_field(s,32,rng)
    n=3*s
    P=hidden_basis(n,rng)
    invP=cc.inverse(P)
    def coords(x):
        y=cc.action(invP,x)
        return tuple((y >> (i*s)) & (K.q-1) for i in range(3))
    G=tuple(sum((int(i//s==j//s)*K.trace(K.mul(1 << (i%s),1 << (j%s)))) << i
                for i in range(n)) for j in range(n))
    J=cc.compose(cc.transpose(invP),cc.compose(G,invP))
    phases=[]
    polys=[]
    for layer in range(L):
        poly={(1,1,1):1}
        if bad_remainder:
            poly[(1,4,0)]=1
        else:
            for e in [(3,0,0),(2,1,0),(1,0,1),(0,1,0),(0,0,0)]:
                c=rng.randrange(K.q)
                if c:poly[e]=c
        phase=cc.anf_from_function(n,lambda x:K.trace(ff.evaluate_mv(K,poly,coords(x))))
        phases.append(phase);polys.append(poly)
    desc=['cubic-field-v1',n,list(J),phases,rng.randrange(1 << n),rng.randrange(n)]
    return desc,K,P,polys,coords

def independent_probabilities(desc):
    _,n,J,phases,basis,output=desc
    size=1 << n
    state=[0]*size;state[basis]=1
    signs=[cc.action(J,x) for x in range(size)]
    def fourier(vector):
        return [sum((-a if (y&signs[x]).bit_count()&1 else a)
                    for x,a in enumerate(vector)) for y in range(size)]
    state=fourier(state)
    for phase in phases:
        state=[-a if cc.anf_evaluate(phase,x) else a for x,a in enumerate(state)]
        state=fourier(state)
    denominator=1 << (n*(len(phases)+1))
    assert sum(x*x for x in state)==denominator
    return [Fraction(sum(a*a for x,a in enumerate(state) if x >> j & 1),denominator)
            for j in range(n)]

def check_centroid(n,K,P,phase,computed):
    s=K.r
    expected=[]
    for j in range(s):
        scalar=tuple(K.mul(1 << j,1 << (i%s)) << (s*(i//s)) for i in range(n))
        expected.append(cc.flatten(cc.compose(P,cc.compose(scalar,cc.inverse(P)))))
    span=echelon([cc.flatten(t) for t in computed])
    assert len(span)==s
    assert all(solve(span,t) is not None for t in expected)
    bump('hidden_scalar_field_recoveries')

def boolean_output_phase(desc,values):
    _,n,J,phases,basis,output=desc
    L=len(phases)
    ket=values[:L]
    bra=values[L:]+[ket[-1]^cc.action(cc.inverse(J),1 << output)]
    value=(basis&cc.action(J,ket[0]^bra[0])).bit_count()&1
    for phase,x,y in zip(phases,ket,bra):
        value ^= cc.anf_evaluate(phase,x)^cc.anf_evaluate(phase,y)
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            value ^= (x&cc.action(J,y)).bit_count()&1
    return value

def main():
    rng=random.Random(1730503)
    records=[]
    count_cases=[]
    native_cases=[]
    for s,L in [(1,1),(1,2),(1,3),(2,1),(2,2),(3,1),(4,1),(5,1),(6,1)]:
        desc,K,P,polys,oldcoords=source(s,L,rng)
        native=cc.compile_native(desc)
        assert cc.recognize_native(native['qubits'],native['gates'],native['basis'],native['output'])==native['descriptor']
        reduction,discovered=cc.reduce_native(native['qubits'],native['gates'],
                                             native['basis'],native['output'],32,rng)
        assert reduction is not None,discovered
        D=discovered['structure']
        n=desc[1]
        check_centroid(n,K,P,desc[3][0],D.centroid_basis)
        assert reduction['count_variables']==6*L-2 and reduction['degree']<=3
        points=range(1 << n) if n<=9 else [rng.randrange(1 << n) for _ in range(256)]
        for x in points:
            assert D.physical(D.coordinates(x))==x
            for old,polynomial,phase in zip(polys,discovered['polynomials'],desc[3]):
                actual=D.field.trace(ff.evaluate_mv(D.field,polynomial,D.coordinates(x)))
                expected=K.trace(ff.evaluate_mv(K,old,oldcoords(x)))
                assert actual==expected==cc.anf_evaluate(phase,x)
                bump('whole_phase_values')
        for _ in range(128):
            values=[rng.randrange(1 << n) for j in range(2*L-1)]
            coord=tuple(y for x in values for y in D.coordinates(x))
            actual=D.field.trace(ff.evaluate_mv(D.field,reduction['phase'],coord))
            assert actual==boolean_output_phase(desc,values)
            bump('physical_output_phase_values')
        record=dict(n=n,layers=L,centroid_dimension=len(D.centroid_basis),
                    phase_span_dimension=discovered['phase_span_dimension'],
                    pairing_span_dimension=discovered['pairing_span_dimension'],
                    native_records=len(native['gates']),source_bits=native['source_bits'],
                    count_variables=reduction['count_variables'],count_degree=reduction['degree'],
                    field_attempts=D.attempts,field_modulus=D.field.modulus)
        records.append(record)
        if (s,L) in [(1,1),(1,2),(1,3),(2,1),(3,1)]:
            p,_,count=ff.enumerate_reduction(reduction)
            expected=independent_probabilities(desc)[desc[-1]]
            assert p==expected
            for b in (2,128):
                rounded=round_probability(scale(ONE,p),b)
                assert 0<=p-rounded<Fraction(1,1 << b)
                bump('physical_output_precision_cases')
            count_cases.append(dict(n=n,layers=L,probability=str(p),count=count))
            bump('complete_point_count_outputs')
            if (s,L) in [(1,1),(1,2),(2,1)]:
                gates=[('X',j) for j in range(n) if native['basis'] >> j & 1]+native['gates']
                state,h,peak=sparse_native(gates)
                value=ZERO
                for x,a in state.items():
                    if x >> native['output'] & 1:
                        value=add(value,mul(a,conjugate(a)))
                assert scale(value,Fraction(1,1 << h))==scale(ONE,p)
                native_cases.append(dict(n=n,layers=L,peak_support=peak,probability=str(p)))
                bump('independent_native_outputs')
        print('Hidden-field source and whole output phase pass:',n,L,flush=True)
    bad_phases=[]
    for s in (4,5,6):
        desc,K,P,polys,coords=source(s,2,rng,bad_remainder=True)
        native=cc.compile_native(desc)
        reduction,reason=cc.reduce_native(native['qubits'],native['gates'],
                                         native['basis'],native['output'],32,rng)
        assert reduction is None and reason=='phase_outside_cubic_field_span',reason
        # The cubic tensor still recovers the same hidden field.
        computed=cc.centroid(desc[1],desc[3][0])
        check_centroid(desc[1],K,P,desc[3][0],computed)
        bad_phases.append(dict(n=3*s,native_records=len(native['gates']),reason=reason))
        bump('lower_degree_obstruction_sources')
        print('Lower-degree remainder correctly rejected:',3*s,flush=True)
    bad_pairings=[]
    rescued_pairings=[]
    for s in (2,3,4,5,6):
        # Two phase layers exercise the newly admitted internal coupling.
        # At one layer the final Fourier sum removes every internal pairing.
        desc,K,P,polys,coords=source(s,2,rng)
        n=desc[1];J=desc[2];invJ=cc.inverse(J)
        candidates=[1 << j for j in range(n)]+[(1 << i)|(1 << j)
                                                for i in range(n) for j in range(i)]
        v=next(x for x in candidates if not (x&cc.action(invJ,x)).bit_count()&1)
        desc[2]=[column^(v if v >> j & 1 else 0) for j,column in enumerate(J)]
        cc.inverse(desc[2])
        native=cc.compile_native(desc)
        reduction,result=cc.reduce_native(n,native['gates'],native['basis'],native['output'],32,rng)
        if s<=3:
            assert reduction is not None and result['pairing'] is None
            expected=independent_probabilities(desc)[desc[-1]]
            count=None
            if s==2:
                print('Checking full two-layer semilinear point count:',n,flush=True)
                p,_,count=ff.enumerate_reduction(reduction)
                assert p==expected
                bump('rescued_pairing_complete_outputs')
            for _ in range(128):
                values=[rng.randrange(1 << n) for j in range(2*len(desc[3])-1)]
                coord=tuple(y for x in values for y in result['structure'].coordinates(x))
                actual=result['structure'].field.trace(ff.evaluate_mv(
                    result['structure'].field,reduction['phase'],coord))
                assert actual==boolean_output_phase(desc,values)
                bump('rescued_pairing_output_phase_values')
            rescued_pairings.append(dict(n=n,layers=len(desc[3]),
                                         reference_probability=str(expected),
                                         verified_point_count=count,
                                         pairing_span_dimension=result['pairing_span_dimension']))
            bump('non_field_bilinear_pairings_rescued')
        else:
            assert reduction is None and result=='pairing_outside_cubic_field_span',result
            bad_pairings.append(dict(n=n,reason=result))
            bump('fourier_cubic_degree_obstruction_sources')
            # The same J is harmless for one layer: no internal pairing survives.
            single=desc[:3]+[[desc[3][0]]]+desc[4:]
            single_native=cc.compile_native(single)
            one,one_source=cc.reduce_native(n,single_native['gates'],single[-2],single[-1],32,rng)
            assert one is not None and not one_source['pairing_needed']
            for _ in range(64):
                value=rng.randrange(1 << n)
                actual=one_source['structure'].field.trace(ff.evaluate_mv(
                    one_source['structure'].field,one['phase'],one_source['structure'].coordinates(value)))
                assert actual==boolean_output_phase(single,[value])
                bump('unused_pairing_output_phase_values')
            bump('unused_pairing_gates_avoided')
    class ZeroTape:
        def getrandbits(self,k):return 0
    desc,_,_,_,_=source(2,1,rng)
    D,reason=cc.discover_field(desc[1],desc[3][0],5,ZeroTape())
    assert D is None and reason=='bounded_generator_failure'
    bump('bounded_generator_failure_control')
    native=cc.compile_native(desc)
    bad=list(native['gates']);bad[-1]=('X',bad[-1][1])
    for n,gates,b,out in [(native['qubits'],bad,native['basis'],native['output']),
                         (native['qubits'],native['gates'],native['basis']^1,native['output']),
                         (1,[('X',0)],0,0)]:
        try:cc.recognize_native(n,gates,b,out)
        except ValueError:bump('native_rejection_controls')
        else:raise AssertionError('bad native accepted')
    paths=['src/cubic_centroid_descent.py','src/check_cubic_centroid_descent.py',
           'src/finite_field_acceptance.py','src/finite_field_descent.py',
           'src/check_bordered_rank_fourier.py','src/check_acceptance_estimator.py',
           'src/check_eth_acceptance_transfer.py','src/quartic_pfaffian_moments.py',
           'src/eth_acceptance_encoding.py','src/bordered_rank_fourier.py','src/rank_orbit_fourier.py']
    hashes={}
    for path in paths:
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
    result=dict(status='pass',seed=1730503,counts=COUNTS,sources=records,
                count_outputs=count_cases,native_outputs=native_cases,
                rejected_remainders=bad_phases,rejected_pairings=bad_pairings,
                rescued_pairings=rescued_pairings,hashes=hashes,
                scope='The source supplies native gates and Boolean ANF/Fourier data, not a field. Tests cover field discovery, full-phase reconstruction, actual-output reduction and two rejection mechanisms. Point counts are finite enumeration; no p-adic backend or universal coverage claim.')
    out=ROOT/'artifacts/s173-cubic-centroid-descent-checks.json'
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(out)),indent=2))

if __name__=='__main__':
    main()
