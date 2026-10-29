"""Independent finite checks for complete cubic/quad phase-defect discovery."""
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
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve,xor_sum
from check_field_defect_subspaces import build_source,span_equal,complete_two_layer_counts
from check_frobenius_trace_degree import fast_independent_probability
from check_cubic_centroid_descent import boolean_output_phase
from check_rank_one_field_correction import complete_count
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def covector(D,coefficient,axis):
    mask=sum(D.field.trace(D.field.mul(coefficient,1 << j)) << (axis*D.s+j)
             for j in range(D.s))
    return cc.action(cc.transpose(D.inverse),mask)


def independent_product_anf(n,forms):
    return set(cc.anf_from_function(n,lambda x:all((u&x).bit_count()&1 for u in forms)))


def compatible_quadratic(D):
    K=D.field
    def value(x):
        a,b,c=D.coordinates(x)
        return K.trace(K.mul(K.mul(a,a),b)^K.mul(K.mul(b,b),b)^K.mul(b,c))
    single=[value(1 << j) for j in range(D.n)]
    matrix=[0]*D.n
    for i in range(D.n):
        for j in range(i+1,D.n):
            if value((1 << i)|(1 << j))^single[i]^single[j]:
                matrix[i] ^= 1 << j;matrix[j] ^= 1 << i
    return tuple(matrix)


def matrix_checks(rng):
    records=[]
    for s,r,mode in [(9,2,'independent_coordinates'),(19,2,'one_coordinate'),(33,4,'one_coordinate')]:
        desc,D,U,H=build_source(s,r,2,rng,mode,True,False)
        element=2 if mode=='independent_coordinates' else D.field.power(2,r)
        flat=[cc.flatten(a) for a in D.centroid_basis]
        E=ds.certify_generator(D.n,D.centroid_basis,flat,echelon(flat),element,1)
        assert E is not None
        powers=pd.scalar_powers(E.generator)
        selected=tuple(v for j in pd.TRANSLATES for v in cc.compose(cc.transpose(powers[j]),U))
        assert len(echelon(selected))==7*r
        compatible=compatible_quadratic(D)
        assert not any(pd.displacement(compatible,powers))
        assert not any(pd.displacement(compatible,powers,2))
        bump('compatible_quadratic_annihilations',2)
        matrix=rc.matrix_add(compatible,ds.defect_matrix(U,H,D.n))
        found,details=pd.quadratic_defect_image(matrix,E,r)
        assert found is not None and span_equal(found,U),details
        assert details['displacement_ranks']==[4*r,4*r]
        bump('quadratic_hidden_subspace_recoveries')
        refused,reason=pd.quadratic_defect_image(matrix,E,r-1)
        assert refused is None and reason['reason']=='quadratic_rank_budget'
        bump('quadratic_rank_budget_refusals')
        records.append(dict(s=s,rank=r,n=D.n,displacement_ranks=details['displacement_ranks'],
                            translated_dimension=7*r,field_size_bound=s>=7*r+5,
                            scope='matrix identity and discovery only'))
    return records


def spectrum_checks(rng):
    records=[]
    cases=[(0,{0}),(3,{7}),(4,{7,0}),(7,{7,56,65}),(8,{7,28,112,128}),
           (6,{3,12,48,1,0}),(9,{7,56,448,5,0})]
    for t,terms in cases:
        degree=max((m.bit_count() for m in terms),default=0)
        mock=dict(selector_bits=t,selector=terms,residual_degree=degree,
                  active_bits=tuple(pd.bits(pd.xor_or(terms))))
        got=dict(pd.spectrum(mock))
        values=[-1 if cc.anf_evaluate(terms,b) else 1 for b in range(1 << t)]
        expected={}
        for z in range(1 << t):
            w=sum(v*(-1 if (z&b).bit_count()&1 else 1) for b,v in enumerate(values))
            if w:expected[z]=w
            bump('independent_full_walsh_coefficients')
        assert got==expected
        assert sum(got.values())==(-1 if 0 in terms else 1)*(1 << t)
        for b,v in enumerate(values):
            assert sum(w*(-1 if (z&b).bit_count()&1 else 1) for z,w in got.items())==v*(1 << t)
            bump('full_walsh_inverse_identities')
        if degree==3 and len({abs(w) for w in got.values()})>1:bump('nonflat_cubic_spectra')
        records.append(dict(bits=t,degree=degree,active_bits=len(mock['active_bits']),
                            nonzero=len(got),magnitudes=sorted({abs(w) for w in got.values()})))
    return records


def build_native_case(s,L,rng,where,lower=False,pure_quadratic=False,coupling=False):
    desc,D,U,H=build_source(s,3,L,rng,'independent_coordinates',False)
    if not coupling:desc[2]=list(rc.matrix_add(desc[2],ds.defect_matrix(U,H,D.n)))
    if lower or pure_quadratic:
        U=tuple(covector(D,D.field.power(2,i),0) for i in range(3))
        V=(covector(D,1,1),covector(D,1,2))
    else:V=()
    defect=set() if pure_quadratic else independent_product_anf(D.n,U)
    if V:defect ^= independent_product_anf(D.n,V)
    for i in where:desc[3][i]=sorted(set(desc[3][i])^defect)
    return desc,D,U,V


def main():
    rng=random.Random(1730507)
    matrix_records=matrix_checks(rng)
    print('Quadratic displacement and hidden-image checks pass',flush=True)
    spectra=spectrum_checks(rng)
    records=[]
    cases=[(2,2,(0,),False,False,False),(2,2,(1,),False,False,False),
           (3,2,(0,),False,False,True),(3,3,(0,2),False,False,False),
           (9,2,(0,),True,False,False),(9,2,(0,),False,True,False)]
    for s,L,where,lower,pure_quad,coupling in cases:
        desc,known,U,V=build_native_case(s,L,rng,where,lower,pure_quad,coupling)
        budget=5 if lower else 2 if pure_quad else 3
        raw_phase=None;induced_rank=None
        if lower:
            # Keep the failed raw lift as a control. A cubic basis change can
            # add a quadratic on U, so the remainder need not have rank len(V).
            flat=[cc.flatten(a) for a in known.centroid_basis]
            generator=cc.compose(known.generator,cc.compose(known.generator,known.generator))
            fixture_field=ds.certify_generator(known.n,known.centroid_basis,flat,echelon(flat),
                                               solve(echelon(flat),cc.flatten(generator)),1)
            image=pd.cubic_imbalance_image(desc[3][0],fixture_field)
            difference=independent_product_anf(known.n,U)^independent_product_anf(known.n,image)
            assert max((m.bit_count() for m in difference),default=0)<=2
            raw_phase=list(desc[3][0])
            induced_rank=len(echelon(pd.quadratic_matrix(
                difference^independent_product_anf(known.n,V),known.n)))
            assert induced_rank==4 and 7*induced_rank>known.n
            desc[3][0]=sorted(set(desc[3][0])^difference)
        native=cc.compile_native(desc)
        if lower:
            anchor=desc[3][1];centroid=cc.centroid(desc[1],anchor)
            span=echelon([cc.flatten(a) for a in centroid])
            bad=solve(span,cc.flatten(known.generator))
            good_matrix=cc.compose(known.generator,cc.compose(known.generator,known.generator))
            good=solve(span,cc.flatten(good_matrix))
            class Tape:
                def __init__(self,values):self.values=iter(values);self.bits=0
                def getrandbits(self,k):self.bits+=k;return next(self.values,0)
            tape=Tape([bad,good])
            result,details=pd.reduce_native(native['qubits'],native['gates'],native['basis'],
                                            native['output'],budget,1,tape)
            assert result is not None,details
            assert details['total_trials']==2 and details['random_bits']==18
            assert details['rejected'].get('dependent_cubic_translate')==1
            bump('bad_phase_generator_then_success')
            E=result['structure'];rec=cc.PhaseReconstructor(E)
            image=pd.cubic_imbalance_image(desc[3][0],E)
            assert span_equal(image,U) and pd.full_fit(desc[3][0],rec,image) is None
            bump('cubic_only_full_phase_counterexample')
            raw_result,raw_reason=pd.recover_phase(raw_phase,E,rec,budget)
            assert raw_result is None and raw_reason.startswith('quadratic_')
            bump('basis_induced_quadratic_rank_growth_control')
            assert result['phase_parts'][0]['quadratic_rank']==2
            assert span_equal(result['phase_parts'][0]['columns'],U+V)
            refused,failure=pd.discover_source(desc,4,1,Tape([good]*3))
            assert refused is None and failure['random_bits']<=3*s*L
            assert failure['rejected'].get('phase_union_rank_budget')==3
            bump('combined_phase_rank_budget_refusal')
            refused,failure=pd.discover_source(desc,budget,2,Tape([]))
            assert refused is None and failure['random_bits']<=3*s*L*2
            assert failure['total_trials']==6
            bump('bounded_zero_tape_phase_failure')
        else:
            result,details=pd.reduce_native(native['qubits'],native['gates'],native['basis'],
                                            native['output'],budget,8,rng)
            assert result is not None,details
        assert details['random_bits']<=3*s*L*8
        if 0 in where and not pure_quad:
            assert details['anchor_index']==1
            bump('later_clean_anchor_discoveries')
        if pure_quad:
            part=result['phase_parts'][0]
            assert part['cubic_rank']==0 and part['quadratic_rank']==2
            assert span_equal(part['columns'],V)
            bump('pure_quadratic_phase_recovery')
        for i,part in enumerate(result['phase_parts']):
            D=result['structure'];K=D.field
            points=range(1 << D.n) if D.n<=9 else [rng.randrange(1 << D.n) for _ in range(64)]
            for x in points:
                selector=sum(((u&x).bit_count()&1) << j for j,u in enumerate(part['columns']))
                actual=K.trace(ff.evaluate_mv(K,part['field_poly'],D.coordinates(x)))^cc.anf_evaluate(part['residual'],selector)
                assert actual==cc.anf_evaluate(desc[3][i],x)
                bump('whole_phase_value_checks')
        branches=list(pd.cubic_branches(result))
        t=result['selector_bits'];r=result['residual_rank'];D=result['structure'];K=D.field;k=result['k']
        assert all(b['degree']<=3 for _,_,b in branches)
        assert sum(w for _,w,_ in branches)==(-1 if 0 in result['selector'] else 1)*(1 << t)
        trials=8 if s==9 and lower else 16 if L==3 else 32
        for _ in range(trials):
            physical=[rng.randrange(1 << D.n) for _ in range(k)]
            x=tuple(a for value in physical for a in D.coordinates(value))
            selector=sum(((u&value).bit_count()&1) << (v*r+j)
                         for v,value in enumerate(physical) for j,u in enumerate(result['columns']))
            original=boolean_output_phase(desc,physical)
            assert original==K.trace(ff.evaluate_mv(K,result['base']['phase'],x))^cc.anf_evaluate(result['selector'],selector)
            weighted=sum(w*(-1 if K.trace(ff.evaluate_mv(K,b['phase'],x)) else 1) for _,w,b in branches)
            assert weighted==(-1 if original else 1)*(1 << t)
            bump('complete_output_pointwise_identities')
        counts=[];probability=None
        if s<=3 and L==2:
            print('Complete finite separated phase-defect counts:',D.n,coupling,len(branches),flush=True)
            shim=dict(result,correction=dict(rank=r))
            counts=complete_two_layer_counts(shim,branches)
            probability,signed=pd.combine_counts(result,counts)
            assert probability==fast_independent_probability(desc)
            bump('complete_separated_cubic_counts',len(counts))
            bump('complete_phase_defect_output_counts')
            for precision in (3,128,8192):
                rounded=rc.round_probability(probability,precision)
                assert 0<=probability-rounded<Fraction(1,1 << precision)
                bump('phase_defect_precision_cases')
            if s==2 and where==(0,):
                gates=[('X',j) for j in range(D.n) if native['basis'] >> j & 1]+native['gates']
                state,h,_=sparse_native(gates);p=ZERO
                for x,a in state.items():
                    if x >> native['output'] & 1:p=add(p,mul(a,conjugate(a)))
                assert scale(p,Fraction(1,1 << h))==scale(ONE,probability)
                bump('independent_native_phase_defect_output')
        elif D.n<=9:probability=fast_independent_probability(desc)
        records.append(dict(n=D.n,s=s,layers=L,budget=budget,where=where,lower_quadratic=lower,
                            pure_quadratic=pure_quad,coupling=coupling,native_records=len(native['gates']),
                            raw_lift_defect_polar_rank=induced_rank,
                            raw_lift_refusal=raw_reason if lower else None,
                            source_bits=native['source_bits'],discovery=details,residual_rank=r,
                            selector_bits=t,active_bits=len(result['active_bits']),
                            residual_degree=result['residual_degree'],spectrum_method=result['spectrum_method'],
                            residual_constant=int(0 in result['selector']),
                            phase_methods=[dict(method=p['method'],cubic_rank=p['cubic_rank'],
                                                quadratic_rank=p['quadratic_rank'],rank=len(p['columns']))
                                           for p in result['phase_parts']],
                            cubic_counts=len(branches),count_variables=6*L-2,
                            count_magnitudes=sorted({abs(w) for _,w,_ in branches}),
                            complete_counts=counts,probability=str(probability) if probability is not None else None))
        print('Native full-phase discovery passes:',D.n,L,[p['method'] for p in result['phase_parts']],flush=True)
    # Algebraic count identity with G(0)=1; not a claimed native circuit.
    desc,D,U,H=build_source(2,3,1,rng,'independent_coordinates',False)
    synthetic=dict(field=D.field,k=1,residual_rank=3,selector_bits=3,
                   selector={0,7},residual_degree=3,active_bits=(0,1,2),
                   ell=[D.linear_coefficients(u) for u in U],
                   base=dict(field=D.field,phase={},field_variables=3,count_variables=4,
                             denominator=1 << D.n,layers=1,padic_bits=5*D.s))
    branches=list(pd.cubic_branches(synthetic))
    counts=[(w,complete_count(D.field,b['phase'],3)) for _,w,b in branches]
    p,signed=pd.combine_counts(synthetic,counts)
    assert p==Fraction(7,8) and signed==-48 and sum(w for _,w,_ in branches)==-8
    bump('nonzero_constant_exact_count_identity')
    paths=['src/phase_defect_tensors.py','src/check_phase_defect_tensors.py',
           'src/field_defect_subspaces.py','src/check_field_defect_subspaces.py',
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
    prior=ROOT/'artifacts/s173-field-defect-subspace-checks.json'
    receipt=dict(status='pass',seed=1730507,counts=COUNTS,quadratic_matrix_cases=matrix_records,
                 spectra=spectra,native_sources=records,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Complete low-dimensional cubic and quadratic phase-defect recovery, source anchor search and exact output transfer. Complete finite separated counts only on the stated n<=9 two-layer sources. Large-field tests are matrix identities or pointwise native checks; no p-adic implementation or universal compiler.')
    target=ROOT/'artifacts/s173-phase-defect-tensor-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
