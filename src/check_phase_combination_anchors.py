"""Independent finite checks for the phase-combination anchor mechanism."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from pathlib import Path
import cubic_centroid_descent as cc
import finite_field_acceptance as ff
import field_defect_subspaces as ds
import rank_one_field_correction as rc
import phase_defect_tensors as pd
import phase_combination_anchors as pa
from finite_field_descent import echelon,solve,xor_sum
from check_field_defect_subspaces import build_source,complete_two_layer_counts,span_equal
from check_phase_defect_tensors import independent_product_anf
from check_cubic_centroid_descent import boolean_output_phase,hidden_basis
from check_frobenius_trace_degree import fast_independent_probability
from check_bordered_rank_fourier import sparse_native
from check_eth_acceptance_transfer import ZERO,ONE,add,mul,conjugate
from quartic_pfaffian_moments import scale

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def search_lemma_checks(rng):
    records=[]
    for m in range(1,7):
        for d in range(min(m-1,3)+1):
            for budget in range(d,m+1):
                for _ in range(4):
                    change=hidden_basis(m,rng) if m>1 else (1,)
                    q=min(m,budget+1);residual=[c&((1 << d)-1) for c in change]
                    clean=[z for z in range(1,1 << q) if cc.action(residual,z)==0]
                    assert clean
                    assert len(clean)==(1 << (q-len(echelon(residual[:q]))))-1
                    assert all(cc.action(change,z) for z in clean)
                    bump('prefix_clean_anchor_cases')
                    # Random-combination success count, with full coefficients.
                    total=sum(cc.action(residual,z)==0 and cc.action(change,z)!=0
                              for z in range(1 << m))
                    assert total==(1 << (m-d))-1
                    assert total*(1 << (d+1))>=1 << m
                    bump('random_combination_probability_checks')
                records.append(dict(span=m,residual_dimension=d,budget=budget,prefix=q,
                                    candidate_limit=(1 << q)-1))
    # In a (d+1)-space each possible one-dimensional clean kernel must be hit.
    for d in range(5):
        q=d+1
        for w in range(1,1 << q):
            pivot=(w&-w).bit_length()-1
            rows=[(1 << j)^(((w >> j)&1) << pivot) for j in range(q) if j!=pivot]
            kernel=[z for z in range(1,1 << q) if all(not ((row&z).bit_count()&1) for row in rows)]
            assert kernel==[w] and len(echelon(rows))==d
            bump('exact_cleanness_hitting_lower_bound_controls')
    return records


def native_source(s,L,rng,kind='common',coupling=False):
    desc,D,U,H=build_source(s,3,L,rng,'independent_coordinates',False)
    if not coupling:desc[2]=list(rc.matrix_add(desc[2],ds.defect_matrix(U,H,D.n)))
    first=independent_product_anf(D.n,U)
    if kind=='two_defects':
        U=U+(cc.action(cc.transpose(D.generator),U[0]),)
        second=independent_product_anf(D.n,(U[0],U[1],U[3]))
        residuals=[first,second,first^second];budget=2
    else:
        residuals=[first]*L;budget=1
    for i,residual in enumerate(residuals):
        coefficient=1 if kind=='no_clean_echo' else (1 << i)
        poly={(1,1,1):coefficient,(1,0,0):rng.randrange(D.field.q),
              (0,1,1):rng.randrange(D.field.q)}
        compatible=set(cc.anf_from_function(D.n,lambda x:D.field.trace(
            ff.evaluate_mv(D.field,poly,D.coordinates(x)))))
        desc[3][i]=sorted(compatible^residual)
    if kind=='clean_echo':
        desc[3]=[desc[3][0],desc[3][1],[],desc[3][1],desc[3][0]]
    if kind=='no_clean_echo':desc[3]=[desc[3][0],[],desc[3][0]]
    return desc,D,U,budget


def verify_original_anchor_refusals(desc,h,rng):
    n=desc[1];s=n//3;tried=set()
    for phase in desc[3]:
        cubic=tuple(m for m in phase if m.bit_count()==3)
        if not cubic or cubic in tried:continue
        tried.add(cubic);basis=cc.centroid(n,cubic)
        if len(basis)==s:
            flat=[cc.flatten(t) for t in basis];span=echelon(flat)
            assert all(ds.certify_generator(n,basis,flat,span,a,1) is None for a in range(1 << s))
            bump('all_original_centroid_elements_nonfield')
        else:bump('original_centroid_dimension_refusals')
    result,details=pd.discover_source(desc,4 if len(desc[3])==3 and n==12 else 3,h,rng)
    assert result is None,details
    bump('old_reader_refused_sources')


class ZeroTape:
    def __init__(self):self.bits=0
    def getrandbits(self,k):self.bits+=k;return 0


def four_form_probe():
    """Next-mechanism lemma only: supplied clean contractions, not recovery."""
    rng=random.Random(1730509);records=[]
    for s in (2,3,4):
        _,D,_,_=build_source(s,3,2,rng,'independent_coordinates',False)
        K=D.field;n=D.n
        phase=cc.anf_from_function(n,lambda x:K.trace(K.mul(
            K.mul(D.coordinates(x)[0],D.coordinates(x)[1]),D.coordinates(x)[2])))
        tensor=pd.cubic_tensor(phase,n)
        vectors=[D.physical(x) for x in [(1,0,0),(0,1,0),(0,0,1),(2,1,0)]]
        forms=[tuple(sum(((tensor[i][j]&v).bit_count()&1) << i for i in range(n))
                     for j in range(n)) for v in vectors]
        def equations(selected):
            for matrix in selected:
                for i in range(n):
                    for j in range(i+1,n):
                        yield (matrix[j] << (n*i))^(matrix[i] << (n*j))
        three=cc.nullspace(equations(forms[:3]),n*n)
        four=cc.nullspace(equations(forms),n*n)
        assert len(three)==s*(s+1)//2
        assert span_equal(four,[cc.flatten(t) for t in D.centroid_basis])
        bump('supplied_clean_four_contraction_lemma_checks')
        records.append(dict(s=s,three_form_dimension=len(three),four_form_dimension=len(four),
                            scope='supplied clean forms; no corrupted-source discovery claim'))
    return records


def main():
    rng=random.Random(1730508)
    abstract=search_lemma_checks(rng)
    print('Prefix search and exact-cleanness boundary checks pass',flush=True)
    records=[]
    cases=[(2,2,'common',False),(3,2,'common',True),(3,3,'common',False),
           (4,3,'two_defects',False),(9,2,'common',False),(2,2,'clean_echo',False)]
    for s,L,kind,coupling in cases:
        desc,known,U,d=native_source(s,L,rng,kind,coupling)
        L=len(desc[3]);R=len(U)
        verify_original_anchor_refusals(desc,1,rng)
        native=cc.compile_native(desc)
        result,details=pa.reduce_native(native['qubits'],native['gates'],native['basis'],
                                       native['output'],R,8,rng,d)
        assert result is not None,details
        assert details['anchor_mask'].bit_count()>=2
        assert details['random_bits']<=3*8*s*details['candidate_limit']
        assert details['observed_defect_span_dimension']==d
        assert details['prefix_dimension']==min(details['tensor_span_dimension'],d+1)
        basis=pa.source_tensor_basis(desc[3]);seen=set()
        for ordinal,mask,anchor in pa.anchor_candidates(basis,details['prefix_dimension']):
            expected=set()
            for i,phase in enumerate(desc[3]):
                if mask >> i & 1:expected ^= {m for m in phase if m.bit_count()==3}
            assert expected==set(anchor) and anchor not in seen
            seen.add(anchor);bump('source_combination_and_gray_identity_checks')
        if kind=='two_defects':
            assert details['anchor_mask']==7 and details['anchor_ordinal']==5
            bump('three_phase_clean_anchor_discoveries')
        else:
            assert details['anchor_mask']==3
            bump('pair_cancellation_anchor_discoveries')
        if details['prefix_dimension']<details['tensor_span_dimension']:
            bump('strict_prefix_search_savings')
        D=result['structure'];K=D.field;r=result['residual_rank'];k=result['k']
        for i,part in enumerate(result['phase_parts']):
            points=range(1 << D.n) if D.n<=9 else [rng.randrange(1 << D.n) for _ in range(32)]
            for x in points:
                bits=sum(((u&x).bit_count()&1) << j for j,u in enumerate(part['columns']))
                actual=K.trace(ff.evaluate_mv(K,part['field_poly'],D.coordinates(x)))^cc.anf_evaluate(part['residual'],bits)
                assert actual==cc.anf_evaluate(desc[3][i],x)
                bump('full_original_phase_checks')
        for _ in range(16):
            physical=[rng.randrange(1 << D.n) for _ in range(k)]
            x=tuple(a for v in physical for a in D.coordinates(v))
            bits=sum(((u&v).bit_count()&1) << (j*r+i)
                     for j,v in enumerate(physical) for i,u in enumerate(result['columns']))
            actual=K.trace(ff.evaluate_mv(K,result['base']['phase'],x))^cc.anf_evaluate(result['selector'],bits)
            assert actual==boolean_output_phase(desc,physical)
            bump('full_original_output_identities')
        counts=[];probability=None;branch_count=None
        if L==2:
            branches=list(pd.cubic_branches(result));branch_count=len(branches)
            assert all(branch['degree']<=3 for _,_,branch in branches)
            if s<=3:
                print('Exact finite counts for discovered combination:',D.n,len(branches),flush=True)
                counts=complete_two_layer_counts(dict(result,correction=dict(rank=r)),branches)
                probability,signed=pd.combine_counts(result,counts)
                assert probability==fast_independent_probability(desc)
                bump('complete_combination_cubic_counts',len(counts))
                bump('complete_combination_output_counts')
                for b in (4,192,4096):
                    assert 0<=probability-rc.round_probability(probability,b)<Fraction(1,1 << b)
                    bump('combination_precision_cases')
                if s==2:
                    gates=[('X',j) for j in range(D.n) if native['basis'] >> j & 1]+native['gates']
                    state,h,_=sparse_native(gates);p=ZERO
                    for x,a in state.items():
                        if x >> native['output'] & 1:p=add(p,mul(a,conjugate(a)))
                    assert scale(p,Fraction(1,1 << h))==scale(ONE,probability)
                    bump('independent_native_combination_output')
        elif D.n<=12:probability=fast_independent_probability(desc)
        if kind=='clean_echo':
            assert probability==((desc[4] >> desc[5])&1)
            flipped=list(desc);flipped[4] ^= 1 << desc[5]
            assert fast_independent_probability(flipped)==1-probability
            bump('clean_combination_promised_echo_outputs',2)
        if s==3 and kind=='common' and L==2:
            failed,why=pa.discover_source(desc,R,2,ZeroTape(),d)
            assert failed is None and why['random_bits']<=3*2*s*why['candidate_limit']
            assert why['total_trials']==6
            bump('bounded_zero_tape_combination_failure')
            failed,why=pa.discover_source(desc,R,2,rng,0)
            assert failed is None and why['candidate_limit']==1
            bump('insufficient_span_budget_failure')
            full,more=pa.discover_source(desc,R,3,rng)
            assert full is not None and more['candidate_limit']==3
            bump('automatic_span_budget_success')
            altered=list(native['gates'])+[('Z',0)]
            try:pa.reduce_native(native['qubits'],altered,native['basis'],native['output'],R,1,rng,d)
            except ValueError:bump('altered_native_source_refusal')
            else:raise AssertionError('altered original source accepted')
        records.append(dict(n=D.n,s=s,layers=L,kind=kind,coupling=coupling,
                            source_bits=native['source_bits'],native_records=len(native['gates']),
                            rank_budget=R,discovery=details,residual_rank=r,
                            selector_bits=result['selector_bits'],active_bits=len(result['active_bits']),
                            count_variables=6*L-2,enumerated_branches=branch_count,
                            complete_counts=counts,probability=str(probability) if probability is not None else None))
        print('Original source verified through a combination:',D.n,L,details['anchor_mask'],flush=True)
    # No nonzero clean combination exists in this one-dimensional tensor span.
    desc,D,U,d=native_source(3,3,rng,'no_clean_echo')
    assert len(pa.source_tensor_basis(desc[3])['columns'])==1
    assert len(cc.centroid(D.n,desc[3][0]))==1
    for value in (0,1):
        desc[4]=(desc[4]&~(1 << desc[5]))|(value << desc[5])
        result,details=pa.discover_source(desc,3,3,rng)
        assert result is None and details['candidate_limit']==1 and details['total_trials']==0
        assert fast_independent_probability(desc)==value
        bump('no_clean_combination_easy_echo_boundaries')
    contractions=four_form_probe()
    prior=ROOT/'artifacts/s173-phase-defect-tensor-checks.json'
    old=json.loads(prior.read_text())
    paths=['src/phase_combination_anchors.py','src/check_phase_combination_anchors.py']+list(old['hashes'])
    hashes={}
    for path in paths:
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
    receipt=dict(status='pass',seed=1730508,counts=COUNTS,abstract_prefix_cases=abstract,
                 next_mechanism_clean_contraction_cases=contractions,
                 native_sources=records,no_clean_combination=dict(span_dimension=1,residual_dimension=1,
                    centroid_dimension=1,candidate_limit=1,outputs=[0,1],scope='easy echo, no hardness claim'),
                 hashes=hashes,prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Deterministic prefix anchor search and full original-source verification. Finite complete counts only on n<=9 two-layer sources. Larger/later-layer controls test discovery and pointwise output identity; no implemented p-adic backend.')
    target=ROOT/'artifacts/s173-phase-combination-anchor-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
