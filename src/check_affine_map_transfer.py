"""Exact map composition, source Gaussian kernels, closure and native precision."""
import ast,hashlib,json,random
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import affine_map_transfer as am
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
import gaussian_interface_transfer as it
from finite_field_descent import echelon
from check_gaussian_block_cuts import dense_source
from check_diagonal_control_sampling import all_aux_graph
from check_gaussian_message_norms import all_aux_cycle,graph_probability
from check_cubic_centroid_controls import transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1];COUNTS={}


def bump(name,n=1):COUNTS[name]=COUNTS.get(name,0)+n


def twisted_cycle(k,g,matrices,flip=False):
    desc=dense_source(k,g,edges=[]);w=2*k+1;terms=set()
    assert len(matrices)==g
    for j,H in enumerate(matrices):
        assert len(H)==k
        for b,column in enumerate(H):
            for a in pd.bits(column):
                terms.add((1 << (w*j+2*a+1))|(1 << (w*((j+1)%g)+2*b+2)))
    desc[3][0]=sorted(set(desc[3][0])^terms)
    if flip:desc[3][1]=sorted(set(desc[3][1])^{1 << i for i in pd.bits(desc[2][0])})
    return desc


def cycle_formula(k,g,matrices):
    product=cc.identity(k)
    for H in matrices:product=cc.compose(cc.inverse(H),product)
    A=product if g%2==0 else cc.compose(product,product)
    rank=len(echelon(v^(1 << j) for j,v in enumerate(A)))
    d=(2 if g%2==0 else 1)*(k-rank)
    return (1-Fraction((-1)**g*((1 << d)-1),1 << (g*(k+1))))/2


def independent_twisted_rank(k,g,matrices):
    """Enumerate only g controls; rank a full 2kg bilinear matrix."""
    total=0
    for word in range(1 << g):
        columns=[0]*(2*k*g)
        for j in range(g):
            for i in range(k):
                for copy in range(2):
                    at=2*k*j+copy*k+i
                    columns[at]^=(1 << (2*k*j+i))|(1 << (2*k*j+k+i))
                    if word >> j&1:columns[at]^=1 << at
            for b,column in enumerate(matrices[j]):
                for a in pd.bits(column):
                    for copy in range(2):
                        columns[2*k*((j+1)%g)+copy*k+b]^=1 << (2*k*j+copy*k+a)
        total+=(-1)**word.bit_count()*(1 << (4*k*g-len(echelon(columns))))
    return (1-Fraction(total,1 << (g*(3*k+1))))/2


def operator_checks(rng):
    for _ in range(72):
        ni,nm,no=[rng.randrange(4) for _ in range(3)]
        def random_key(a,b):
            phase=[m for m in cc.anf_masks(a,2) if m and rng.getrandbits(1)]
            return am.operator_key(a,b,tuple(rng.getrandbits(b) for _ in range(a)),rng.getrandbits(b),phase)[0]
        A=random_key(ni,nm);B=random_key(nm,no);C,sign=am.compose(A,B)
        for u in range(1 << ni):
            for w in range(1 << no):
                expected=sum(am.kernel_value(A,u,v)*am.kernel_value(B,v,w) for v in range(1 << nm))
                assert sign*am.kernel_value(C,u,w)==expected
                bump('independent_dense_map_product_entries')
        square=random_key(ni,ni)
        value,used=am.trace(square)
        assert value==sum(am.kernel_value(square,u,u) for u in range(1 << ni))
        bump('independent_fixed_point_phase_traces')
    # Arbitrary map sums do not have a universal small dictionary.
    records=[]
    for g in range(1,9):
        states={am.identity(g):1}
        for j in range(g):
            shifted=am.operator_key(g,g,cc.identity(g),1 << j,())[0];new={}
            for first,c in states.items():
                for second in (am.identity(g),shifted):
                    key,sign=am.compose(first,second);new[key]=new.get(key,0)+sign*c
            states=new
        assert len(states)==1 << g
        total=sum(c*am.trace(key)[0] for key,c in states.items())
        assert total==1 << g
        records.append(dict(g=g,distinct_maps=len(states),trace=total))
        bump('exponential_map_dictionary_easy_trace_examples')
    return records


def source_kernel_checks(result):
    detail=result['map_transfer']
    source=next(r for r in detail['retained']['refusals'] if 'joint' in r)
    certificate=detail['certificates'][0]
    for component in certificate['components']:
        for local in component['locals']:
            group=source['messages'][local['block']]
            incoming=local['incoming'];outgoing=local['outgoing'];H=local['pairing']
            if len(incoming)>2 or len(outgoing)>2:continue
            for u in range(1 << len(incoming)):
                for v in range(1 << len(outgoing)):
                    expected=0
                    for message in group:
                        for z in range(1 << len(message['kernel'])):
                            x=message['origin']^cc.action(message['kernel'],z)
                            if it.signature(incoming,x)!=u:continue
                            cross=(it.signature(outgoing,x)&cc.action(H,v)).bit_count()%2
                            expected+=(-1)**(cc.anf_evaluate(message['quadratic'],z)^cross)
                    actual=sum(c*am.kernel_value(key,u,v) for key,c in local['operators'].items())
                    assert actual==expected
                    bump('independent_original_local_kernel_entries')
    if max(e['rank'] for e in certificate['interfaces'].values())<=4:
        old=it.transfer(source,4)
        assert old['accepted'] and old['value']==certificate['value']
        bump('independent_old_boundary_table_transfers')


def native_case(k,g,matrices,rng,hidden=False,flip=False,label=None,bits=4096):
    desc=twisted_cycle(k,g,matrices,flip)
    expected=cycle_formula(k,g,matrices)
    if flip:expected=1-expected
    if g<=6:
        rank=independent_twisted_rank(k,g,matrices)
        assert (1-rank if flip else rank)==expected
        bump('independent_full_bilinear_rank_references')
    elif all(tuple(H)==cc.identity(k) for H in matrices):
        rank=graph_probability(k,g,[(j,(j+1)%g) for j in range(g)],all_aux=True)
        assert (1-rank if flip else rank)==expected
        bump('independent_control_rank_cycle_references')
    if hidden:desc=transform_physical(desc,rng)
    native=cc.compile_native(desc)
    result=am.reduce_native(desc[1],native['gates'],desc[4],desc[5],state_cap=3)
    assert result['map_transfer']['certificates'] and not result['map_transfer']['refusals']
    assert not result['cost']['gaussian_sums'] and not result['cost']['unsupported_work']
    with patch.object(cb,'evaluate_controls',side_effect=AssertionError('forbidden exponential control readout')):
        answer=am.evaluate_source(result,bits,max_work=1)
    assert answer['probability']==expected and answer['random_bits']==0
    assert answer['error_bound']<Fraction(1,1 << bits)
    if desc[1]<=15:
        assert fast_independent_probability(desc)==expected
        bump('independent_native_state_outputs')
        if desc[1]<=9:check_native(native,expected);bump('literal_native_gate_outputs')
    for b in (1,2,7,128,4096):
        a=am.evaluate_source(result,b,max_work=1)
        assert a['probability']==expected and 0<=expected-a['rounded']<Fraction(1,1 << b)
        assert a['error_bound']==expected-a['rounded'] and a['failure_probability']==0
        bump('complete_exact_precision_outputs')
    for certificate in result['map_transfer']['certificates']:
        assert certificate['stats']['peak_states']<=3
        assert certificate['stats']['boundary_table_entries']==0
        assert certificate['stats']['map_products']==6*g-6
    if k<=2 and g<=4:source_kernel_checks(result)
    phase,m=qr.original_output_phase(desc)
    for _ in range(8):
        xs=[rng.getrandbits(desc[1]) for _ in range(3)]
        assert cc.anf_evaluate(phase,sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
        bump('original_source_phase_identities')
    record=dict(label=label or f'k{k}_g{g}_hidden{hidden}_flip{flip}',k=k,g=g,n=desc[1],
                source_bits=native['source_bits'],native_records=len(native['gates']),
                probability=str(expected),bits=bits,remaining_work=result['cost']['work'],
                previous_joint_branches=result['map_transfer']['previous']['gaussian_sums'],
                stats=[c['stats'] for c in result['map_transfer']['certificates']],
                twists=[list(H) for H in matrices])
    bump('complete_original_native_exact_outputs');print('Exact map native output:',record,flush=True)
    return record


def boundary_checks(rng):
    d=all_aux_cycle(2,3)
    for cap in (1,2):
        result=am.reduce_source(d,cap)
        assert any(r['reason']=='map_state_cap' for r in result['map_transfer']['refusals'])
        answer=am.evaluate_source(result,200,max_work=1)
        assert answer['mode']=='budget_refused' and answer['probability'] is None
        bump('bounded_map_cap_and_fallback_refusals')
    dense=all_aux_graph(1,4,[(a,b) for a in range(4) for b in range(4) if a!=b])
    result=am.reduce_source(dense,3)
    assert any(r['reason']=='interaction_degree' for r in result['map_transfer']['refusals'])
    assert am.evaluate_source(result,200,max_work=1)['mode']=='budget_refused'
    bump('native_graph_degree_refusal')
    # Rank-deficient edge alignments challenge total-map admission.
    records=[]
    for matrices in (((1,0),(0,2),(1,0)),((1,0),(1,0),(0,2)),((1,0),(0,1),(2,0))):
        desc=twisted_cycle(2,3,matrices)
        result=am.reduce_source(desc,8)
        expected=independent_twisted_rank(2,3,matrices)
        answer=am.evaluate_source(result,80,max_work=32)
        assert answer['probability']==expected==fast_independent_probability(desc)
        reasons=[r['reason'] for r in result['map_transfer']['refusals']]
        records.append(dict(matrices=matrices,probability=str(expected),refusals=reasons,
                            cost=result['cost']))
        bump('singular_edge_original_output_references')
    return records


def main():
    rng=random.Random(1730529);growth=operator_checks(rng)
    print('Independent map products, traces and dictionary-growth boundary pass',flush=True)
    native=[]
    for k,g,hidden,flip,twisted in ((1,3,False,False,False),(1,3,False,True,False),
                                  (2,3,True,False,True),(3,4,False,False,True),
                                  (4,6,False,False,False),(2,12,False,False,False),
                                  (6,5,False,False,False)):
        matrices=[hidden_basis(k,rng) if twisted else cc.identity(k) for _ in range(g)]
        native.append(native_case(k,g,matrices,rng,hidden,flip))
    boundaries=boundary_checks(rng)
    prior=ROOT/'artifacts/s173-affine-control-sampling-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/affine_map_transfer.py','src/check_affine_map_transfer.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730529,counts=COUNTS,native_sources=native,
                 dictionary_growth=growth,singular_edge_references=boundaries,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-derived Gaussian kernels become signed affine quadratic maps. Bounded exact map aggregation removes boundary and joint-control enumeration on admitted sources. Twisted all-auxiliary cycles have at most three prefix maps and complete exact polynomial source/precision cost. General map dictionaries can grow exponentially; total-map and graph gates remain. No universal or hard-language claim.')
    target=ROOT/'artifacts/s173-affine-map-transfer-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
