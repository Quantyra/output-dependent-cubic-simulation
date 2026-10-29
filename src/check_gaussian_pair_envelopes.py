"""Independent pair-mass, recursive error, threshold and native-source checks."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from unittest.mock import patch
import gaussian_pair_envelopes as pe
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import gaussian_boundary_factorization as gb
import gaussian_block_cuts as bc
import phase_defect_tensors as pd
from check_gaussian_block_cuts import dense_source
from check_gaussian_interface_transfer import dense_prefix_reference
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_cubic_linear_factors import terminal
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def direct_mass(phase,width,direction):
    pivot=(direction&-direction).bit_length()-1
    return sum(abs((-1)**cc.anf_evaluate(phase,x)+(-1)**cc.anf_evaluate(phase,x^direction))
               for x in range(1 << width) if not x >> pivot & 1)


def local_checks(rng):
    for width in (1,2,3):
        monomials=tuple(cc.anf_masks(width,3))
        for coefficients in range(1 << len(monomials)):
            phase={term for j,term in enumerate(monomials) if coefficients >> j & 1}
            for direction in range(1,1 << width):
                assert pe.pair_mass(phase,width,direction)==direct_mass(phase,width,direction)
                bump('exhaustive_local_pair_masses')
    for width in (4,5,6):
        for _ in range(8):
            phase={term for term in cc.anf_masks(width,3) if rng.getrandbits(1)}
            rows=tuple(rng.getrandbits(width) for _ in range(width//2))
            first=pe.block_envelope(phase,width,rows,6)
            eligible=[v for v in range(1,1 << width) if all((v&r).bit_count()%2==0 for r in rows)]
            expected=min([1 << width]+[direct_mass(phase,width,v) for v in eligible])
            assert first['bound']==expected and first['trials']==len(eligible)
            P=hidden_basis(width,rng);origin=rng.getrandbits(width)
            transformed=pd.substitute_boolean(phase,qr.affine_forms(origin,P,width))
            changed_rows=tuple(sum(((r&c).bit_count()%2) << j for j,c in enumerate(P)) for r in rows)
            second=pe.block_envelope(transformed,width,changed_rows,6)
            assert second['bound']==first['bound'] and second['trials']==first['trials']
            bump('independent_boundary_kernel_minima')
            bump('affine_invariant_pair_minima')
    # General pair counting applies even when the older local-control search refuses.
    field=field_phase(3,11);tree,c=pe.compile_sum(field,9)
    assert tree['kind']=='terminal' and c['capped_blocks']==1 and c['pair_trials']==0
    tree2,d=pe.compile_sum(field,9,max_kernel_dimension=9)
    assert d['pair_trials']==511 and not d['capped_blocks'] and tree2['bound']<=tree['bound']
    assert abs(brute(field,9))<=tree2['bound']
    assert pe.exact_tree(tree)[0]==pe.exact_tree(tree2)[0]==120
    bump('unsupported_field_paid_cap_extension')
    for cap in (-1,True):
        try:pe.compile_sum(field,9,max_kernel_dimension=cap)
        except ValueError:bump('invalid_cap_refusals')
        else:raise AssertionError('invalid cap accepted')


def recursive_checks(rng):
    fixtures=[(0,set()),(0,{0}),(2,{3}),(2,{1,3,0}),
              (10,{7,56,1 << 9,0}),
              (12,{7,56,448,3584,1|(1 << 3),0}),
              (11,field_phase(3,11)^{(1 << 9)|(1 << 10),0})]
    for n in range(3,11):
        for _ in range(5):
            fixtures.append((n,{m for m in cc.anf_masks(n,3) if rng.randrange(6)==0}))
    kinds=set()
    for n,phase in fixtures:
        expected=brute(phase,n);tree,detail=pe.compile_sum(phase,n)
        value,stats=pe.exact_tree(tree)
        assert value==expected and abs(expected)<=tree['bound']<=1 << n
        pending=[tree]
        while pending:
            node=pending.pop();kinds.add(node['kind'])
            assert abs(cb.evaluate_tree(node))<=node['bound']
            bump('recursive_node_envelopes')
            if node['kind']=='product':pending.extend(node['children'])
            elif node['kind']=='push':pending.append(node['child'])
        bump('independent_full_recursive_sums')
    assert {'constant','zero','push','product'}<=kinds,kinds
    # A zero sibling is known before unsupported original-atom enumeration.
    field=field_phase(3,11);tree,_=pe.compile_sum(field^{1 << 9},10)
    with patch.object(cc,'anf_evaluate',side_effect=AssertionError('forbidden point readout')):
        value,stats=pe.exact_tree(tree)
    assert value==0 and stats['point_evaluations']==0 and stats['zero_pruned']==1
    bump('zero_before_unsupported_readout')
    zero={7,25,6,10,20,1};edges=[(0,1),(0,2),(0,3),(1,2),(1,3)]
    phase={m << (5*j) for j in range(4) for m in zero}^{(1 << (5*a))|(1 << (5*b)) for a,b in edges}^{1}
    tree,_=pe.compile_sum(phase^{m << 20 for m in field},29)
    assert tree['bound']>0 and cb.tree_cost(tree)['unsupported_work']==512
    original_evaluate=cc.anf_evaluate
    def no_cubic_points(poly,x):
        assert not any(m.bit_count()==3 for m in poly),'forbidden cubic point readout'
        return original_evaluate(poly,x)
    with patch.object(cc,'anf_evaluate',side_effect=no_cubic_points):
        value,stats=pe.exact_tree(tree)
    assert value==0 and stats['point_evaluations']==0 and stats['cut_accepted']==1
    bump('bounded_cut_zero_prunes_unsupported_sibling')


def check_answer(result,bits,expected=None):
    answer=pe.evaluate_source(result,bits);eps=Fraction(1,1 << bits)
    assert answer['error_bound']<eps and 0<=answer['estimate']<=1
    if expected is not None:
        assert answer['interval'][0]<=expected<=answer['interval'][1]
        assert abs(answer['estimate']-expected)<=answer['error_bound']
        if answer['probability'] is not None:assert answer['probability']==expected
        bump('complete_precision_reference_comparisons')
    if answer['mode']=='envelope':
        assert answer['fallback_work']==0 and answer['stats']=={}
        # A certified result must not invoke any previous exact evaluation backend.
        with patch.object(pe,'exact_tree',side_effect=AssertionError('forbidden exact readout')):
            again=pe.evaluate_source(result,bits)
        assert again==answer
        bump('certified_branches_without_exact_readout')
    return answer


def first_failed_bits(result):
    denbits=result['descriptor'][1]*len(result['descriptor'][3])
    bound=result['tree']['bound'];b=max(1,denbits-bound.bit_length())
    while (bound << b)<(2 << denbits):b+=1
    return b


BOUNDARY_EDGES=[(0,2),(0,4),(1,2),(1,3),(1,5),(1,6),
                (2,5),(3,4),(3,6),(3,7),(5,6),(5,7),(6,7)]


def native_checks(rng):
    records=[]
    # Exact independent references for original native sources and threshold crossings.
    for g,flip,hidden in [(1,False,False),(2,True,False),(4,False,False),
                           (4,True,True),(8,False,False),(24,True,False),(32,False,False)]:
        desc=dense_source(1,g,flip)
        p=dense_prefix_reference(1,g)
        if flip:p=1-p
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc)
        result=pe.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        assert result['tree']['bound']<=48**g
        threshold=first_failed_bits(result)
        answers=[check_answer(result,b,p) for b in sorted({1,max(1,threshold-1),threshold,160,4096})]
        for _ in range(8):
            xs=[rng.getrandbits(desc[1]) for _ in range(3)]
            x=sum(v << (j*desc[1]) for j,v in enumerate(xs))
            assert cc.anf_evaluate(result['phase'],x)==boolean_output_phase(desc,xs)
            bump('original_native_output_phase_identities')
        if desc[1]<=12:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
            check_native(native,p);bump('literal_native_outputs')
        if g==1:
            assert check_answer(result,3,p)['mode']=='exact_fallback'
            bump('strict_error_equality_refusal')
        record=dict(g=g,n=desc[1],hidden=hidden,flip=flip,source_bits=native['source_bits'],
                    native_records=len(native['gates']),path_bits=result['physical_bits'],
                    probability=str(p),root_bound=str(result['tree']['bound']),first_failed_bits=threshold,
                    pair_trials=result['pair_certification']['pair_trials'],
                    precision_modes=[(a['bits'],a['mode']) for a in answers])
        records.append(record);bump('complete_native_reference_sources')
        print('Complete native pair reader:',record,flush=True)
    # Real earlier width refusal: 256 joint sums remain only above the error threshold.
    for flip,hidden in [(False,False),(True,False),(False,True)]:
        desc=dense_source(1,8,flip,BOUNDARY_EDGES)
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc);result=pe.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        p=Fraction(65531,131072)
        if flip:p=1-p
        low=check_answer(result,4,p);high=check_answer(result,6,p)
        assert low['mode']=='envelope' and high['stats']['gaussian_sums']==256
        assert high['stats']['cut_attempts']==1 and high['stats']['cut_accepted']==0
        capped=pe.reduce_source(desc,max_kernel_dimension=0)
        old=check_answer(capped,4,p)
        assert capped['pair_certification']['pair_trials']==0 and old['stats']['gaussian_sums']==256
        bump('native_cut_refusal_escaped_at_finite_precision')
        records.append(dict(kind='high_selected_rank_boundary',flip=flip,hidden=hidden,
                            n=desc[1],source_bits=native['source_bits'],probability=str(p),
                            pair_trials=result['pair_certification']['pair_trials'],
                            root_bound=str(result['tree']['bound']),low_bits=4,exact_stats=high['stats']))
    # Growing arbitrary couplings: complete certified approximate outputs, with no
    # claim of an independently computed exact probability for these large graphs.
    for g in (24,32):
        edges=[(a,b) for a,b in combinations(range(g),2) if rng.getrandbits(1)]
        desc=dense_source(1,g,edges=edges);native=cc.compile_native(desc)
        result=pe.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        certificate=result['pair_certification']
        assert result['tree']['bound']<=48**g and certificate['pair_trials']<=31*g
        bits=10 if g==24 else 14;answer=check_answer(result,bits)
        assert answer['mode']=='envelope'
        pending=[result['tree']];controls=[]
        while pending:
            node=pending.pop()
            if node['kind']=='controls':controls.append(node)
            elif node['kind']=='push':pending.append(node['child'])
            elif node['kind']=='product':pending.extend(node['children'])
        assert len(controls)==1
        source=controls[0]['source'];matrix,masks,_=bc.cross_matrix(source)
        plan=bc.discover_order(matrix,masks)
        assert plan['max_rank']>4 and source['joint_branches']==1 << g
        phases,_,rows=gb.split_phase(source['decomposition'])
        for phase,block,boundary,cert in zip(phases,source['decomposition']['blocks'],rows,
                                          controls[0]['pair_envelope']['blocks']):
            assert len(block)==5 and cert['bound']<=12
            assert direct_mass(phase,5,cert['direction'])==cert['bound']
            bump('large_native_independent_local_certificates')
        for _ in range(12):
            xs=[rng.getrandbits(desc[1]) for _ in range(3)]
            assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
            bump('original_native_output_phase_identities')
        record=dict(kind='large_arbitrary_graph_certificate',g=g,n=desc[1],source_bits=native['source_bits'],
                    native_records=len(native['gates']),bits=bits,estimate=str(answer['estimate']),
                    error_bound=str(answer['error_bound']),root_bound=str(result['tree']['bound']),
                    pair_trials=certificate['pair_trials'],selected_cut_ranks=plan['ranks'],
                    previous_joint_budget=str(1 << g),fallback_work=answer['fallback_work'],
                    reference_scope='Exact local mass and original phase identities; global error follows from the proved recursive certificate. Exact probability not independently evaluated.')
        records.append(record);bump('complete_large_high_rank_certified_sources')
        print('High-rank original-source certificate:',record,flush=True)
    # Affine-hidden terminal minima remain invariant even with arbitrary graph edges.
    desc=dense_source(1,4,edges=[(0,1),(0,2),(1,2),(2,3)])
    leaf=terminal(qr.reduce_source(desc)['tree']);base=pe.terminal_envelope(gb.primitive_blocks(leaf['phase'],leaf['n']))
    for _ in range(5):
        P=hidden_basis(leaf['n'],rng);origin=rng.getrandbits(leaf['n'])
        changed=pd.substitute_boolean(leaf['phase'],qr.affine_forms(origin,P,leaf['n']))
        found=pe.terminal_envelope(gb.primitive_blocks(changed,leaf['n']))
        assert found['bound']==base['bound'] and found['trials']==base['trials']
        bump('native_terminal_affine_envelope_invariance')
    # Auxiliary lower-order perturbations preserve the family guarantee but can change p.
    changed=0
    for term in (1 << 1,(1 << 1)|(1 << 2),1 << 3):
        desc=dense_source(1,4);desc[3][0]=sorted(set(desc[3][0])^{term})
        native=cc.compile_native(desc);result=pe.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        p=fast_independent_probability(desc)
        for bits in (2,160):check_answer(result,bits,p)
        assert result['tree']['bound']<=48**4
        changed+=p!=Fraction(259,512);bump('perturbed_native_probabilities')
    assert changed;bump('changed_probability_controls',changed)
    bad=list(native['gates'])+[('Z',0)]
    try:pe.reduce_native(desc[1],bad,desc[4],desc[5])
    except ValueError:bump('modified_native_source_refusal')
    else:raise AssertionError('modified original source accepted')
    return records


def threshold_checks():
    # Integer decision used by production, and a conservative algebraic exponent.
    for b in range(1,65):
        for g in range(1,3*b+2):
            fail=12**g*(1 << b)>=2*16**g
            if fail:
                # alpha=1/log2(4/3)<5/2 gives an exact integer upper bound.
                assert (1 << (2*g))<=(1 << (5*(b-1)))
                bump('paid_precision_fallback_thresholds')
            else:
                assert Fraction(3,4)**g/2<Fraction(1,1 << b)
                bump('strict_midpoint_thresholds')
    assert 4**5>4*3**5  # (4/3)^(5/2)>2; alpha<5/2.


def main():
    rng=random.Random(1730524)
    local_checks(rng);recursive_checks(rng);threshold_checks()
    print('Local masses, affine invariance, complete recursion and integer thresholds pass',flush=True)
    native=native_checks(rng)
    prior=ROOT/'artifacts/s173-gaussian-block-cut-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/gaussian_pair_envelopes.py','src/check_gaussian_pair_envelopes.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730524,counts=COUNTS,native_sources=native,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Complete deterministic finite-precision native reader with paid pair discovery, recursive bounds, normalization and exact fallback. Narrow-star cost is polynomial in original source and inverse precision independently of cut rank. Large random graphs have certified approximate outputs, not independent exact-probability references. No universal or hard-language claim.')
    target=ROOT/'artifacts/s173-gaussian-pair-envelope-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
