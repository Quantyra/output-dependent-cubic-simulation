"""Exact block-cut invariant, source-cost and native-family checks."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import gaussian_block_cuts as bc
import gaussian_interface_transfer as it
import gaussian_boundary_factorization as gb
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_gaussian_boundary_factorization import graph_source
from check_gaussian_interface_transfer import dense_prefix_reference
from check_cubic_linear_factors import terminal
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def independent_table_values(source,certificate):
    full=source['decomposition']['phase'];width=len(certificate['matrix'])
    tables=list(certificate['leaves'].values())+certificate['prefixes']
    for table in tables:
        cut=table['cut'];mask=cut['mask'];positions=list(pd.bits(mask))
        if len(positions)>12:continue
        internal={term for term in full if term and not term&~mask}
        crossing=[term for term in full if term.bit_count()==2 and term&mask and term&~mask]
        expected={}
        for word in range(1 << len(positions)):
            x=sum(1 << positions[j] for j in pd.bits(word));signature=0
            for term in crossing:
                inside=term&mask
                if x&inside:signature ^= term&~mask
            expected[signature]=expected.get(signature,0)+(-1)**cc.anf_evaluate(internal,x)
        actual={cc.action(cut['basis'],s):value for s,value in enumerate(table['values'])}
        assert expected==actual
        bump('independent_partial_signed_entries',len(expected))
        bump('independent_partial_assignments',1 << len(positions))
        for s in range(1 << cut['rank']):
            x=cc.action(cut['lifts'],s);actual_signature=0
            for term in crossing:
                if x&(term&mask):actual_signature ^= term&~mask
            assert not x&~mask and actual_signature==cc.action(cut['basis'],s)
            bump('independent_signature_representatives')
        if any(value==0 for value in table['values']):bump('retained_zero_signature_tables')
        if any(value<0 for value in table['values']):bump('negative_signed_tables')
    assert certificate['stats']['peak_integer_bits']<=width+1


def residual_checks(rng):
    records=[]
    # Arbitrary complete couplings/lower terms, with independent whole-sum reference.
    for g in (3,4):
        n=3*g
        for _ in range(6):
            f={7 << (3*j) for j in range(g)}^{m for m in cc.anf_masks(n,2) if rng.randrange(3)==0}
            expected=brute(f,n);P=hidden_basis(n,rng);offset=rng.getrandbits(n)
            changed=pd.substitute_boolean(f,qr.affine_forms(offset,P,n))
            source=gb.discover(changed,n);certificate=bc.contract(source,4,8)
            assert certificate['accepted'] and certificate['value']==expected
            independent_table_values(source,certificate)
            assert certificate['stats']['rank_candidates']==g*(g+1)//2
            bump('hidden_affine_arbitrary_graph_sums')
    # Dense native-derived terminal, globally hidden and affinely shifted.
    desc=dense_source(1,4);leaf=terminal(qr.reduce_source(desc)['tree'])
    expected=cb.evaluate_controls(gb.discover(leaf['phase'],leaf['n'])['joint'])
    for _ in range(8):
        P=hidden_basis(leaf['n'],rng);offset=rng.getrandbits(leaf['n'])
        changed=pd.substitute_boolean(leaf['phase'],qr.affine_forms(offset,P,leaf['n']))
        source=gb.discover(changed,leaf['n']);certificate=bc.contract(source)
        assert certificate['accepted'] and certificate['value']==expected
        assert certificate['plan']['ranks']==(2,2,2,0)
        independent_table_values(source,certificate)
        bump('dense_native_residual_affine_recoveries')
        records.append(dict(value=expected,ranks=certificate['plan']['ranks'],stats=certificate['stats']))
    # Earlier affine and zero-total traps remain correct under the general join.
    traps=[(8,{7,25,6,10,20,1}^{7 << 5}^{1|(1 << 5)},16),
           (6,{7,4,56,32,18},-4),(6,{7,2,56,18},20)]
    mixed=field_phase(2,7)^{m << 6 for m in (7,25)}^{(1 << 2)|(1 << 7),1,0}
    traps.append((11,mixed,-112))
    for n,f,value in traps:
        source=gb.discover(f,n);certificate=bc.contract(source)
        assert certificate['accepted'] and certificate['value']==brute(f,n)==value
        independent_table_values(source,certificate);bump('retained_affine_zero_and_mixed_traps')
    # A new high-degree join evaluates to zero; its whole scalar cannot be guessed
    # by discarding any locally zero total before the coupling is considered.
    zero={7,25,6,10,20,1};edges=[(0,1),(0,2),(0,3),(1,2),(1,3)]
    f={m << (5*j) for j in range(4) for m in zero}^{(1 << (5*a))|(1 << (5*b)) for a,b in edges}^{1}
    source=gb.discover(f,20);certificate=bc.contract(source)
    assert not source['accepted'] and not it.transfer(source)['accepted']
    local=[zero^{1}]+[zero]*3;branch=[]
    for phase in local:
        branch.append([sum((-1)**cc.anf_evaluate(phase,t|(x << 1)) for x in range(16)) for t in range(2)])
    expected=sum((-1)**sum(((word >> a)&1)*((word >> b)&1) for a,b in edges)*
                 __import__('math').prod(branch[j][(word >> j)&1] for j in range(4)) for word in range(16))
    assert certificate['value']==expected==0
    independent_table_values(source,certificate);bump('new_high_degree_zero_join')
    field=field_phase(3,11);tree,detail=bc.compile_sum(f^{m << 20 for m in field},29)
    assert tree['kind']=='zero' and bc.evaluate_tree(tree)==0
    assert detail['previous']['unsupported_work']==512
    bump('new_join_zero_prunes_unsupported_sibling')
    # Disconnected components and isolated nodes are handled by the same joins.
    f={7,56,448,3584,1|(1 << 3),0};s=gb.discover(f,12);c=bc.contract(s)
    assert c['value']==brute(f,12)
    independent_table_values(s,c);bump('disconnected_cut_joins')
    return records


def dense_source(k,g,flip=False,edges=None):
    desc,_=graph_source(k,g,'cycle_uv',flip);w=2*k+1
    if edges is None:edges=list(combinations(range(g),2))
    desc[3][0]=sorted(set(desc[3][0])^{(1 << (w*j+1))|(1 << (w*((j+1)%g)+2)) for j in range(g)}
                       ^{(1 << (w*a+1))|(1 << (w*b+2)) for a,b in edges})
    return desc


def check_envelope(p,k,g):
    assert (1-2*p)**2 <= (1-Fraction(1,4**k))**g
    bump('native_trace_envelope_checks')


def pair_envelope_reference(source):
    """Finite reference for the next mechanism, not an approximate source reader."""
    local,_,boundaries=gb.split_phase(source['decomposition'])
    if any(len(block)>5 for block in source['decomposition']['blocks']):return None
    factors=[];bound=1;trials=0
    from cubic_linear_factors import quadratic_value
    for phase,block,rows in zip(local,source['decomposition']['blocks'],boundaries):
        width=len(block);kernel=tuple(cc.nullspace(rows,width));best=(1 << width,0)
        for word in range(1,1 << len(kernel)):
            direction=cc.action(kernel,word);pivot=(direction&-direction).bit_length()-1
            columns=tuple(1 << j for j in range(width) if j!=pivot)
            first=pd.substitute_boolean(phase,qr.affine_forms(0,columns,width))
            second=pd.substitute_boolean(phase,qr.affine_forms(direction,columns,width))
            delta=first^second
            assert all(term.bit_count()<=2 for term in delta)
            mass=(1 << (width-1))+quadratic_value(delta,width-1)
            independent=sum(abs((-1)**cc.anf_evaluate(phase,cc.action(columns,z))+
                                (-1)**cc.anf_evaluate(phase,direction^cc.action(columns,z)))
                            for z in range(1 << (width-1)))
            assert mass==independent and all((row&direction).bit_count()%2==0 for row in rows)
            trials+=1;bump('independent_pair_mass_counts');best=min(best,(mass,direction))
        bound*=best[0];factors.append(dict(width=width,kernel_dimension=len(kernel),mass=best[0],direction=best[1]))
    return dict(bound=bound,factors=factors,trials=trials)

def native_checks(rng):
    records=[]
    cases=[(4,1,False,False),(5,1,True,False),(6,2,False,False),
           (8,1,False,False),(12,1,True,False),(24,1,False,False),(32,1,True,False),
           (4,3,False,False),(6,3,True,False),
           (4,1,True,True),(4,2,False,True),(6,1,False,True)]
    for g,k,flip,hidden in cases:
        desc=dense_source(k,g,flip);p=dense_prefix_reference(k,g)
        if flip:p=1-p
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc);result=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        detail=result['block_cut_contraction']
        assert len(detail['certificates'])==1 and not detail['refusals']
        c=detail['certificates'][0]
        assert c['plan']['ranks']==(2,)*(g-1)+(0,)
        assert c['previous_joint_branches']==1 << g and c['local_branches']==2*g
        assert c['stats']['leaf_entries']==16*(g-2)+8 and c['stats']['join_pairs']==64*g-108
        assert c['stats']['rank_candidates']==g*(g+1)//2
        assert result['cost']['work']==1
        for bits in (2,160,4096):
            a=bc.evaluate_source(result,bits)
            assert a['probability']==p and 0<=p-a['rounded']<Fraction(1,1 << bits)
            bump('complete_precision_evaluations')
        for _ in range(10):
            xs=[rng.getrandbits(desc[1]) for _ in range(2*len(desc[3])-1)]
            x=sum(v << (j*desc[1]) for j,v in enumerate(xs))
            assert cc.anf_evaluate(result['phase'],x)==boolean_output_phase(desc,xs)
            bump('original_output_phase_identities')
        if desc[1]<=12:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
            check_native(native,p);bump('literal_native_outputs')
        if g<=6:
            old=it.reduce_source(desc)
            assert it.evaluate_source(old,160)['probability']==p
            bump('completed_previous_joint_comparisons')
        check_envelope(p,k,g);bump('complete_native_dense_outputs')
        pair=None
        if k==1:
            source=detail['retained']['retained']['refusals'][0]
            pair=pair_envelope_reference(source)
            assert pair['bound']<=12**g and abs(1-2*p)<=Fraction(pair['bound'],16**g)
            bump('native_pair_envelope_checks')
        records.append(dict(g=g,k=k,flip=flip,hidden_physical_basis=hidden,n=desc[1],
                            source_bits=native['source_bits'],native_records=len(native['gates']),
                            path_bits=result['physical_bits'],old_joint_branches=str(1 << g),
                            probability=str(p),stats=c['stats'],ranks=c['plan']['ranks'],cost=result['cost'],pair_envelope=pair))
        print('Native dense block cuts:',g,k,hidden,p,c['stats'],flush=True)
    bad=list(native['gates'])+[('Z',0)]
    try:bc.reduce_native(desc[1],bad,desc[4],desc[5])
    except ValueError:bump('modified_native_source_refusal')
    else:raise AssertionError('modified source accepted')
    for term in (1 << 1,(1 << 1)|(1 << 2),1 << 3):
        desc=dense_source(1,4);desc[3][0]=sorted(set(desc[3][0])^{term})
        p=fast_independent_probability(desc)
        native=cc.compile_native(desc);result=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        assert bc.evaluate_source(result,180)['probability']==p
        bump('perturbed_native_outputs')
        if p!=Fraction(259,512):bump('changed_native_probabilities')
    return records


def boundary_checks(rng):
    edges=[(0,2),(0,4),(1,2),(1,3),(1,5),(1,6),(2,5),(3,4),(3,6),(3,7),(5,6),(5,7),(6,7)]
    desc=dense_source(1,8,edges=edges);native=cc.compile_native(desc);boundary_n=desc[1]
    result=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    refusal=result['block_cut_contraction']['refusals'][0]
    assert refusal['reason']=='selected_cut_rank' and refusal['tables_built']==0
    assert refusal['plan']['ranks']==(2,4,6,6,8,6,2,0)
    assert result['cost']['gaussian_sums']==256
    p=bc.evaluate_source(result,160)['probability']
    old=it.reduce_source(desc);assert it.evaluate_source(old,160)['probability']==p
    expanded=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5],4,8)
    assert bc.evaluate_source(expanded,160)['probability']==p and expanded['cost']['work']==1
    bump('native_rank_refusal_and_paid_extension');check_envelope(p,1,8)
    source=result['block_cut_contraction']['retained']['retained']['refusals'][0]
    pair=pair_envelope_reference(source)
    assert pair['bound']<=12**8 and abs(1-2*p)<=Fraction(pair['bound'],16**8)
    bump('native_pair_envelope_checks')
    print('Native cut-rank boundary:',p,refusal['plan']['ranks'],flush=True)
    leaf=terminal(qr.reduce_source(dense_source(1,4))['tree']);s=gb.discover(leaf['phase'],leaf['n'])
    r=bc.contract(s,1,4);assert not r['accepted'] and r['reason']=='leaf_rank' and r['tables_built']==0
    bump('leaf_rank_refusal_before_tables')
    for kind in ('clique','cycle_uv'):
        desc,p0=graph_source(1,6,kind);native=cc.compile_native(desc)
        result=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        assert bc.evaluate_source(result,160)['probability']==p0 and not result['block_cut_contraction']['certificates']
        bump('retained_support_or_cycle_native_output')
    field=field_phase(3,11);tree,detail=bc.compile_sum(field,9)
    assert detail['current']['unsupported_work']==512 and bc.evaluate_tree(tree)==120
    bump('retained_indecomposable_field_boundary')
    from check_quadratic_pushforward_recursion import isotropic_source
    desc,p0=isotropic_source(3,33,rng,True,False);native=cc.compile_native(desc)
    result=bc.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert bc.evaluate_source(result,160)['probability']==p0
    bump('retained_growing_layer_native_output')
    return dict(n=boundary_n,boundary_probability=str(p),selected_ranks=refusal['plan']['ranks'],pair_envelope=pair,
                old_joint_branches=256,extended_stats=expanded['block_cut_contraction']['certificates'][0]['stats'])


def rank_and_envelope_checks(rng):
    # Exact rank counts independently check the elementary factorization bound.
    for h in range(1,5):
        histogram=[0]*(h+1)
        for word in range(1 << (h*h)):
            columns=[(word >> (j*h))&((1 << h)-1) for j in range(h)]
            histogram[len(echelon(columns))]+=1
        for r in range(h//2+1):
            assert sum(histogram[:r+1])<=1 << (2*h*r)
            bump('exact_low_rank_count_bounds')
    # Every balanced block cut exposes an h-by-h fully random upper rectangle.
    for g in (6,12):
        h=g//6;half=g//2
        A=[[int(i<j and rng.getrandbits(1)) for j in range(g)] for i in range(g)]
        C=[0]*(4*g)
        for i in range(g):
            for j in range(i+1,g):
                if A[i][j]:
                    for a,b in ((4*i,4*j+1),(4*i+2,4*j+3)):
                        C[a]^=1 << b;C[b]^=1 << a
        for bits in range(1 << g):
            S=[j for j in range(g) if bits >> j & 1]
            if not g//3<=len(S)<=2*g//3:continue
            outside=[j for j in range(g) if j not in S]
            left=[j for j in S if j<half];right=[j for j in outside if j>=half]
            if min(len(left),len(right))<h:
                left=[j for j in outside if j<half];right=[j for j in S if j>=half]
            assert len(left)>=h and len(right)>=h
            left=left[:h];right=right[:h]
            rect=len(echelon(sum(A[i][j] << z for z,i in enumerate(left)) for j in right))
            first=len(echelon(sum(A[i][j] << z for z,i in enumerate(S)) for j in outside))
            second=len(echelon(sum(A[i][j] << z for z,i in enumerate(outside)) for j in S))
            rank=bc.cut_rank(C,sum(15 << (4*j) for j in S))
            assert rank==2*(first+second) and rank>=2*rect
            bump('balanced_cross_rectangle_extractions')
    for b in (1,2,5,12):
        assert Fraction(3,4)**(3*b)<=Fraction(1,1 << b)
        bump('pair_envelope_threshold_checks')
    # Exact local overlap for the retained trace-norm alternative; no numerical eigensolver.
    for k in range(1,5):
        Q={3 << (2*j) for j in range(k)}
        overlap=Fraction(brute(Q,2*k),1 << (2*k))
        assert overlap==Fraction(1,1 << k)
        rho=1-overlap*overlap
        for b in (1,2,5,12):
            g=2*(4**k)*b
            assert rho**g<=Fraction(1,1 << (2*b))
            bump('trace_envelope_threshold_checks')
        bump('exact_local_overlap_checks')


def main():
    rng=random.Random(1730523)
    residual=residual_checks(rng)
    assert COUNTS.get('retained_zero_signature_tables',0)>0 and COUNTS.get('negative_signed_tables',0)>0
    print('Independent partial sums, representatives, hidden graphs and zero pruning pass',flush=True)
    native=native_checks(rng);boundary=boundary_checks(rng);rank_and_envelope_checks(rng)
    assert COUNTS.get('changed_native_probabilities',0)>0
    prior=ROOT/'artifacts/s173-gaussian-interface-transfer-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/gaussian_block_cuts.py','src/check_gaussian_block_cuts.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730523,counts=COUNTS,hidden_dense_residuals=residual,
                 native_sources=native,cut_boundary=boundary,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-derived signed block cuts remove the dense native fallback at bounded selected ranks. All main native outputs are complete. A random-family rank-count argument limits full structural tables. Local pair envelopes have exact source-derived finite references, but their recursive error-controlled reader is not implemented. A trace-norm alternative remains separately proved. No universal or hard-language claim.')
    target=ROOT/'artifacts/s173-gaussian-block-cut-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
