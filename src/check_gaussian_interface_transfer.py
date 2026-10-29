"""Independent interface-fiber, quotient, native-source and precision checks."""
import ast,hashlib,json,random
from fractions import Fraction
from pathlib import Path
import gaussian_interface_transfer as it
import gaussian_boundary_factorization as gb
import cubic_centroid_controls as cb
import cubic_centroid_descent as cc
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_linear_factors import star_blocks,terminal
from check_gaussian_boundary_factorization import graph_source
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def independent_fibers(source,certificate):
    local,_,_=gb.split_phase(source['decomposition'])
    for j,t in certificate['tables'].items():
        width=len(source['decomposition']['blocks'][j]);rows=t['rows']
        if width>11:continue
        expected=[0]*(1 << len(rows))
        for x in range(1 << width):
            key=sum(((r&x).bit_count()&1) << a for a,r in enumerate(rows))
            expected[key]+=(-1)**cc.anf_evaluate(local[j],x)
        for a,row in enumerate(t['values']):
            for b,value in enumerate(row):
                assert value==expected[a|(b << t['incoming'])]
                bump('independent_signed_interface_values')
        if len(echelon(rows))<len(rows):bump('dependent_endpoint_rows')
        for message,prepared in zip(source['messages'][j],t['prepared']):
            expected=[0]*(1 << len(rows));free=len(message['kernel'])
            for z in range(1 << free):
                x=message['origin']^cc.action(message['kernel'],z)
                expected[it.signature(rows,x)]+=(-1)**cc.anf_evaluate(message['quadratic'],z)
            for s,value in enumerate(expected):
                assert it.message_value(prepared,s)==value
                bump('independent_branch_interface_values')
            if message['value']==0 and any(expected):bump('zero_scalar_nonzero_interface')
            if prepared['signature_origin']:bump('nonzero_affine_signature_origins')
    for (a,b),H in source['edges'].items():
        e=certificate['interfaces'][(a,b)];table=certificate['edge_tables'][(a,b)]
        wa=len(source['decomposition']['blocks'][a]);wb=len(source['decomposition']['blocks'][b])
        if wa+wb>12:continue
        for x in range(1 << wa):
            for y in range(1 << wb):
                u=it.signature(e['left'],x);v=it.signature(e['right'],y)
                assert table[u][v]==(-1)**((x&cc.action(H,y)).bit_count()&1)
                bump('independent_edge_quotient_values')


def residual_checks(rng):
    records=[]
    traps=[(8,{7,25,6,10,20,1}^{7 << 5}^{1|(1 << 5)},16),
           (6,{7,4,56,32,18},-4),(6,{7,2,56,18},20)]
    mixed=field_phase(2,7)^{m << 6 for m in (7,25)}^{(1 << 2)|(1 << 7),1,0}
    traps.append((11,mixed,-112))
    # A chain uses the same control on both sides of its middle block.
    chain={7,56,448,1|(1 << 3),(1 << 3)|(1 << 6),0}
    traps.append((9,chain,brute(chain,9)))
    for n,f,expected in traps:
        source=gb.discover(f,n);cert=it.transfer(source)
        assert cert['accepted'] and cert['value']==brute(f,n)==expected
        independent_fibers(source,cert);bump('exact_cancellation_and_dependency_traps')
        records.append(dict(n=n,value=expected,components=len(cert['components']),stats=cert['stats']))
    # Random local lower terms, arbitrary edge orientations/ranks, affine bases.
    for blocks in (2,3,4):
        n=3*blocks;cubes={7 << (3*j) for j in range(blocks)}
        for trial in range(6):
            f=set(cubes)
            for j in range(blocks):
                f ^= {m << (3*j) for m in cc.anf_masks(3,2) if rng.getrandbits(1)}
            edges=[(j,j+1) for j in range(blocks-1)]
            if blocks>2 and trial%2:edges.append((0,blocks-1))
            for a,b in edges:
                # Every edge has rank at most two, but the local row union may be dependent.
                for _ in range(2):
                    l=rng.randrange(1,8);r=rng.randrange(1,8)
                    f ^= {(1 << (3*a+i))|(1 << (3*b+j)) for i in pd.bits(l) for j in pd.bits(r)}
            if trial%3==0:f ^= {0}
            expected=brute(f,n);P=hidden_basis(n,rng);offset=rng.getrandbits(n)
            changed=pd.substitute_boolean(f,qr.affine_forms(offset,P,n))
            source=gb.discover(changed,n);cert=it.transfer(source)
            assert cert['accepted'] and cert['value']==expected
            independent_fibers(source,cert)
            assert cert['stats']['peak_integer_bits']<=n+1
            bump('hidden_affine_random_path_cycle_sums')
    # Former affine refusals on a native-derived terminal now contract.
    desc,_=star_blocks(1,3);leaf=terminal(qr.reduce_source(desc)['tree'])
    base=leaf['phase'];n=leaf['n'];expected=brute(base,n)
    for _ in range(8):
        P=hidden_basis(n,rng);offset=rng.getrandbits(n)
        changed=pd.substitute_boolean(base,qr.affine_forms(offset,P,n))
        source=gb.discover(changed,n);cert=it.transfer(source)
        assert cert['accepted'] and cert['value']==expected
        independent_fibers(source,cert);bump('native_residual_affine_transfers')
    # Disconnected components and isolated blocks in the transfer invariant itself.
    f={7,56,448,3584,1|(1 << 3),0};source=gb.discover(f,12);cert=it.transfer(source)
    assert cert['accepted'] and len(cert['components'])==3 and cert['value']==brute(f,12)
    independent_fibers(source,cert);bump('disconnected_and_isolated_components')
    return records


def path_source(k,g,flip=False):
    desc,_=graph_source(k,g,'cycle_uv',flip);d=2*k+1
    desc[3][0]=sorted(set(desc[3][0])^{(1 << (d*(g-1)+1))|(1 << 2)})
    return desc


def family_reference(k,g,cycle):
    A=8**(k-1);B=4**(k-1)
    W=[[(-1)**((u.bit_count()*v.bit_count())&1)*(A-B*(-1)**((u&v).bit_count()&1))
        for u in range(4)] for v in range(4)]
    E=[[(-1)**((u&v).bit_count()&1) for v in range(4)] for u in range(4)]
    def mm(a,b):return [[sum(a[i][j]*b[j][h] for j in range(4)) for h in range(4)] for i in range(4)]
    power=[[int(i==j) for j in range(4)] for i in range(4)]
    for j in range(g):
        power=mm(power,W)
        if cycle or j+1<g:power=mm(power,E)
    Z=sum(power[i][i] for i in range(4)) if cycle else sum(map(sum,power))
    if cycle:
        assert Z==4**g*((A-B)**g+B**g+2*(-B)**g)
    bump('independent_supplied_family_matrix_references')
    return (1-Fraction(Z,1 << (g*(3*k+1))))/2


def native_checks(rng):
    records=[]
    cases=[(3,1,True,False,False),(4,1,True,True,False),(5,2,True,False,False),
           (6,2,True,False,False),(12,1,True,False,False),(24,1,True,True,False),
           (32,1,True,False,False),(3,3,True,True,False),(6,3,True,False,False),
           (3,1,False,False,False),(12,1,False,True,False),
           (3,1,True,True,True),(4,2,True,False,True),(3,2,False,False,True)]
    for g,k,cycle,flip,hidden in cases:
        desc=graph_source(k,g,'cycle_uv',flip)[0] if cycle else path_source(k,g,flip)
        p=family_reference(k,g,cycle)
        if flip:p=1-p
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc)
        result=it.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        detail=result['interface_transfer']
        assert len(detail['certificates'])==1 and not detail['refusals']
        cert=detail['certificates'][0]
        assert cert['previous_joint_branches']==1 << g
        assert cert['max_rank']==2 and cert['local_branches']==2*g
        assert result['cost']['work']==1
        assert cert['stats']['interface_entries']==16*g if cycle else cert['stats']['interface_entries']==16*(g-2)+8
        assert cert['stats']['peak_integer_bits']<=result['physical_bits']+1
        for bits in (2,160,4096):
            answer=it.evaluate_source(result,bits)
            assert answer['probability']==p and 0<=p-answer['rounded']<Fraction(1,1 << bits)
            bump('complete_precision_evaluations')
        for _ in range(10):
            xs=[rng.getrandbits(desc[1]) for _ in range(2*len(desc[3])-1)]
            x=sum(v << (j*desc[1]) for j,v in enumerate(xs))
            assert cc.anf_evaluate(result['phase'],x)==boolean_output_phase(desc,xs)
            bump('original_output_phase_identities')
        if desc[1]<=12:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
        if desc[1]<=9:check_native(native,p);bump('literal_native_outputs')
        if g<=4:
            old=gb.reduce_source(desc)
            assert gb.evaluate_source(old,160)['probability']==p
            bump('completed_previous_joint_comparisons')
        bump('complete_native_transfer_outputs')
        records.append(dict(g=g,k=k,cycle=cycle,flip=flip,hidden_physical_basis=hidden,n=desc[1],
                            source_bits=native['source_bits'],native_records=len(native['gates']),
                            path_bits=result['physical_bits'],old_joint_branches=str(1 << g),
                            probability=str(p),stats=cert['stats'],cost=result['cost']))
        print('Native signed interface:',g,k,'cycle' if cycle else 'path',hidden,p,cert['stats'],flush=True)
    bad=list(native['gates'])+[('Z',0)]
    try:it.reduce_native(desc[1],bad,desc[4],desc[5])
    except ValueError:bump('modified_native_source_refusal')
    else:raise AssertionError('modified source accepted')
    # Local perturbations change the answer and still have independent state references.
    for term in (1 << 1,(1 << 1)|(1 << 2),1 << 3):
        desc,_=graph_source(1,3,'cycle_uv')
        desc[3][0]=sorted(set(desc[3][0])^{term})
        p=fast_independent_probability(desc)
        native=cc.compile_native(desc);result=it.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        assert it.evaluate_source(result,180)['probability']==p
        bump('perturbed_native_outputs')
        if p!=Fraction(65,128):bump('changed_native_probabilities')
    return records


def dense_prefix_reference(k,g):
    A=8**(k-1);B=4**(k-1);T=[]
    for s in range(4):
        row=[]
        for t in range(4):
            u=s^t
            value=sum((-1)**(((u.bit_count()*v.bit_count())+(s&v).bit_count())&1)*
                      (A-B*(-1)**((u&v).bit_count()&1)) for v in range(4))
            assert value==4*(A*int(s==3*(u.bit_count()&1))-B*int(s==(3*(u.bit_count()&1))^u))
            row.append(value)
        T.append(row)
    weights=[1,0,0,0]
    for _ in range(g):weights=[sum(weights[s]*T[s][t] for s in range(4)) for t in range(4)]
    bump('dense_supplied_family_prefix_references')
    return (1-Fraction(sum(weights),1 << (g*(3*k+1))))/2


def dense_cut_checks(rng):
    records=[]
    for g in range(3,9):
        # Full four-coordinate block interfaces in a hidden order and local bases.
        order=list(range(g));rng.shuffle(order);positions={j:p for p,j in enumerate(order)}
        bases=[hidden_basis(4,rng) for _ in range(g)]
        def edge(a,b):
            pa,pb=positions[a],positions[b]
            cols=(0,1,0,4) if pa<pb else (2,0,8,0)
            return cc.compose(cc.transpose(bases[a]),cc.compose(cols,bases[b]))
        def cut_rank(selected):
            outside=[j for j in range(g) if j not in selected];selected=sorted(selected)
            columns=[]
            for a in selected:
                for col in range(4):
                    columns.append(sum(edge(b,a)[col] << (4*p) for p,b in enumerate(outside)))
            return len(echelon(columns))
        for mask in range(1,(1 << g)-1):
            selected={j for j in range(g) if mask >> j & 1}
            logical=sorted(positions[j] for j in selected);length=len(selected)
            end_interval=logical==list(range(length)) or logical==list(range(g-length,g))
            assert (cut_rank(selected)==2)==end_interval
            bump('dense_rank_two_cut_classifications')
        selected=set();recovered=[];ranks=[]
        while len(selected)<g:
            rank,j=min((cut_rank(selected|{j}),j) for j in range(g) if j not in selected)
            selected.add(j);recovered.append(positions[j]);ranks.append(rank)
        assert recovered in (list(range(g)),list(reversed(range(g))))
        assert ranks==[2]*(g-1)+[0]
        bump('hidden_dense_greedy_orders')
        records.append(dict(g=g,recovered_order=recovered,cut_ranks=ranks))
    return records

def boundaries(rng):
    records=[]
    # A native directed complete graph has rank-two edges but degree three.
    desc,_=graph_source(1,4,'cycle_uv');d=3;phase=set(desc[3][0])
    phase ^= {(1 << (d*j+1))|(1 << (d*((j+1)%4)+2)) for j in range(4)}
    phase ^= {(1 << (d*j+1))|(1 << (d*l+2)) for j in range(4) for l in range(j+1,4)}
    desc[3][0]=sorted(phase);native=cc.compile_native(desc)
    result=it.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    detail=result['interface_transfer']
    assert len(detail['refusals'])==1 and detail['refusals'][0]['reason']=='interaction_degree'
    assert detail['refusals'][0]['tables_built']==0 and result['cost']['gaussian_sums']==16
    p=fast_independent_probability(desc);assert it.evaluate_source(result,180)['probability']==p
    assert p==dense_prefix_reference(1,4)
    for k,g in ((1,3),(2,3),(1,8),(1,32),(3,32)):
        reference=dense_prefix_reference(k,g)
        if g==3:
            check,_=graph_source(k,g,'cycle_uv');width=2*k+1
            check[3][0]=sorted(set(check[3][0])^{(1 << (width*2+1))|(1 << 2),
                                               (1 << 1)|(1 << (width*2+2))})
            assert it.evaluate_source(it.reduce_source(check),180)['probability']==reference
            bump('dense_small_complete_reference_comparisons')
    bump('native_high_degree_exact_fallback')
    records.append(dict(kind='native_high_degree',n=desc[1],gaussian_sums=16,probability=str(p)))
    # A single rank-three edge is refused at cap two, admitted at cap three.
    f={7,56,1|(1 << 3),2|(1 << 4),4|(1 << 5)}
    source=gb.discover(f,6)
    refused=it.transfer(source,2);assert not refused['accepted'] and refused['reason']=='edge_rank'
    accepted=it.transfer(source,3);assert accepted['accepted'] and accepted['value']==brute(f,6)
    independent_fibers(source,accepted);bump('paid_rank_cap_extension')
    # Retain prior dense cancellation, indecomposable boundary and growing-layer cases.
    desc,p=graph_source(1,6,'clique');native=cc.compile_native(desc)
    result=it.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert it.evaluate_source(result,160)['probability']==p and not result['interface_transfer']['certificates']
    assert len(result['interface_transfer']['retained']['certificates'])==1
    bump('retained_dense_support_factorization')
    field=field_phase(3,11);tree,detail=it.compile_sum(field,9)
    assert detail['current']['unsupported_work']==512 and it.evaluate_tree(tree)==120
    bump('retained_indecomposable_field_boundary')
    zero={7,25,6,10,20,1};tree,detail=it.compile_sum(zero^{m << 5 for m in field},14)
    assert tree['kind']=='zero' and it.evaluate_tree(tree)==0
    bump('retained_zero_pruning')
    from check_quadratic_pushforward_recursion import isotropic_source
    desc,p=isotropic_source(3,33,rng,True,False);native=cc.compile_native(desc)
    result=it.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert it.evaluate_source(result,160)['probability']==p
    bump('retained_growing_layer_native_output')
    return records


def main():
    rng=random.Random(1730520)
    residual=residual_checks(rng)
    assert all(COUNTS.get(k,0)>0 for k in ('dependent_endpoint_rows','zero_scalar_nonzero_interface','nonzero_affine_signature_origins'))
    print('Signed fibers, edge quotients, hidden affine sums and cancellation traps pass',flush=True)
    native=native_checks(rng);limits=boundaries(rng);dense_orders=dense_cut_checks(rng)
    assert COUNTS.get('changed_native_probabilities',0)>0
    prior=ROOT/'artifacts/s173-gaussian-boundary-factorization-checks.json';old=json.loads(prior.read_text())
    hashes={}
    for path in ['src/gaussian_interface_transfer.py','src/check_gaussian_interface_transfer.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730520,counts=COUNTS,residual_traps=residual,
                 native_sources=native,boundaries=limits,dense_cut_references=dense_orders,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-derived signed interfaces replace joint control enumeration on admitted paths/cycles. All listed native outputs are fully evaluated, including the former 32-block cycle boundary. General interaction graphs and indecomposable blocks remain unresolved. No hard-language or full-portfolio claim.')
    target=ROOT/'artifacts/s173-gaussian-interface-transfer-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
