"""Independent Gaussian-mixture norms, native precision and grouping-boundary checks."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations,product
from pathlib import Path
from unittest.mock import patch
import gaussian_message_norms as gm
import gaussian_pair_envelopes as pe
import gaussian_boundary_factorization as gb
import gaussian_block_cuts as bc
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_gaussian_block_cuts import dense_source
from check_gaussian_pair_envelopes import BOUNDARY_EDGES
from check_cubic_linear_factors import terminal
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def branch_value(branch,x):
    z=solve(branch['span'],x^branch['origin'])
    return 0 if z is None else branch['amplitude']*((-1)**cc.anf_evaluate(branch['phase'],z))


def direct_norm(branches,width):
    return sum(abs(sum(branch_value(b,x) for b in branches)) for x in range(1 << width))


def gaussian_checks(rng):
    for t in range(5):
        for amplitudes in [tuple(1 for _ in range(t)),tuple(1 << (3*i) for i in range(t))]:
            coefficients=gm.absolute_coefficients(amplitudes)
            for values in product((-1,0,1),repeat=t):
                actual=0
                for powers,c in coefficients.items():
                    term=c
                    for z,e in zip(values,powers):term*=z**e
                    actual+=term
                assert actual==(1 << t)*abs(sum(a*z for a,z in zip(amplitudes,values)))
                bump('independent_ternary_interpolation_values')
    for width in range(9):
        for t in range(5):
            branches=[]
            for i in range(t):
                P=hidden_basis(width,rng) if width>=2 else cc.identity(width)
                d=rng.randrange(width+1);columns=P[:d]
                phase={m for m in cc.anf_masks(d,2) if rng.getrandbits(1)}
                branches.append(gm.affine_branch(width,rng.getrandbits(width),columns,phase,1 << (3*i)))
            norm=gm.absolute_mass(branches,width)
            assert norm['value']==direct_norm(branches,width) and norm['monomials']<=3**t
            assert norm['gaussian_sums']<=norm['monomials']
            bump('independent_gaussian_mixture_norms')
    # Identical supports with opposite phases must cancel before absolute values.
    for width in (0,1,8):
        a=gm.affine_branch(width,0,cc.identity(width),set(),1 << 20)
        b=gm.affine_branch(width,0,cc.identity(width),{0},1 << 20)
        assert gm.absolute_mass([a,b],width)['value']==0
        bump('zero_mixture_cancellation')
    # Rank 64 is handled without a table: compare to an independent 8-bit core.
    width=64;P=hidden_basis(width,rng);origin=rng.getrandbits(width)
    branches=[];small=[]
    for i,a in enumerate((1,3,7,15)):
        phase={3 << (2*i)}
        small.append(gm.affine_branch(8,0,cc.identity(8),phase,a))
        hidden=pd.substitute_boolean(phase,qr.affine_forms(origin,P,width))
        branches.append(gm.affine_branch(width,0,cc.identity(width),hidden,a))
    norm=gm.absolute_mass(branches,width)
    assert norm['value']==direct_norm(small,8)*(1 << 56)
    assert norm['gaussian_sums']<=81 and norm['coefficient_denominator']==16
    bump('rank64_bulk_norm')
    return norm


def source_checks(rng):
    for n in (6,9,12):
        for _ in range(5):
            phase={7 << (3*j) for j in range(n//3)}^{m for m in cc.anf_masks(n,2) if rng.randrange(3)==0}
            P=hidden_basis(n,rng);origin=rng.getrandbits(n)
            phase=pd.substitute_boolean(phase,qr.affine_forms(origin,P,n))
            source=gb.discover(phase,n)
            norm=gm.terminal_norm(source)
            local,_,rows=gb.split_phase(source['decomposition'])
            for f,block,R,group,answer in zip(local,source['decomposition']['blocks'],rows,source['messages'],norm['blocks']):
                fibers={}
                for x in range(1 << len(block)):
                    y=sum(((r&x).bit_count()%2) << j for j,r in enumerate(R))
                    fibers[y]=fibers.get(y,0)+(-1)**cc.anf_evaluate(f,x)
                branches=[b for m in group if (b:=gm.source_branch(m,R)) is not None]
                for y in range(1 << len(R)):
                    assert sum(branch_value(b,y) for b in branches)==fibers.get(y,0)
                    bump('independent_source_fiber_values')
                assert answer['value']==sum(abs(x) for x in fibers.values())
                bump('independent_source_absolute_masses')
            assert abs(brute(phase,n))<=norm['bound']
            tree,detail=gm.compile_sum(phase,n);value,_=pe.exact_tree(tree)
            assert value==brute(phase,n) and abs(value)<=tree['bound']<=detail['previous_bound']
            bump('independent_recursive_source_sums')
    # Two local controls and four branches, including a six-variable field block.
    mixed=field_phase(2,7)^{m << 6 for m in (7,25)}^{(1 << 2)|(1 << 7),1,0}
    source=gb.discover(mixed,11);norm=gm.terminal_norm(source)
    assert max(len(group) for group in source['messages'])==4
    assert abs(brute(mixed,11))<=norm['bound']
    for group,R,answer in zip(source['messages'],source['boundaries'],norm['blocks']):
        branches=[b for m in group if (b:=gm.source_branch(m,R)) is not None]
        assert answer['value']==direct_norm(branches,len(R))
    bump('source_four_branch_norm')
    # Unsupported field fallback is unchanged.
    tree,detail=gm.compile_sum(field_phase(3,11),9)
    value,stats=pe.exact_tree(tree)
    assert value==120 and stats['point_evaluations']==512 and not detail['certificates']
    bump('unsupported_field_exact_fallback')


def graph_probability(k,g,edges,all_aux=False):
    """Independent 2^g bilinear-rank reference, not the production evaluator."""
    base=[3 << (2*j) for j in range(g) for _ in range(2)]
    for a,b in edges:
        for i in (0,1):base[2*b+i] ^= 1 << (2*a+i)
    A=8**(k-1);B=4**(k-1);total=0
    for word in range(1 << g):
        columns=list(base)
        for j in pd.bits(word):
            columns[2*j] ^= 1 << (2*j);columns[2*j+1] ^= 1 << (2*j+1)
        exponent=4*g-len(echelon(columns));ones=word.bit_count()
        if all_aux:total+=(-1)**ones*(1 << (k*exponent))
        else:total+=A**(g-ones)*(-B)**ones*(1 << exponent)
    return (1-Fraction(total,1 << (g*(3*k+1))))/2


def all_aux_cycle(k,g):
    desc=dense_source(k,g,edges=[]);w=2*k+1
    desc[3][0]=sorted(set(desc[3][0])^{(1 << (w*j+2*i+1))|(1 << (w*((j+1)%g)+2*i+2))
                                    for j in range(g) for i in range(k)})
    return desc


def check_answer(result,bits,expected=None):
    a=gm.evaluate_source(result,bits)
    assert a['error_bound']<Fraction(1,1 << bits)
    if expected is not None:
        assert a['interval'][0]<=expected<=a['interval'][1]
        assert abs(a['estimate']-expected)<=a['error_bound']
        if a['probability'] is not None:assert a['probability']==expected
        bump('complete_precision_reference_comparisons')
    if a['mode']=='envelope':
        with patch.object(pe,'exact_tree',side_effect=AssertionError('forbidden exact readout')):
            assert gm.evaluate_source(result,bits)==a
        bump('certified_without_exact_readout')
    return a


def native_checks(rng):
    records=[]
    cases=[(1,4,None,False,False),(2,3,None,True,True),(3,4,None,False,False),
           (3,8,BOUNDARY_EDGES,False,False),(4,8,BOUNDARY_EDGES,True,False),
           (3,16,[(a,b) for a in range(16) for b in range(16) if a!=b and rng.randrange(3)==0],False,False)]
    for k,g,edges,flip,hidden in cases:
        if edges is None:edges=list(combinations(range(g),2))
        desc=dense_source(k,g,flip,edges)
        p=graph_probability(k,g,edges)
        if flip:p=1-p
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc);result=gm.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        norm=result['gaussian_norm'];D=1 << (desc[1]*2)
        rho=1-Fraction(1,1 << (k+1))
        assert Fraction(norm['bound'],D)<=rho**g
        chosen=next(b for b in range(1,30) if (norm['bound'] << (b+1))>=2*D)
        low=check_answer(result,chosen,p)
        assert low['mode']=='envelope'
        if g<=8:
            high=check_answer(result,180,p)
            if edges==BOUNDARY_EDGES:
                assert high['stats']['gaussian_sums']==1 << g
                old=pe.reduce_source(desc);old_answer=pe.evaluate_source(old,chosen)
                assert old_answer['mode']=='exact_fallback' and old_answer['probability']==p
                assert old_answer['stats']['gaussian_sums']==1 << g
                bump('completed_prior_fallback_comparisons')
            bump('complete_exact_fallbacks')
        if desc[1]<=15:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
            if desc[1]<=12:check_native(native,p);bump('literal_native_outputs')
        for _ in range(8):
            xs=[rng.getrandbits(desc[1]) for _ in range(3)]
            assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
            bump('original_output_phase_identities')
        record=dict(k=k,g=g,n=desc[1],hidden=hidden,flip=flip,source_bits=native['source_bits'],
                    native_records=len(native['gates']),probability=str(p),bits=chosen,
                    prior_bound=str(norm['previous_bound']),bound=str(norm['bound']),
                    error_bound=str(low['error_bound']),gaussian_sums=norm['gaussian_sums'],monomials=norm['monomials'],
                    pair_trials=result['pair_certification']['pair_trials'],
                    prior_joint_budget=str(result['cost']['gaussian_sums']),reference_terms=1 << g)
        records.append(record);bump('complete_native_reference_sources')
        print('Native bulk Gaussian norm:',record,flush=True)
    # Larger graph uses complete certificates; its exact probability is not enumerated.
    k=3;g=24;edges=[(a,b) for a in range(g) for b in range(g) if a!=b and rng.randrange(4)==0]
    desc=dense_source(k,g,edges=edges);native=cc.compile_native(desc)
    result=gm.reduce_native(desc[1],native['gates'],desc[4],desc[5]);norm=result['gaussian_norm']
    a=check_answer(result,3)
    assert a['mode']=='envelope' and result['pair_certification']['pair_trials']==0
    assert result['cost']['gaussian_sums']==1 << g
    assert Fraction(norm['bound'],1 << (desc[1]*2))<=(1-Fraction(1,16))**g
    pending=[result['tree']];controls=[]
    while pending:
        node=pending.pop()
        if node['kind']=='controls':controls.append(node)
        elif node['kind']=='push':pending.append(node['child'])
        elif node['kind']=='product':pending.extend(node['children'])
    assert len(controls)==1;source=controls[0]['source']
    C,masks,_=bc.cross_matrix(source);plan=bc.discover_order(C,masks)
    assert plan['max_rank']>4
    local,_,rows=gb.split_phase(source['decomposition'])
    for phase,block,R,answer in zip(local,source['decomposition']['blocks'],rows,norm['certificates'][0]['blocks']):
        fibers={}
        for x in range(1 << len(block)):
            y=sum(((r&x).bit_count()%2) << j for j,r in enumerate(R))
            fibers[y]=fibers.get(y,0)+(-1)**cc.anf_evaluate(phase,x)
        assert answer['value']==sum(abs(x) for x in fibers.values())
        bump('large_native_independent_block_norms')
    for _ in range(12):
        xs=[rng.getrandbits(desc[1]) for _ in range(3)]
        assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
        bump('original_output_phase_identities')
    record=dict(kind='large_certified_source',k=k,g=g,n=desc[1],source_bits=native['source_bits'],
                native_records=len(native['gates']),bits=3,estimate=str(a['estimate']),error_bound=str(a['error_bound']),
                gaussian_sums=norm['gaussian_sums'],monomials=norm['monomials'],
                selected_cut_ranks=plan['ranks'],prior_joint_budget=str(1 << g),
                reference_scope='Original phase and independent local fiber norms; exact global probability not independently evaluated.')
    records.append(record);bump('complete_large_native_certificate')
    print('Large native bulk norm:',record,flush=True)
    return records


def cluster_reference(source,selected):
    """Next-mechanism finite reference; not an integrated clustered reader."""
    C,masks,_=bc.cross_matrix(source);mask=0
    for j in selected:mask|=masks[j]
    positions=tuple(pd.bits(mask));index={v:i for i,v in enumerate(positions)}
    phase={sum(1 << index[j] for j in pd.bits(m)) for m in source['decomposition']['phase'] if m and m&mask==m}
    width=len(positions);local=gb.discover(phase,width)
    joint=gb.joint_certificate(phase,width,local['decomposition'],local['factors']);q=joint['control_rank']
    rows=ds.image_basis(ds.transpose_rect(tuple(C[j]&~mask for j in positions),len(C)))
    factor=dict(control_rank=q,columns=joint['columns'][q:],
                origins=tuple(cc.action(joint['columns'][:q],t) for t in range(1 << q)),
                phases=tuple(cb.restricted_quadratic(joint,t) for t in range(1 << q)))
    factor['values']=tuple(lf.quadratic_value(p,width-q) for p in factor['phases'])
    messages=gb.local_messages(phase,width,rows,factor)
    branches=[b for m in messages if (b:=gm.source_branch(m,rows)) is not None]
    return gm.absolute_mass(branches,len(rows)),phase,rows


def boundary_and_cluster_checks():
    records=[]
    for k in (2,3):
        g=3;desc=all_aux_cycle(k,g);native=cc.compile_native(desc)
        result=gm.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        p=graph_probability(k,g,[(j,(j+1)%g) for j in range(g)],all_aux=True)
        a=check_answer(result,4,p);norm=result['gaussian_norm']
        mass=(1 << (4*k))-(1 << (2*k))
        assert norm['bound']==mass**g*(1 << ((k+1)*g))
        assert all(b['boundary_rank']==4*k and b['value']==mass for c in norm['certificates'] for b in c['blocks'])
        assert norm['bound']>1 << (2*desc[1]) and a['stats']['gaussian_sums']==1 << g
        if k==2:assert p==fast_independent_probability(desc);bump('independent_all_aux_state_output')
        bump('full_auxiliary_local_norm_obstructions')
        records.append(dict(k=k,g=g,probability=str(p),local_norm=mass,normalized_local_ratio=str(Fraction(mass,1 << (3*k+1))),stats=a['stats']))
    # Pair neighboring original blocks before absolute values. The closed formula
    # follows independently from ranks k and 2k of J and J+I.
    clusters=[]
    for k in (1,2,3,4):
        desc=all_aux_cycle(k,4);leaf=terminal(qr.reduce_source(desc)['tree'])
        source=gb.discover(leaf['phase'],leaf['n']);selected=min(source['edges'])
        norm,phase,rows=cluster_reference(source,selected)
        predicted=(1 << (6*k+1))-(1 << (5*k))-(1 << (4*k))
        assert norm['value']==predicted
        ratio=Fraction(predicted,1 << (6*k+2))
        assert ratio==Fraction(1,2)-Fraction(1,1 << (k+2))-Fraction(1,1 << (2*k+2))<Fraction(1,2)
        if k<=2:
            fibers={}
            for x in range(1 << (2*(4*k+1))):
                y=sum(((r&x).bit_count()%2) << j for j,r in enumerate(rows))
                fibers[y]=fibers.get(y,0)+(-1)**cc.anf_evaluate(phase,x)
            assert sum(abs(v) for v in fibers.values())==predicted
            bump('independent_cluster_fiber_norms')
        clusters.append(dict(k=k,norm=predicted,ratio=str(ratio),boundary_rank=len(rows),gaussian_sums=norm['gaussian_sums']))
        bump('source_derived_pair_cluster_references')
    return records,clusters


def main():
    rng=random.Random(1730525)
    rank64=gaussian_checks(rng);source_checks(rng)
    print('Ternary coefficients, Gaussian intersections, source fibers and rank-64 norm pass',flush=True)
    native=native_checks(rng);boundary,clusters=boundary_and_cluster_checks()
    prior=ROOT/'artifacts/s173-gaussian-pair-envelope-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/gaussian_message_norms.py','src/check_gaussian_message_norms.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730525,counts=COUNTS,rank64=rank64,native_sources=native,
                 all_auxiliary_boundary=boundary,next_cluster_references=clusters,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Complete source-derived bulk Gaussian norm and precision reader; fixed-k first-auxiliary graph theorem. Full-auxiliary cycles refute the unclustered normalized bound. Neighbor-pair norms support the next mechanism; clustered full reader unimplemented. No universal or hard-language claim.')
    target=ROOT/'artifacts/s173-gaussian-message-norm-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
