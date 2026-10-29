"""Exact checks of local Gaussian-support factorization and original outputs."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import gaussian_boundary_factorization as gb
import cubic_centroid_controls as cb
import cubic_centroid_descent as cc
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_cubic_linear_factors import star_blocks,terminal
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def graph_source(k,g,kind,flip=False):
    desc,p=star_blocks(k,g,flip);d=2*k+1;phase=set(desc[3][0])
    phase ^= {(1 << (d*j+1))|(1 << (d*(j+1)+1)) for j in range(g-1)}
    if kind=='clique':edges=list(combinations(range(g),2))
    elif kind=='star':edges=[(0,j) for j in range(1,g)]
    elif kind=='path':edges=[(j,j+1) for j in range(g-1)]
    elif kind=='cycle_uv':
        edges=[]
        phase ^= {(1 << (d*j+1))|(1 << (d*((j+1)%g)+2)) for j in range(g)}
        beta=Fraction(1,1 << (k+1))
        expectation=(Fraction(1,4)-beta)**g+(1+2*(-1)**g)*beta**g
        p=(1-expectation)/2
        if flip:p=1-p
    else:raise ValueError(kind)
    phase ^= {(1 << (d*a+1))|(1 << (d*b+1)) for a,b in edges}
    desc[3][0]=sorted(phase)
    return desc,p


def message_checks(result):
    for group in result.get('messages',()):
        for m in group:
            Q=m['quadratic'];rows=m['rows'];free=len(m['kernel']);push=m['push']
            if free>8:continue
            support=echelon(push['columns'])
            for y in range(1 << len(rows)):
                expected=sum(-1 if cc.anf_evaluate(Q,x) else 1
                             for x in range(1 << free)
                             if sum(((r&x).bit_count()&1) << j for j,r in enumerate(rows))==y)
                z=solve(support,y^push['origin'])
                actual=0 if push['zero'] or z is None else ((-1)**cc.anf_evaluate(push['phase'],z))*(1 << push['exponent'])
                assert expected==actual
                bump('independent_boundary_fiber_values')
            assert m['value']==brute(Q,free)
            if m['value']==0 and not push['zero']:bump('zero_total_nonzero_message')
            if not push['zero'] and m['lift_origin']:bump('nonzero_affine_origins')
    for (a,b),matrix in result.get('edges',{}).items():
        for x in result['messages'][a]:
            if x['push']['zero']:continue
            for y in result['messages'][b]:
                if y['push']['zero']:continue
                phase=gb.cross_restriction(matrix,x,y);nx=len(x['lift_columns']);ny=len(y['lift_columns'])
                if nx+ny>7:continue
                for word in range(1 << (nx+ny)):
                    left=x['lift_origin']^cc.action(x['lift_columns'],word&((1 << nx)-1))
                    right=y['lift_origin']^cc.action(y['lift_columns'],word >> nx)
                    assert cc.anf_evaluate(phase,word)==((left&cc.action(matrix,right)).bit_count()&1)
                    bump('independent_affine_cross_values')


def residual_checks(rng):
    desc,p=star_blocks(1,3);root=qr.reduce_source(desc);leaf=terminal(root['tree'])
    base=leaf['phase'];n=leaf['n'];expected=brute(base,n)
    records=[]
    for affine in (False,True):
        for _ in range(8):
            P=hidden_basis(n,rng);offset=rng.getrandbits(n) if affine else 0
            f=pd.substitute_boolean(base,qr.affine_forms(offset,P,n))
            if len(records)<4:
                assert gb.fast_centroid(f,n)==tuple(cc.centroid(n,f));bump('packed_centroid_equivalence')
                assert gb.primitive_blocks(f,n)['projectors']==cb.centroid_blocks(f,n)['projectors']
            result=gb.discover(f,n);message_checks(result)
            if not affine:assert result['accepted']
            if result['accepted']:
                assert result['value']==expected;bump('hidden_support_factorizations')
            else:
                assert cb.evaluate_controls(result['joint'])==expected
                bump('affine_refusal_exact_fallback')
            for _ in range(8):
                x=rng.getrandbits(n)
                assert cc.anf_evaluate(f,x)==cc.anf_evaluate(base,offset^cc.action(P,x))
                bump('hidden_affine_bijections')
            records.append(dict(affine=affine,accepted=result['accepted'],reason=result['reason'],value=expected))
    for n in (6,9):
        cubic={7 << (3*j) for j in range(n//3)}
        for _ in range(10):
            f=cubic^{m for m in cc.anf_masks(n,2) if rng.randrange(4)==0}
            result=gb.discover(f,n);message_checks(result)
            value=result['value'] if result['accepted'] else cb.evaluate_controls(result['joint'])
            assert value==brute(f,n);bump('arbitrary_lower_term_values')
    # Whole local scalar zero, but coupling two controls restores a nonzero sum.
    zero={7,25,6,10,20,1};trap=zero^{7 << 5}^{1|(1 << 5)}
    result=gb.discover(trap,8);message_checks(result)
    assert not result['accepted']
    assert any(sum(m['value'] for m in group)==0 for group in result['messages'])
    assert cb.evaluate_controls(result['joint'])==brute(trap,8)==16
    bump('zero_local_total_coupling_trap')
    # Omitting affine origins would miss the minus sign on the only surviving pair.
    offset_trap={7,4,56,32,18};result=gb.discover(offset_trap,6);message_checks(result)
    assert not result['accepted'] and result['witness']['phase']=={0}
    assert cb.evaluate_controls(result['joint'])==brute(offset_trap,6)==-4
    bump('affine_origin_sign_trap')
    # A branch has zero scalar but a nonzero boundary message.
    branch_trap={7,2,56,18};result=gb.discover(branch_trap,6);message_checks(result)
    assert not result['accepted'] and cb.evaluate_controls(result['joint'])==brute(branch_trap,6)==20
    bump('zero_branch_total_coupling_trap')
    mixed=field_phase(2,7)^{m << 6 for m in (7,25)}^{(1 << 2)|(1 << 7),1,0}
    result=gb.discover(mixed,11);message_checks(result)
    assert sorted(f['control_rank'] for f in result['factors'])==[1,2]
    value=result['value'] if result['accepted'] else cb.evaluate_controls(result['joint'])
    assert value==brute(mixed,11)==-112
    bump('mixed_one_two_control_messages')
    return records


def pointwise_source(result,rng):
    desc=result['descriptor'];n=desc[1]
    for _ in range(10):
        xs=[rng.getrandbits(n) for _ in range(2*len(desc[3])-1)]
        x=sum(v << (j*n) for j,v in enumerate(xs))
        assert cc.anf_evaluate(result['phase'],x)==boolean_output_phase(desc,xs)
        bump('original_output_phase_identities')


def cycle_matrix_reference(k,g):
    A=8**(k-1);B=4**(k-1)
    M=[]
    for v in range(4):
        row=[];parity=v.bit_count()&1
        for w in range(4):
            value=sum((-1)**((u.bit_count()*parity+(u&w).bit_count())&1)*
                      (A-B*(-1)**((u&v).bit_count()&1)) for u in range(4))
            assert value==4*(A*int(w==3*parity)-B*int(w==(3*parity)^v))
            row.append(value)
        M.append(row)
    def multiply(a,b):
        return [[sum(a[i][j]*b[j][l] for j in range(4)) for l in range(4)] for i in range(4)]
    power=[[int(i==j) for j in range(4)] for i in range(4)]
    for _ in range(g):power=multiply(power,M)
    value=sum(power[i][i] for i in range(4))
    assert value==4**g*((A-B)**g+B**g+2*(-B)**g)
    bump('supplied_family_transfer_references')
    return (1-Fraction(value,1 << (g*(3*k+1))))/2


def native_checks(rng):
    records=[]
    cases=[(3,1,'path',False,False),(3,1,'clique',True,False),
           (4,2,'clique',False,False),(5,1,'star',True,False),
           (8,1,'clique',False,False),(12,1,'clique',True,False),
           (24,1,'clique',False,False),(32,1,'clique',True,False),
           (3,3,'clique',False,False),(3,1,'clique',False,True),(3,2,'clique',True,True)]
    for g,k,kind,flip,hidden in cases:
        desc,p=graph_source(k,g,kind,flip)
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc);result=gb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        detail=result['support_factorization'];assert len(detail['certificates'])==1 and not detail['refusals']
        cert=detail['certificates'][0]
        assert cert['local_branches']==2*g and cert['joint_branches']==1 << g
        assert detail['previous']['max_width']==g*(4*k+1)
        assert cert['reason']=='annihilated_cross_support'
        assert result['cost']['work']==1
        for bits in (2,160,4096):
            answer=gb.evaluate_source(result,bits)
            assert answer['probability']==p and 0<=p-answer['rounded']<Fraction(1,1 << bits)
            bump('complete_precision_evaluations')
        pointwise_source(result,rng)
        if desc[1]<=12:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
        if desc[1]<=9:check_native(native,p);bump('literal_native_outputs')
        if g<=4:
            old=cb.reduce_source(desc)
            assert cb.evaluate_source(old,160)['probability']==p
            bump('completed_previous_joint_comparisons')
        bump('complete_native_factorized_outputs')
        records.append(dict(g=g,k=k,graph=kind,flip=flip,hidden_physical_basis=hidden,
                            n=desc[1],path_bits=result['physical_bits'],source_bits=native['source_bits'],
                            native_records=len(native['gates']),old_width=g*(4*k+1),
                            previous_joint_branches=str(1 << g),local_branches=cert['local_branches'],
                            pair_checks=cert['pair_checks'],probability=str(p),cost=result['cost']))
        print('Native support factorization:',g,k,kind,hidden,p,cert['local_branches'],flush=True)
    bad=list(native['gates'])+[('Z',0)]
    try:gb.reduce_native(desc[1],bad,desc[4],desc[5])
    except ValueError:bump('modified_native_source_refusal')
    else:raise AssertionError('modified source accepted')
    return records


def cycle_and_boundary(rng):
    records=[]
    for g,k,full in [(3,1,True),(4,1,True),(5,2,True),(6,2,True),(32,1,False)]:
        desc,p=graph_source(k,g,'cycle_uv')
        assert p==cycle_matrix_reference(k,g)
        native=cc.compile_native(desc);result=gb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        detail=result['support_factorization']
        assert not detail['certificates'] and len(detail['refusals'])==1
        assert detail['refusals'][0]['reason']=='nonvanishing_cross_support'
        assert result['cost']['gaussian_sums']==1 << g
        assert all(len(r)==4 for r in detail['refusals'][0]['boundaries'])
        pointwise_source(result,rng)
        if full:
            assert gb.evaluate_source(result,160)['probability']==p;bump('complete_native_cycle_fallbacks')
            if desc[1]<=12:
                assert p==fast_independent_probability(desc);bump('independent_cycle_state_outputs')
        records.append(dict(g=g,k=k,n=desc[1],full_fallback_evaluated=full,
                            declared_gaussian_sums=str(1 << g),reference_probability=str(p)))
        print('Native surviving cycle:',g,k,'full' if full else 'construction only',p,flush=True)
    field=field_phase(3,11);tree,detail=gb.compile_sum(field,9)
    assert not detail['certificates'] and detail['current']['unsupported_work']==512
    assert gb.evaluate_tree(tree)==120
    bump('retained_indecomposable_field_boundary')
    zero={7,25,6,10,20,1}
    tree,detail=gb.compile_sum(zero^{m << 5 for m in field},14)
    assert tree['kind']=='zero' and gb.evaluate_tree(tree)==0
    bump('certified_zero_prunes_unsupported_sibling')
    from check_quadratic_pushforward_recursion import isotropic_source
    desc,p=isotropic_source(3,33,rng,True,False);native=cc.compile_native(desc)
    result=gb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert gb.evaluate_source(result,128)['probability']==p
    bump('retained_growing_layer_native_output')
    return records


def main():
    rng=random.Random(1730519)
    residual=residual_checks(rng)
    assert COUNTS.get('zero_total_nonzero_message',0)>0 and COUNTS.get('nonzero_affine_origins',0)>0
    print('Hidden supports, all message fibers and cancellation traps pass',flush=True)
    native=native_checks(rng);boundaries=cycle_and_boundary(rng)
    prior=ROOT/'artifacts/s173-cubic-centroid-control-checks.json';old=json.loads(prior.read_text())
    hashes={}
    for path in ['src/gaussian_boundary_factorization.py','src/check_gaussian_boundary_factorization.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730519,counts=COUNTS,hidden_residuals=residual,
                 native_sources=native,cycle_boundaries=boundaries,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Local Gaussian boundary supports certify exact factorization before joint enumeration. Eleven factorized original-native outputs are complete. The 32-block surviving cycle is construction/reference only, not enumerated. No hard-language or full-portfolio claim.')
    target=ROOT/'artifacts/s173-gaussian-boundary-factorization-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
