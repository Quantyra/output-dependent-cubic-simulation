"""Check recursive Gaussian constraints and actual native output costs."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import quadratic_pushforward_recursion as qr
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
import corrupted_field_contractions as cf
from finite_field_descent import echelon
from magic_residual_counts import quadratic_sum
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from rank_one_field_correction import round_probability

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def brute(poly,n):
    return sum(-1 if cc.anf_evaluate(poly,x) else 1 for x in range(1 << n))


def gauss(poly,n):
    return quadratic_sum(int(0 in poly),{m.bit_length()-1 for m in poly if m.bit_count()==1},
                         {tuple(pd.bits(m)) for m in poly if m.bit_count()==2},n)


def check_pushforwards(rng):
    for n in range(9):
        for t in range(n+1):
            for _ in range(4):
                basis=hidden_basis(n,rng) if n>1 else cc.identity(n)
                rows=basis[:t]
                Q={m for m in cc.anf_masks(n,2) if rng.getrandbits(1)}
                pushed=qr.quadratic_pushforward(Q,rows,n)
                expected=[0]*(1 << t)
                for x in range(1 << n):
                    b=sum(((row&x).bit_count()&1) << j for j,row in enumerate(rows))
                    expected[b]+=(-1)**cc.anf_evaluate(Q,x)
                actual=[0]*(1 << t)
                if not pushed['zero']:
                    for z in range(1 << len(pushed['columns'])):
                        b=pushed['origin']^cc.action(pushed['columns'],z)
                        actual[b]=(1 << pushed['exponent'])*(-1)**cc.anf_evaluate(pushed['phase'],z)
                assert actual==expected
                bump('exact_quadratic_pushforwards')
                bump('quadratic_fiber_values',len(expected))
                if pushed['zero']:bump('zero_pushforwards')
    for n in range(1,10):
        for _ in range(12):
            poly={m for m in cc.anf_masks(n) if rng.getrandbits(1)}
            tree=qr.compile_sum(poly,n);cost=qr.tree_cost(tree)
            assert qr.evaluate_tree(tree)==brute(poly,n)
            assert cost['nodes']<=3*n+1
            bump('exact_recursive_cubic_sums')
    # Two distinct eliminations: y*x forces x=0, then a*c forces c=0.
    poly={3,14,20,112}
    P=hidden_basis(7,rng)
    hidden=pd.substitute_boolean(poly,qr.affine_forms(0,P,7))
    tree=qr.compile_sum(hidden,7);cost=qr.tree_cost(tree)
    assert qr.evaluate_tree(tree)==brute(hidden,7)
    assert cost['pushes']>=2 and cost['max_width']==0,cost
    bump('multiple_constraint_rounds')
    vanished=qr.compile_sum({7,8},4)
    assert vanished['kind']=='zero' and qr.tree_cost(vanished)['work']==1
    assert qr.evaluate_tree(vanished)==brute({7,8},4)==0
    bump('zero_factor_prunes_cubic_enumeration')
    return dict(cascade_cost=cost,cascade_signed_sum=qr.evaluate_tree(tree))


def native_check(result,native,rng,reference=None):
    desc=result['descriptor'];n=desc[1];k=2*len(desc[3])-1
    for _ in range(16):
        xs=[rng.getrandbits(n) for _ in range(k)]
        packed=sum(x << (i*n) for i,x in enumerate(xs))
        assert cc.anf_evaluate(result['phase'],packed)==boolean_output_phase(desc,xs)
        bump('original_output_phase_identities')
    answer=qr.evaluate_source(result,192)
    if reference is None:reference=fast_independent_probability(desc)
    assert answer['probability']==reference
    for bits in (2,192,4096):
        rounded=round_probability(reference,bits)
        assert 0<=reference-rounded<Fraction(1,1 << bits)
        if bits==192:assert rounded==answer['rounded']
        bump('precision_cases')
    bump('complete_native_output_evaluations')
    assert result['cost']['nodes']<=3*result['physical_bits']+1
    return answer


def isotropic_source(r,L,rng,hidden=False,flip=False):
    n=2*r
    J0=tuple(1 << ((i+r)%n) for i in range(n))
    P=hidden_basis(n,rng) if hidden else cc.identity(n)
    inv=cc.inverse(P);dual=cc.transpose(inv)
    J=cc.compose(dual,cc.compose(J0,inv))
    U=tuple(cc.transpose(inv)[i] for i in range(r))
    # U rows of inv, represented as physical covector columns.
    assert all((u&cc.action(cc.inverse(J),v)).bit_count()%2==0 for u in U for v in U)
    g={7 << j for j in range(0,r-2,3)}
    phase=sorted(pd.substitute_boolean(g,[(u,0) for u in U]))
    output=next(j for j in range(n) if any((u&cc.action(cc.inverse(J),1 << j)).bit_count()&1 for u in U))
    basis=(1 << output) if flip else 0
    desc=['cubic-field-v1',n,list(J),[list(phase) for _ in range(L)],basis,output]
    shift=cc.action(cc.inverse(J),1 << output)
    delta=sum(((u&shift).bit_count()&1) << j for j,u in enumerate(U))
    if L%2==0:p=Fraction(1,2)
    else:
        reduced=g if ((L+1)//2)%2 else set()
        signed=sum((-1)**(cc.anf_evaluate(reduced,z)^cc.anf_evaluate(reduced,z^delta))
                   for z in range(1 << r))
        p=Fraction((1 << r)-(-1 if flip else 1)*signed,1 << (r+1))
    return desc,p


def growing_sources(rng):
    records=[]
    cases=[(3,L,False,flip) for L in (1,2,3,5,9,17,33,65) for flip in ((False,True) if L%2 else (False,))]
    cases += [(3,9,True,False),(6,17,True,True),(12,17,False,False)]
    for r,L,hidden,flip in cases:
        desc,p=isotropic_source(r,L,rng,hidden,flip)
        native=cc.compile_native(desc)
        result=qr.reduce_native(native['qubits'],native['gates'],native['basis'],native['output'])
        assert result['cost']['max_width']==0,result['cost']
        answer=native_check(result,native,rng,p)
        if desc[1]<=6:
            assert p==fast_independent_probability(desc)
            bump('independent_small_state_probabilities')
        if r==3 and L in (1,3) and not hidden:
            check_native(native,p);bump('independent_literal_native_outputs')
        old_count=None
        if r==3 and not hidden:
            # Full three-variable cubic Walsh support at every nonterminal block;
            # the final nonzero derivative has quadratic Walsh support size four.
            old_count=1 << (6*L-4)
            if L<=3:
                old,why=cf.small_cubic_image(desc,3)
                assert old is not None,why
                actual=sum(1 for _ in pd.spectrum(old))
                assert actual==old_count,(actual,old_count)
                bump('old_walsh_branch_count_controls')
        records.append(dict(n=desc[1],layers=L,hidden=hidden,flip=flip,source_bits=native['source_bits'],
                            native_records=len(native['gates']),path_bits=result['physical_bits'],
                            cost=result['cost'],old_walsh_branch_count=str(old_count) if old_count else None,
                            probability=str(p)))
        print('Growing-layer exact output:',desc[1],L,hidden,p,result['cost'],flush=True)
    return records


def terminal(tree):
    if tree['kind']=='terminal':return tree
    if tree['kind']=='push':return terminal(tree['child'])
    raise AssertionError('expected a connected terminal')


def boundary_sources(rng):
    records=[]
    for k in (1,2,3,4,8,16):
        for flip in (False,True):
            n=2*k+1
            f={1 | (1 << (2*i+1)) | (1 << (2*i+2)) for i in range(k)}
            desc=['cubic-field-v1',n,list(cc.identity(n)),[sorted(f),sorted(f^{1} if flip else f)],0,0]
            native=cc.compile_native(desc)
            result=qr.reduce_native(n,native['gates'],0,0)
            leaf=terminal(result['tree']);width=4*k+1
            assert result['cost']['work']==1 << width and leaf['n']==width
            # The next-mechanism control only: a literal common cubic factor.
            common=(1 << width)-1
            for mask in leaf['phase']:
                if mask.bit_count()==3:common &= mask
            assert common.bit_count()==1
            j=common.bit_length()-1;parts=[]
            for bit in (0,1):
                columns=tuple(1 << i for i in range(width) if i!=j)
                restricted=pd.substitute_boolean(leaf['phase'],qr.affine_forms(bit << j,columns,width))
                assert all(mask.bit_count()<=2 for mask in restricted)
                parts.append(gauss(restricted,width-1))
            signed=(1 << result['tree']['push']['exponent'])*sum(parts)
            p=Fraction((1 << (2*n))-signed,1 << (2*n+1))
            expected=Fraction(1,4)+Fraction(1,1 << (k+2))
            if flip:expected=1-expected
            assert p==expected
            bump('two_gauss_terminal_controls',2)
            if k<=3:
                native_check(result,native,rng,p)
                assert p==fast_independent_probability(desc)
                bump('full_boundary_output_checks')
                if k==1:check_native(native,p);bump('independent_literal_native_outputs')
            if k>=2:assert p<=Fraction(1,3) or p>=Fraction(2,3)
            records.append(dict(k=k,n=n,path_bits=result['physical_bits'],terminal_bits=width,
                                terminal_work=str(result['cost']['work']),probability=str(p),
                                literal_common_factor=j,two_gauss_sums=list(map(str,parts)),
                                source_bits=native['source_bits'],native_records=len(native['gates']),
                                full_recursive_enumeration=k<=3))
    print('Connected terminal obstruction and two-Gauss controls pass',flush=True)
    return records


def assorted_native(rng):
    records=[]
    for n,L in ((3,1),(3,2),(3,3),(4,2),(4,3)):
        for _ in range(2):
            P=hidden_basis(n,rng);J=cc.compose(cc.transpose(P),P)
            phases=[[m for m in cc.anf_masks(n) if rng.getrandbits(1)] for _ in range(L)]
            desc=['cubic-field-v1',n,list(J),phases,rng.getrandbits(n),rng.randrange(n)]
            native=cc.compile_native(desc)
            result=qr.reduce_native(n,native['gates'],desc[4],desc[5])
            assert result['cost']['work']<=1 << 14,result['cost']
            answer=native_check(result,native,rng)
            records.append(dict(n=n,layers=L,cost=result['cost'],probability=str(answer['probability'])))
    altered=list(native['gates'])+[('Z',0)]
    try:qr.reduce_native(n,altered,desc[4],desc[5])
    except ValueError:bump('altered_source_refusals')
    else:raise AssertionError('altered source accepted')
    return records


def main():
    rng=random.Random(1730514)
    abstract=check_pushforwards(rng)
    print('Quadratic pushforward and recursive identity checks pass',flush=True)
    growing=growing_sources(rng)
    boundary=boundary_sources(rng)
    assorted=assorted_native(rng)
    prior=ROOT/'artifacts/s173-corrupted-field-contraction-checks.json'
    old=json.loads(prior.read_text());hashes={}
    for path in ['src/quadratic_pushforward_recursion.py','src/check_quadratic_pushforward_recursion.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730514,counts=COUNTS,abstract=abstract,growing_sources=growing,
                 terminal_boundaries=boundary,assorted_sources=assorted,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Exact source-derived recursive sums and growing-layer outputs. Star terminals enumerate only k<=3; larger cases verify the constructed terminal cost and separate two-quadratic-sum formula. No universal small-terminal claim or full-portfolio advantage.')
    target=ROOT/'artifacts/s173-quadratic-pushforward-recursion-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
