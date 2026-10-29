"""Exact checks of one/two exterior control discovery and native costs."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from rank_one_field_correction import round_probability

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def brute(poly,n):
    return sum((-1)**cc.anf_evaluate(poly,x) for x in range(1 << n))


def direct_wedge(lam,cubic):
    result=set()
    for mask in cubic:
        for j in pd.bits(lam&~mask):
            term=mask|(1 << j)
            if term in result:result.remove(term)
            else:result.add(term)
    return result


def coefficient_checks(rng):
    cases=[]
    for n in (3,4,5):
        cubes=[m for m in cc.anf_masks(n) if m.bit_count()==3]
        cases.extend((n,{mask for j,mask in enumerate(cubes) if value >> j & 1})
                     for value in range(1 << len(cubes)))
    for n in (6,7,8):
        cases.extend((n,{m for m in cc.anf_masks(n) if m.bit_count()==3 and rng.getrandbits(1)})
                     for _ in range(12))
    for n,cubic in cases:
        basis=lf.linear_wedge_kernel(cubic,n);span=echelon(basis)
        for lam in range(1 << n):
            assert (solve(span,lam) is not None)==(not direct_wedge(lam,cubic))
            bump('independent_linear_wedge_memberships')
        if cubic:assert len(basis) in (0,1,3)
        poly=cubic^{m for m in cc.anf_masks(n,2) if rng.getrandbits(1)}
        certificate=lf.discover_factor(poly,n)
        if certificate is not None:
            assert certificate['value']==brute(poly,n)
            assert all(max((m.bit_count() for m in q),default=0)<=2 for q in certificate['phases'])
            bump('exact_factor_values')
        else:
            tree,details=lf.compile_sum(poly,n)
            assert qr.evaluate_tree(tree)==brute(poly,n)
            bump('exact_fallback_values')
    return len(cases)


def hidden_factor_checks(rng):
    records=[]
    for k in range(1,6):
        n=2*k+1
        cubic={1|(1 << (2*i+1))|(1 << (2*i+2)) for i in range(k)}
        for _ in range(6):
            q={m for m in cc.anf_masks(n,2) if rng.getrandbits(1)}
            P=hidden_basis(n,rng);offset=rng.getrandbits(n)
            changed=pd.substitute_boolean(cubic^q,qr.affine_forms(offset,P,n))
            certificate=lf.discover_factor(changed,n)
            assert certificate is not None and certificate['control_rank']==1
            if k>=2:
                expected=cc.action(cc.transpose(P),1)
                assert certificate['linear_kernel']==(expected,)
                if expected.bit_count()>1:bump('hidden_noncoordinate_factors')
            assert certificate['value']==brute(changed,n)
            for b,origin in enumerate(certificate['origins']):
                for _ in range(8):
                    y=rng.getrandbits(n-1);x=origin^cc.action(certificate['columns'],y)
                    assert ((certificate['factor']&x).bit_count()&1)==b
                    assert cc.anf_evaluate(changed,x)==cc.anf_evaluate(certificate['phases'][b],y)
                    bump('full_affine_restriction_values')
            bump('hidden_affine_factor_values')
            records.append(dict(n=n,kernel_dimension=len(certificate['linear_kernel']),
                                factor_weight=certificate['factor'].bit_count()))
    return records


def star_blocks(k,blocks=1,flip=False):
    d=2*k+1;n=blocks*d;f=set();coupling=set()
    for block in range(blocks):
        offset=block*d
        for i in range(k):f.add((1 << offset)|(1 << (offset+2*i+1))|(1 << (offset+2*i+2)))
    for block in range(blocks-1):
        coupling.add((1 << (block*d+1))|(1 << ((block+1)*d+1)))
    P=list(cc.identity(n))
    for block in range(1,blocks):P[block*d] ^= 1
    inverse=cc.inverse(P);J=cc.compose(cc.transpose(inverse),inverse)
    forms=qr.affine_forms(0,inverse,n)
    phases=[pd.substitute_boolean(f^coupling,forms),pd.substitute_boolean(f,forms)]
    if flip:phases[1] ^= {1 << j for j in pd.bits(J[0])}
    desc=['cubic-field-v1',n,list(J),[sorted(p) for p in phases],0,0]
    p=(1-(Fraction(1,2)-Fraction(1,1 << (k+1)))**blocks)/2
    return desc,1-p if flip else p


def pointwise_source(result,rng):
    desc=result['descriptor'];n=desc[1]
    for _ in range(16):
        xs=[rng.getrandbits(n) for _ in range(2*len(desc[3])-1)]
        packed=sum(x << (i*n) for i,x in enumerate(xs))
        assert cc.anf_evaluate(result['phase'],packed)==boolean_output_phase(desc,xs)
        bump('original_output_phase_identities')


def native_sources(rng):
    records=[]
    for blocks,ks in ((1,(1,2,3,4,8,16)),(2,(1,2,3,4))):
        for k in ks:
            for flip in (False,True):
                desc,p=star_blocks(k,blocks,flip);native=cc.compile_native(desc)
                result=lf.reduce_native(native['qubits'],native['gates'],0,0)
                details=result['factor_discovery']
                assert details['previous']['max_width']==blocks*(4*k+1)
                assert details['quadratic_sums']==1 << blocks and details['factors_found']==1
                certificate=details['certificates'][0]
                assert certificate['control_rank']==blocks
                if blocks==2:assert certificate['quadratic_kernel_dimension']==1
                assert result['cost']['max_width']==0 and result['cost']['work']==1
                pointwise_source(result,rng)
                answer=lf.evaluate_source(result,192);assert answer['probability']==p
                for bits in (2,192,4096):
                    rounded=round_probability(p,bits)
                    assert 0<=p-rounded<Fraction(1,1 << bits)
                    if bits==192:assert rounded==answer['rounded']
                    bump('precision_cases')
                if desc[1]<=10:
                    assert p==fast_independent_probability(desc);bump('independent_state_outputs')
                if k==1:
                    check_native(native,p);bump('independent_literal_native_outputs')
                if blocks==1 and k>=2:assert p<=Fraction(1,3) or p>=Fraction(2,3)
                bump('complete_native_factor_outputs')
                records.append(dict(blocks=blocks,k=k,n=desc[1],flip=flip,source_bits=native['source_bits'],
                                    native_records=len(native['gates']),path_bits=result['physical_bits'],
                                    old_width=details['previous']['max_width'],
                                    old_work=str(details['previous']['work']),new_cost=result['cost'],
                                    control_rank=certificate['control_rank'],
                                    quadratic_kernel_dimension=certificate['quadratic_kernel_dimension'],
                                    quadratic_sums=details['quadratic_sums'],probability=str(p)))
                print('Native factor readout:',blocks,k,flip,p,details['quadratic_sums'],flush=True)
    altered=list(native['gates'])+[('Z',0)]
    try:lf.reduce_native(native['qubits'],altered,0,0)
    except ValueError:bump('modified_native_source_refusals')
    else:raise AssertionError('modified source accepted')
    return records


def terminal(tree):
    while tree['kind']=='push':tree=tree['child']
    assert tree['kind']=='terminal'
    return tree


def reparameterized_outputs(rng):
    records=[]
    for k in (1,2):
        desc,p=star_blocks(k);original,m=qr.original_output_phase(desc)
        for _ in range(6):
            change=hidden_basis(m,rng);offset=rng.getrandbits(m)
            poly=pd.substitute_boolean(original,qr.affine_forms(offset,change,m))
            tree=qr.compile_sum(poly,m);leaf=terminal(tree)
            common=(1 << leaf['n'])-1
            for mask in leaf['phase']:
                if mask.bit_count()==3:common &= mask
            details=lf.enhance_tree(tree)
            assert details['factors_found']==1
            signed=qr.evaluate_tree(tree)
            assert signed==(1 << (2*desc[1]))*(1-2*p)
            for _ in range(12):
                x=rng.getrandbits(m)
                assert cc.anf_evaluate(poly,x)==cc.anf_evaluate(original,offset^cc.action(change,x))
                bump('native_path_affine_reparameterization_values')
            if common==0:
                assert details['certificates'][0]['factor'].bit_count()>1
                bump('no_visible_monomial_factor_native_paths')
            records.append(dict(k=k,path_bits=m,visible_factor=common,
                                discovered_weight=details['certificates'][0]['factor'].bit_count(),
                                signed_sum=str(signed),
                                scope='bijective affine change of the original path variables; original circuit unchanged'))
    return records


def composition_and_boundary(rng):
    products=[]
    for count in range(1,9):
        poly={mask << (5*j) for j in range(count) for mask in (7,25)}
        tree,details=lf.compile_sum(poly,5*count)
        assert details['quadratic_sums']==2*count
        assert qr.evaluate_tree(tree)==20**count
        bump('independent_factor_product_cases')
        products.append(dict(factors=count,quadratic_sums=2*count,value=str(20**count)))
    # A newly computed zero factor removes an unsupported three-factor sibling.
    zero={7,25,6,10,20,1}
    assert lf.discover_factor(zero,5)['value']==0
    unsupported={7,56,448,12,96}
    assert not lf.linear_wedge_kernel(unsupported,9)
    assert not lf.quadratic_wedge_kernel(unsupported,9)[1]
    tree,details=lf.compile_sum(zero^{m << 5 for m in unsupported},14)
    assert tree['kind']=='zero' and details['current']['work']==1
    assert qr.evaluate_tree(tree)==0
    bump('new_factor_zero_prunes_unsupported_sibling')
    # Exact source-level remaining boundary; no hard-instance claim.
    records=[]
    for blocks,k in ((3,1),(3,2),(4,1)):
        desc,p=star_blocks(k,blocks);native=cc.compile_native(desc)
        result=lf.reduce_native(desc[1],native['gates'],0,0)
        leaf=terminal(result['tree'])
        assert result['factor_discovery']['factors_found']==0
        assert leaf['n']==blocks*(4*k+1)
        assert not lf.linear_wedge_kernel(leaf['phase'],leaf['n'])
        assert not lf.quadratic_wedge_kernel(leaf['phase'],leaf['n'])[1]
        if blocks==3 and k==1:
            assert lf.evaluate_source(result,128)['probability']==p==fast_independent_probability(desc)
            bump('complete_remaining_boundary_output')
        pointwise_source(result,rng)
        records.append(dict(blocks=blocks,k=k,n=desc[1],terminal_width=leaf['n'],
                            terminal_work=str(result['cost']['work']),reference_probability=str(p),
                            full_recursive_evaluation=blocks==3 and k==1))
    return dict(products=products,remaining_native_boundaries=records)


def preserved_route(rng):
    from check_quadratic_pushforward_recursion import isotropic_source
    desc,p=isotropic_source(3,33,rng,True,False)
    native=cc.compile_native(desc)
    result=lf.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert result['factor_discovery']['factor_tests']==0
    assert lf.evaluate_source(result,128)['probability']==p
    bump('retained_growing_layer_output')
    return dict(n=desc[1],layers=33,probability=str(p),cost=result['cost'])


def symmetric_reference(n):
    """Independent weight-class integer Hadamards, not path/factor discovery."""
    def transform(values):
        return [sum(values[k]*sum((-1)**j*comb(w,j)*comb(n-w,k-j)
                                 for j in range(max(0,k-(n-w)),min(w,k)+1))
                    for k in range(n+1)) for w in range(n+1)]
    values=[1]+[0]*n;values=transform(values)
    for _ in range(2):
        values=[v*(-1)**(comb(w,3) if w>=3 else 0) for w,v in enumerate(values)]
        values=transform(values)
    return Fraction(sum(comb(n-1,w-1)*values[w]**2 for w in range(1,n+1)),1 << (3*n))


def coordinate_cover_gap(rng):
    abstract=[];native=[]
    for n in (5,7,9,17,33,65):
        poly={sum(1 << j for j in ids) for ids in combinations(range(n),3)}
        cert=lf.discover_factor(poly,n)
        assert cert is not None and cert['control_rank']==1
        assert cert['factor']==(1 << n)-1
        expected=sum(comb(n,w)*(-1)**(comb(w,3) if w>=3 else 0) for w in range(n+1))
        assert cert['value']==expected
        # Every three unconditioned coordinates leave their cubic monomial.
        # Deleting n-2 coordinates hits every triple, so the optimum is exact.
        assert len(poly)==comb(n,3)
        bump('dense_parity_factor_gap_cases')
        abstract.append(dict(n=n,coordinate_controls=n-2,coordinate_branches=str(1 << (n-2)),
                             discovered_controls=1,quadratic_sums=2,value=str(expected)))
    for n in (5,7,9,11,13,17):
        f=[sum(1 << j for j in ids) for ids in combinations(range(n),3)]
        desc=['cubic-field-v1',n,list(cc.identity(n)),[f,f],0,0]
        source=cc.compile_native(desc);result=lf.reduce_native(n,source['gates'],0,0)
        p=lf.evaluate_source(result,192)['probability']
        assert p==symmetric_reference(n)
        assert result['factor_discovery']['factors_found']==1
        assert result['factor_discovery']['quadratic_sums']==4
        pointwise_source(result,rng)
        if n<=9:assert p==fast_independent_probability(desc)
        bump('dense_native_factor_outputs')
        native.append(dict(n=n,source_bits=source['source_bits'],native_records=len(source['gates']),
                           old_width=result['factor_discovery']['previous']['max_width'],
                           new_cost=result['cost'],probability=str(p),reference='weight-class Hadamards'))
    return dict(abstract=abstract,native=native)


def main():
    rng=random.Random(1730517)
    cases=coefficient_checks(rng);hidden=hidden_factor_checks(rng)
    print('Exterior equations and full hidden-affine phases pass',flush=True)
    native=native_sources(rng);reparameterized=reparameterized_outputs(rng)
    boundary=composition_and_boundary(rng);retained=preserved_route(rng)
    cover=coordinate_cover_gap(rng)
    prior=ROOT/'artifacts/s173-quadratic-pushforward-recursion-checks.json'
    old=json.loads(prior.read_text());hashes={}
    for path in ['src/cubic_linear_factors.py','src/check_cubic_linear_factors.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730517,counts=COUNTS,coefficient_cases=cases,
                 hidden_affine_cases=hidden,native_sources=native,path_reparameterizations=reparameterized,
                 composition_and_boundaries=boundary,retained_growing_case=retained,
                 coordinate_cover_gap=cover,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Source-derived one/two controlling covectors and complete native outputs. One-factor detection is complete; two-form detection tests an explicit kernel basis, complete on the proved one-dimensional two-star family. Three/four-star kernel obstructions are not hardness; only the smallest remaining boundary is fully enumerated.')
    target=ROOT/'artifacts/s173-cubic-linear-factor-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
