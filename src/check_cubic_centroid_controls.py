"""Independent checks of centroid blocks and joint control readout."""
import ast
import hashlib
import json
import random
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import cubic_centroid_controls as cb
import cubic_centroid_descent as cc
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
import finite_field_acceptance as ff
from finite_field_descent import echelon,solve,xor_sum
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_cubic_linear_factors import star_blocks
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(key,amount=1):
    COUNTS[key]=COUNTS.get(key,0)+amount


def brute(poly,n):
    return sum(-1 if cc.anf_evaluate(poly,x) else 1 for x in range(1 << n))


def field_phase(s,modulus):
    K=ff.Field(modulus);mask=(1 << s)-1
    return set(cc.anf_from_function(3*s,lambda x:K.trace(
        K.mul(K.mul(x&mask,(x >> s)&mask),(x >> (2*s))&mask))))


def stars(widths):
    result=set();offset=0
    for width in widths:
        assert width>=3 and width%2
        for i in range(1,width,2):
            result.add((1 << offset)|(1 << (offset+i))|(1 << (offset+i+1)))
        offset+=width
    return result


def coordinate_projectors(widths):
    n=sum(widths);offset=0;result=[]
    for width in widths:
        keep=((1 << width)-1) << offset
        result.append(tuple((1 << j) if keep >> j & 1 else 0 for j in range(n)))
        offset+=width
    return result


def algebra_checks(rng):
    cases=[(3,{7}),(5,{7,25}),(6,{7,56}),(6,field_phase(2,7)),
           (9,field_phase(3,11)),(6,{37,25,22})]
    for n in (4,5,6,7):
        for _ in range(8):
            f={m for m in cc.anf_masks(n) if m.bit_count()==3 and rng.getrandbits(1)}
            if len(echelon(row for rows in pd.cubic_tensor(f,n) for row in rows))==n:
                cases.append((n,f))
    records=[]
    for n,f in cases:
        d=cb.centroid_blocks(f,n);basis=d['centroid_basis'];idem=d['idempotents']
        assert len(basis)<=8
        idempotent_span=echelon([cc.flatten(t) for t in idem])
        actual=set()
        for word in range(1 << len(basis)):
            T=cc.unflatten(xor_sum(cc.flatten(t) for j,t in enumerate(basis) if word >> j & 1),n)
            valid=cc.compose(T,T)==T
            assert valid==(solve(idempotent_span,cc.flatten(T)) is not None)
            if valid:actual.add(cc.flatten(T))
            bump('exhaustive_centroid_idempotent_memberships')
        projectors=d['projectors']
        sums={xor_sum(cc.flatten(p) for j,p in enumerate(projectors) if word >> j & 1)
              for word in range(1 << len(projectors))}
        assert actual==sums
        bump('complete_primitive_projector_cases')
        # A direct cubic tensor contraction, independent of the equation builder.
        rows=pd.cubic_tensor(f,n)
        def tensor(x,y,z):
            return xor_sum((rows[i][j]&z).bit_count()&1
                           for i in pd.bits(x) for j in pd.bits(y))
        for T in basis:
            for _ in range(12):
                x,y,z=(rng.getrandbits(n) for _ in range(3))
                assert tensor(cc.action(T,x),y,z)==tensor(x,cc.action(T,y),z)==tensor(x,y,cc.action(T,z))
                bump('independent_centroid_slot_identities')
        records.append(dict(n=n,centroid=len(basis),idempotents=len(idem),
                            blocks=[len(b) for b in d['blocks']]))
    dual=cb.centroid_blocks({37,25,22},6)
    assert dual['centroid_dimension']==2 and dual['idempotent_dimension']==1
    assert any(any(t) and not any(cc.compose(t,t)) for t in dual['centroid_basis'])
    bump('nilpotent_not_split')
    try:cb.centroid_blocks({7},4)
    except ValueError:bump('nonfull_mode_refusal')
    else:raise AssertionError('radical not refused')
    return records


def hidden_and_coupled(rng):
    records=[];naive_failures=0;hidden_failures=0
    for widths,attempts in [((3,3,3),10),((3,3,3,3),6),((5,5,5),4)]:
        n=sum(widths);cubic=stars(widths)
        for trial in range(attempts):
            lower={m for m in cc.anf_masks(n,2) if rng.randrange(4)==0}
            # Force connectivity, while retaining every random lower term.
            offset=0
            for width in widths[:-1]:
                lower.add((1 << offset)|(1 << (offset+width)));offset+=width
            original=cubic^lower;reference=brute(original,n)
            P=hidden_basis(n,rng);inverse=cc.inverse(P);origin=rng.getrandbits(n)
            poly=pd.substitute_boolean(original,qr.affine_forms(origin,P,n))
            certificate,why=cb.discover_controls(poly,n)
            assert certificate is not None,why
            assert certificate['control_rank']==len(widths)
            assert cb.evaluate_controls(certificate)==reference
            expected={cc.flatten(cc.compose(inverse,cc.compose(E,P)))
                      for E in coordinate_projectors(widths)}
            found={cc.flatten(E) for E in certificate['decomposition']['projectors']}
            assert found==expected
            bump('hidden_affine_projector_recoveries')
            if len(qr.components({m for m in poly if m.bit_count()==3},n))==1:
                hidden_failures+=1;bump('no_visible_cubic_block_partition')
            for assignment in range(1 << certificate['control_rank']):
                quadratic=cb.restricted_quadratic(certificate,assignment)
                for _ in range(4):
                    y=rng.getrandbits(n-certificate['control_rank'])
                    packed=assignment|(y << certificate['control_rank'])
                    x=cc.action(certificate['columns'],packed)
                    assert cc.anf_evaluate(quadratic,y)==cc.anf_evaluate(poly,x)
                    bump('full_conditional_phase_identities')
            for _ in range(8):
                x=rng.getrandbits(n)
                assert cc.anf_evaluate(poly,x)==cc.anf_evaluate(original,origin^cc.action(P,x))
                bump('hidden_affine_bijection_values')
            transformed=certificate['decomposition']['phase']
            naive=-1 if 0 in transformed else 1;offset=0
            for block in certificate['decomposition']['blocks']:
                w=len(block);keep=((1 << w)-1) << offset
                local={m >> offset for m in transformed if m and m&keep==m}
                naive*=brute(local,w);offset+=w
            if naive!=reference:naive_failures+=1;bump('discarding_quadratic_bridges_changes_value')
            records.append(dict(widths=widths,n=n,controls=certificate['control_rank'],
                                value=str(reference),naive_product=str(naive)))
    assert naive_failures and hidden_failures
    # A nonsplit field block can need two local controls.
    f=field_phase(2,7)^{m << 6 for m in (7,25)}^{(1 << 2)|(1 << 7),1,0}
    P=hidden_basis(11,rng)
    hidden=pd.substitute_boolean(f,qr.affine_forms(0,P,11))
    tree,details=cb.compile_sum(hidden,11)
    assert details['retained']['factors_found']==0
    cert=details['certificates'][0]
    assert sorted(c['rank'] for c in cert['local'])==[1,2]
    assert cb.evaluate_tree(tree)==brute(f,11)
    bump('mixed_one_two_control_blocks')
    return records


def source_identities(result,rng):
    desc=result['descriptor'];n=desc[1]
    for _ in range(12):
        xs=[rng.getrandbits(n) for _ in range(2*len(desc[3])-1)]
        packed=sum(x << (j*n) for j,x in enumerate(xs))
        assert cc.anf_evaluate(result['phase'],packed)==boolean_output_phase(desc,xs)
        bump('original_output_phase_identities')


def transform_physical(desc,rng):
    _,n,J,phases,basis,output=desc
    assert output==0
    P=list(cc.identity(n))
    for _ in range(4*n):
        b=rng.randrange(1,n);a=rng.choice([j for j in range(n) if j!=b])
        P=[x^(((x >> a)&1) << b) for x in P]
    assert cc.transpose(P)[0]==1
    Jnew=cc.compose(cc.transpose(P),cc.compose(J,P))
    transformed=[sorted(pd.substitute_boolean(f,qr.affine_forms(0,P,n))) for f in phases]
    return ['cubic-field-v1',n,list(Jnew),transformed,cc.action(cc.inverse(P),basis),0]


def native_checks(rng):
    records=[]
    cases=[(g,1,flip,False) for g in (3,4,5,6,8) for flip in (False,True)]
    cases +=[(3,k,flip,False) for k in (2,3,4) for flip in (False,True)]
    cases +=[(3,1,False,True),(3,1,True,True),(3,2,False,True)]
    for g,k,flip,hidden in cases:
        desc,p=star_blocks(k,g,flip)
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc)
        result=cb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        detail=result['centroid_controls'];cert=detail['certificates'][0]
        assert detail['retained']['factors_found']==0
        assert detail['retained']['current']['max_width']==g*(4*k+1)
        assert len(cert['decomposition']['blocks'])==g
        assert sorted(len(b) for b in cert['decomposition']['blocks'])==[4*k+1]*g
        assert result['cost']['gaussian_sums']==1 << g
        assert result['cost']['unsupported_work']==0
        for bits in (1,128,4096):
            answer=cb.evaluate_source(result,bits)
            assert answer['probability']==p
            assert 0<=p-answer['rounded']<Fraction(1,1 << bits)
            bump('complete_precision_evaluations')
        source_identities(result,rng)
        if desc[1]<=12:
            assert p==fast_independent_probability(desc);bump('independent_state_outputs')
        if desc[1]<=9:
            check_native(native,p);bump('independent_literal_native_outputs')
        bump('complete_native_outputs')
        records.append(dict(blocks=g,k=k,hidden_physical_basis=hidden,flip=flip,n=desc[1],
                            source_bits=native['source_bits'],native_records=len(native['gates']),
                            path_bits=result['physical_bits'],old_width=g*(4*k+1),
                            old_work=str(detail['retained']['current']['work']),
                            new_cost=result['cost'],block_sizes=[len(b) for b in cert['decomposition']['blocks']],
                            probability=str(p)))
        print('Native centroid readout:',g,k,flip,hidden,p,result['cost']['gaussian_sums'],flush=True)
    altered=list(native['gates'])+[('Z',0)]
    try:cb.reduce_native(desc[1],altered,desc[4],desc[5])
    except ValueError:bump('modified_native_source_refusal')
    else:raise AssertionError('modified source accepted')
    return records


def boundaries_and_composition(rng):
    fields=[]
    for s,modulus in ((3,11),(4,19),(5,37)):
        f=field_phase(s,modulus);n=3*s;expected=(1 << s)*((1 << (s+1))-1)
        assert not lf.linear_wedge_kernel(f,n) and not lf.quadratic_wedge_kernel(f,n)[1]
        tree,details=cb.compile_sum(f,n)
        assert len(details['refusals'])==1
        d=details['refusals'][0]['decomposition']
        assert d['centroid_dimension']==s and d['idempotent_dimension']==1
        assert len(d['blocks'])==1 and details['current']['unsupported_work']==1 << n
        assert cb.evaluate_tree(tree)==brute(f,n)==expected
        bump('indecomposable_field_obstruction')
        fields.append(dict(s=s,n=n,value=expected,cost=dict(details['current'])))
    # A product adds branch counts. An old factor zero still prunes before enumeration.
    group=stars((3,3,3))^{(1 << 0)|(1 << 3),(1 << 3)|(1 << 6)}
    reference=brute(group,9)
    products=[]
    for count in (1,2,3,5):
        poly={mask << (9*j) for j in range(count) for mask in group}
        tree,details=cb.compile_sum(poly,9*count)
        assert details['current']['gaussian_sums']==8*count
        assert cb.evaluate_tree(tree)==reference**count
        bump('independent_component_additive_costs')
        products.append(dict(components=count,gaussian_sums=8*count,value=str(reference**count)))
    zero={7,25,6,10,20,1}
    f=field_phase(3,11)
    tree,details=cb.compile_sum(zero^{m << 5 for m in f},14)
    assert tree['kind']=='zero' and cb.evaluate_tree(tree)==0 and details['block_tests']==0
    bump('retained_zero_prunes_unsupported_sibling')
    from check_quadratic_pushforward_recursion import isotropic_source
    desc,p=isotropic_source(3,33,rng,True,False)
    native=cc.compile_native(desc)
    result=cb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert result['centroid_controls']['block_tests']==0
    assert cb.evaluate_source(result,128)['probability']==p
    bump('retained_growing_layer_output')
    desc,p=star_blocks(2,2);native=cc.compile_native(desc)
    result=cb.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    assert result['centroid_controls']['block_tests']==0
    assert result['centroid_controls']['retained']['quadratic_sums']==4
    assert cb.evaluate_source(result,128)['probability']==p
    bump('retained_two_control_output')
    return dict(field_boundaries=fields,products=products)


def main():
    rng=random.Random(1730518)
    algebra=algebra_checks(rng);hidden=hidden_and_coupled(rng)
    print('Centroid algebra, hidden projectors and full coupled restrictions pass',flush=True)
    native=native_checks(rng);boundary=boundaries_and_composition(rng)
    prior=ROOT/'artifacts/s173-cubic-linear-factor-checks.json';old=json.loads(prior.read_text())
    hashes={}
    for path in ['src/cubic_centroid_controls.py','src/check_cubic_centroid_controls.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730518,counts=COUNTS,algebra=algebra,
                 hidden_affine_cases=hidden,native_sources=native,boundary_and_composition=boundary,
                 hashes=hashes,prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='S089 centroid splitting reused; new joint-control readout preserves quadratic bridges. All listed native outputs complete. Joint assignments stream with polynomial storage; their 2^q cost remains. Field-centroid refusal is a reader limit, not hardness or a full-portfolio failure.')
    target=ROOT/'artifacts/s173-cubic-centroid-control-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
