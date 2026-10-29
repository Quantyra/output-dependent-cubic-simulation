"""Independent rank, interval, source-access and precision checks for R05-22."""
import ast,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import linear_chain_counts as lc
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import gaussian_relation_transfer as gr
import phase_defect_tensors as pd
from finite_field_descent import echelon
from check_affine_map_transfer import twisted_cycle,independent_twisted_rank
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from check_cubic_centroid_descent import boolean_output_phase
from check_diagonal_control_sampling import all_aux_graph

ROOT=Path(__file__).resolve().parents[1];COUNTS={}


def bump(key,n=1):COUNTS[key]=COUNTS.get(key,0)+n


def invertible(n,rng):
    A=list(cc.identity(n))
    if n>1:
        for _ in range(5*n):
            a,b=rng.sample(range(n),2);A[a]^=A[b]
    return tuple(A)


def full_nullity(H,widths,word):
    """Literal full two-copy bilinear matrix, without chain decomposition."""
    offsets=[];M=0
    for k in widths:offsets.append(2*M);M+=k
    columns=[0]*(2*M);g=len(widths)
    for j,k in enumerate(widths):
        o=offsets[j]
        for i in range(k):
            for copy in range(2):
                at=o+copy*k+i
                columns[at]^=(1 << (o+i))|(1 << (o+k+i))
                if word >> j&1:columns[at]^=1 << at
        following=(j+1)%g
        for b,col in enumerate(H[j]):
            for a in pd.bits(col):
                for copy in range(2):
                    columns[offsets[following]+copy*widths[following]+b]^=1 << (o+copy*k+a)
    return 2*M-len(echelon(columns))


def rank_probability(H,widths):
    g=len(widths);M=sum(widths)
    total=sum((-1)**word.bit_count()*(1 << full_nullity(H,widths,word)) for word in range(1 << g))
    return (1-Fraction(total,1 << (M+g)))/2


def exhaustive_intervals(g,strings):
    return sum((-1)**s.bit_count()*(1 << sum(q*min(2,sum((s >> ((j-i)%g))&1 for i in range(ell)))
               for ell,j,q in strings)) for s in range(1 << g))


def from_strings(g,strings,regular,rng):
    """Build a known graded module, then hide every vertex basis."""
    widths=[regular]*g;chains=[]
    for ell,top,q in strings:
        for _ in range(q):
            chain=[]
            for h in range(ell):
                grade=(top-h)%g;chain.append((grade,widths[grade]));widths[grade]+=1
            chains.append(chain)
    H=[[0]*widths[(j+1)%g] for j in range(g)]
    for j in range(g):
        for i in range(regular):H[j][i]=1 << i
    for chain in chains:
        for (a,i),(b,j) in zip(chain,chain[1:]):H[b][i]=1 << j
    frames=[invertible(k,rng) for k in widths]
    hidden=[cc.compose(frames[j],cc.compose(h,cc.inverse(frames[(j+1)%g]))) for j,h in enumerate(H)]
    return hidden,widths


def mathematics_checks(rng):
    for g in range(1,8):
        for _ in range(12):
            widths=[rng.randrange(1,5) for _ in range(g)]
            H=[tuple(rng.getrandbits(widths[j]) for _ in range(widths[(j+1)%g])) for j in range(g)]
            result=lc.cycle_count(H,widths);profile=result['profile']
            for word in range(1 << g):
                defect=sum(q*min(2,sum(not(word >> ((j-i)%g)&1) for i in range(ell)))
                           for ell,j,q in profile['strings'])
                if word==(1 << g)-1:defect+=profile['regular_nullity']
                assert defect==full_nullity(H,widths,word)
                bump('independent_selector_rank_identities')
            assert result['probability']==rank_probability(H,widths)
            bump('independent_rectangular_cycle_outputs')
    for g in range(1,10):
        for _ in range(20):
            strings=[(rng.randrange(1,3*g+1),rng.randrange(g),rng.randrange(1,4)) for _ in range(7)]
            assert lc.interval_sum(g,strings)[0]==exhaustive_intervals(g,strings)
            bump('exhaustive_cyclic_interval_sums')
    for g in range(3,7):
        for regular in range(3):
            strings=[(1,j,1) for j in range(g)]+[(2*g+1,1,1),(g-1,g-1,2),(g,0,1)]
            H,widths=from_strings(g,strings,regular,rng);profile=lc.cycle_profile(H,widths)
            expected=Counter()
            for ell,j,q in strings:expected[ell,j]+=q
            assert Counter({(ell,j):q for ell,j,q in profile['strings']})==expected
            assert profile['regular_dimension']==regular
            assert profile['regular_nullity']==regular*(2 if g%2==0 else 1)
            bump('hidden_graded_rank_profile_recoveries')
    # Feasible rectangular pairings and exact rank-factor construction.
    for k in range(1,7):
        for _ in range(15):
            a=rng.randrange(k+1);b=rng.randrange(k+1)
            M=tuple(rng.getrandbits(a) for _ in range(b))
            feasible=k>=a+b-len(echelon(M))
            try:
                V,U=lc.realize_pair(k,a,b,M)
                assert feasible and len(echelon(V))==a and len(echelon(U))==b
                assert tuple(lc.it.signature(V,u) for u in U)==M
                bump('constructed_full_rank_pairings')
            except lc.Refusal:
                assert not feasible;bump('infeasible_pairing_refusals')
    records=[]
    for g in (8,16,32):
        # Supplied large graded modules test the bulk claim, not native access.
        strings=[(1,j,1) for j in range(g)]+[(g-1,j,1) for j in range(g)]
        F,stats=lc.interval_sum(g,strings)
        if g<=8:assert F==exhaustive_intervals(g,strings)
        records.append(dict(g=g,dimension=sum(ell*q for ell,j,q in strings),
                            control_words=1 << g,alternating_sum=str(F),stats=stats))
    return records


def rectangular_source(widths,H,flip=False):
    g=len(widths);offsets=[];n=0
    for k in widths:offsets.append(n);n+=2*k+1
    f=set();edges=set()
    for j,k in enumerate(widths):
        o=offsets[j]
        for i in range(k):f.add((1 << o)|(1 << (o+2*i+1))|(1 << (o+2*i+2)))
        nxt=offsets[(j+1)%g]
        for b,col in enumerate(H[j]):
            for a in pd.bits(col):edges.add((1 << (o+2*a+1))|(1 << (nxt+2*b+2)))
    P=list(cc.identity(n))
    for o in offsets[1:]:P[o]^=1
    inverse=cc.inverse(P);J=cc.compose(cc.transpose(inverse),inverse);forms=qr.affine_forms(0,inverse,n)
    phases=[pd.substitute_boolean(f^edges,forms),pd.substitute_boolean(f,forms)]
    if flip:phases[1]^={1 << j for j in pd.bits(J[0])}
    return ['cubic-field-v1',n,list(J),[sorted(p) for p in phases],0,0]


def native_case(widths,H,rng,label,hidden=False,flip=False,local=False):
    desc=rectangular_source(widths,H,flip)
    expected=rank_probability(H,widths)
    if flip:expected=1-expected
    if hidden:desc=transform_physical(desc,rng)
    native=cc.compile_native(desc)
    # No relation dictionary or exponential control reader may rescue this test.
    with patch.object(gr,'transfer',side_effect=AssertionError('forbidden relation fallback')):
        result=lc.reduce_native(desc[1],native['gates'],desc[4],desc[5],state_cap=1)
    detail=result['chain_counts']
    assert detail['certificates'] and not detail['refusals']
    with patch.object(cb,'evaluate_controls',side_effect=AssertionError('forbidden control enumeration')):
        for bits in (1,2,7,128,4096):
            answer=lc.evaluate_source(result,bits,max_work=1)
            assert answer['probability']==expected
            assert 0<=expected-answer['rounded']<Fraction(1,1 << bits)
            assert answer['error_bound']==expected-answer['rounded']
            assert answer['failure_probability']==answer['random_bits']==0
            bump('complete_native_precision_outputs')
    if desc[1]<=15:
        assert fast_independent_probability(desc)==expected;bump('independent_native_state_outputs')
        if desc[1]<=9:check_native(native,expected);bump('literal_native_gate_outputs')
    for certificate in detail['certificates']:
        for component in certificate['components']:
            # Reconstructed surrogate is independently ranked, at every selector.
            surrogate=component['matrices'];ks=[r['k'] for r in component['locals']]
            expected_count=(1-2*rank_probability(surrogate,ks))*(1 << (3*sum(ks)+len(ks)))
            assert component['count']['value']==expected_count
            bump('independent_reconstructed_cycle_counts')
            if local:
                for record in component['locals']:
                    k=record['k'];a=record['incoming_rank'];b=record['outgoing_rank']
                    V,U=lc.realize_pair(k,a,b,record['compressed_map'])
                    for inp in range(1 << (2*a)):
                        for out in range(1 << (2*b)):
                            expected_local=0
                            for word in range(2):
                                # Direct local u/v sum for an independently built factorization.
                                for vs in range(1 << (2*k)):
                                    v0=vs&((1 << k)-1);v1=vs >> k
                                    if lc.it.signature(V,v0)|(lc.it.signature(V,v1) << a)!=inp:continue
                                    p=out&((1 << b)-1);q=out >> b
                                    x0=v0^v1^(v0 if word else 0)^cc.action(U,p)
                                    x1=v0^v1^(v1 if word else 0)^cc.action(U,q)
                                    if x0==x1==0:expected_local+=(-1)**word*(1 << (2*k))
                            actual=sum(c*gr.kernel_value(key,inp,out) for key,c in record['kernels'])
                            assert actual==record['sign']*expected_local
                            bump('literal_local_model_entries')
    for _ in range(6):
        xs=[rng.getrandbits(desc[1]) for _ in range(3)]
        assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
        bump('original_source_phase_identities')
    record=dict(label=label,widths=widths,n=desc[1],source_bits=native['source_bits'],
                native_records=len(native['gates']),probability=str(expected),hidden=hidden,complement=flip,
                old_joint_branches=detail['retained']['current']['gaussian_sums'],remaining_work=result['cost']['work'],
                local_kernels=sum(c['local_gaussian_kernels'] for c in detail['certificates']),
                components=[dict(vertices=c['vertices'],stats=c['count']['stats'],
                                 nilpotent_strings=c['count']['profile']['strings'],
                                 regular_nullity=c['count']['profile']['regular_nullity'])
                            for cert in detail['certificates'] for c in cert['components']])
    bump('complete_original_native_outputs');print('Native chain count:',record,flush=True)
    return record


def native_checks(rng):
    cases=[
        ([1]*3,[(1,)]*3,'invertible_odd',False,False,True),
        ([2]*3,[(1,0),(0,2),(1,0)],'singular',False,False,True),
        ([2]*3,[(1,0),(0,2),(1,0)],'hidden_complement',True,True,True),
        ([1,2,2],[(1,1),(1,2),(3,)],'rectangular_widths',False,False,True),
        ([2]*4,[(1,2),(1,0),(2,3),(0,0)],'open_path_zero_edge',False,False,False),
        ([3]*4,[(1,2,4)]*3+[(1,0,2)],'wrapped_chains_regular_even',False,False,False),
        ([3]*5,[(1,2,4)]*4+[(1,0,2)],'wrapped_chains_regular_odd',False,False,False),
        ([3]*7,[tuple(rng.getrandbits(3) for _ in range(3)) for _ in range(7)],
         'arbitrary_growing_rank',False,False,False),
        ([2]*12,[(1 if x else 2,0) for x in (1,1,0,1,1,1)*2],'growing_g12',False,False,False)]
    records=[native_case(w,H,rng,label,hidden,flip,local) for w,H,label,hidden,flip,local in cases]
    # Zero edges may already be handled by the retained Gaussian support proof.
    for widths,H in (([1]*4,[(1,),(0,),(1,),(0,)]),([1]*3,[(0,)]*3)):
        d=rectangular_source(widths,H);r=lc.reduce_source(d,1)
        assert not r['chain_counts']['refusals']
        assert lc.evaluate_source(r,128,max_work=1)['probability']==rank_probability(H,widths)
        bump('retained_disconnected_zero_edge_outputs')
    # Two opposite edges between the same two blocks are outside the simple-cycle source theorem.
    widths=[1,2];H=[(1,0),(1,)];r=lc.reduce_source(rectangular_source(widths,H),1)
    assert not r['chain_counts']['certificates'] and r['chain_counts']['refusals']
    assert lc.evaluate_source(r,128,max_work=1)['mode']=='budget_refused'
    bump('bidirectional_two_vertex_source_refusal')
    generic=twisted_cycle(2,3,[(1,2)]*3)
    generic[3][0]=sorted(set(generic[3][0])^{(1 << 1)|(1 << 3),1 << 2});generic[4]=1 << 6
    r=lc.reduce_source(generic)
    assert not r['chain_counts']['certificates'] and r['chain_counts']['refusals']
    assert r['chain_counts']['relation_fallback'][0]['accepted']
    assert lc.evaluate_source(r,4096,max_work=1)['probability']==fast_independent_probability(generic)
    bump('generic_phase_refusal_with_exact_relation_fallback')
    dense=all_aux_graph(1,4,[(a,b) for a in range(4) for b in range(4) if a!=b])
    r=lc.reduce_source(dense,state_cap=1)
    assert not r['chain_counts']['certificates']
    assert any(x['reason']=='interaction_degree' for x in r['chain_counts']['refusals'])
    assert lc.evaluate_source(r,100,max_work=1)['mode']=='budget_refused'
    bump('native_degree_and_retained_work_refusal')
    return records



def linear_character_checks():
    """Next mechanism only: exact local identity, not an affine source reader."""
    import cubic_linear_factors as lf
    rng=random.Random(1730532)
    for ell in range(1,7):
        for word in range(1 << ell):
            zeros=[i for i in range(ell) if not(word >> i&1)]
            for _ in range(4):
                a=rng.getrandbits(ell);b=rng.getrandbits(ell);phase=set()
                for i in range(ell):
                    for c in range(2):
                        for d in range(2):
                            if c!=d or not(word >> i&1):
                                phase.add((1 << (c*ell+i))|(1 << ((2+d)*ell+i)))
                        if i+1<ell:phase.add((1 << (c*ell+i))|(1 << ((2+c)*ell+i+1)))
                        if a >> i&1:phase.add(1 << (c*ell+i))
                        if b >> i&1:phase.add(1 << ((2+c)*ell+i))
                alpha=(a >> zeros[-1]).bit_count()%2 if zeros else 0
                beta=(b&((1 << (zeros[0]+1))-1)).bit_count()%2 if zeros else 0
                expected=1 if not zeros else 2*(-1)**(alpha*beta) if len(zeros)==1 else 4*int(alpha==beta==0)
                assert lf.quadratic_value(phase,4*ell)==expected*(1 << (2*ell))
                bump('next_linear_field_chain_character_identity')


def main():
    rng=random.Random(1730531);bulk=mathematics_checks(rng)
    linear_character_checks()
    print('Rank identities, cyclic interval sums, wrapped graded profiles and pairings pass',flush=True)
    native=native_checks(rng)
    prior=ROOT/'artifacts/s173-gaussian-relation-transfer-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/linear_chain_counts.py','src/check_linear_chain_counts.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730531,counts=COUNTS,native_sources=native,bulk_supplied_profiles=bulk,
                 hashes=hashes,prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Exact source-derived linear-cycle aggregation with arbitrary singular rectangular edge maps; graded rank profiles and cyclic-interval DP remove supplied Jordan bases and exponential selector enumeration. Full source and precision-bit costs paid. Arbitrary graphs, phases, longer words and universal/language claims remain open.')
    target=ROOT/'artifacts/s173-linear-chain-counts-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
