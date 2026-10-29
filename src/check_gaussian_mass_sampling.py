"""Independent conditional distributions, recursive normalization and native sampling checks."""
import ast,hashlib,json,random
from fractions import Fraction
from itertools import product,combinations
from math import comb
from pathlib import Path
from unittest.mock import patch
import gaussian_mass_sampling as gs
import gaussian_message_norms as gm
import gaussian_pair_envelopes as pe
import cubic_centroid_controls as cb
import cubic_centroid_descent as cc
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
from check_gaussian_message_norms import branch_value,graph_probability,all_aux_cycle
from check_gaussian_block_cuts import dense_source
from check_gaussian_pair_envelopes import BOUNDARY_EDGES
from check_cubic_centroid_controls import brute,field_phase,transform_physical
from check_cubic_centroid_descent import hidden_basis,boolean_output_phase
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}


def bump(name,n=1):COUNTS[name]=COUNTS.get(name,0)+n


class Tape:
    def __init__(self,word,length):self.word=word;self.length=length;self.used=0
    def getrandbits(self,n):
        assert self.used+n<=self.length
        value=(self.word >> self.used)&((1 << n)-1);self.used+=n
        return value


class NoCoins:
    def getrandbits(self,n):raise AssertionError('unexpected random draw')


def values(mixture):
    return [sum(branch_value(b,y) for b in mixture['branches']) for y in range(1 << mixture['width'])]


def direct_distribution(weights,L):
    """Independent quantized prefix law using an explicit original truth table."""
    total=sum(abs(x) for x in weights);width=(len(weights)-1).bit_length();result=[]
    for y,value in enumerate(weights):
        probability=Fraction(1);prefix=0
        for j in range(width):
            candidates=[x for x in range(len(weights)) if x&((1 << j)-1)==prefix]
            mass=sum(abs(weights[x]) for x in candidates)
            if not mass:probability=Fraction(0);break
            zero=sum(abs(weights[x]) for x in candidates if not x >> j&1)
            cutoff=(zero << L)//mass;bit=y >> j&1
            probability*=Fraction((1 << L)-cutoff if bit else cutoff,1 << L)
            prefix|=bit << j
        result.append(probability)
    assert sum(result)==1 and all(not p or weights[y] for y,p in enumerate(result))
    tv=sum(abs(p-Fraction(abs(value),total)) for p,value in zip(result,weights))/2
    assert tv<=Fraction(width,1 << L)
    return result,tv


def mixture_checks(rng):
    specimens=[];prefixes=0
    for width in range(6):
        for t in (1,2,4):
            branches=[]
            for i in range(t):
                P=hidden_basis(width,rng) if width>=2 else cc.identity(width)
                d=rng.randrange(width+1)
                phase={m for m in cc.anf_masks(d,2) if rng.getrandbits(1)}
                branches.append(gm.affine_branch(width,rng.getrandbits(width),P[:d],phase,2*i+1))
            mix=gs.prepare_mixture(branches,width);table=values(mix)
            assert mix['mass']==sum(abs(v) for v in table)
            for length in range(width+1):
                for prefix in range(1 << length):
                    restricted=tuple(branches)
                    for j in range(length):restricted=gs.restrict_bit(restricted,j,prefix >> j&1)
                    norm=gm.absolute_mass(restricted,width)
                    expected=sum(abs(v) for y,v in enumerate(table) if y&((1 << length)-1)==prefix)
                    assert norm['value']==expected;prefixes+=1
            if width<=3 and mix['mass']:specimens.append(mix)
    bump('independent_prefix_masses',prefixes)
    # Unequal non-dyadic probabilities, absent support and opposite-phase cancellation.
    atoms=[gm.affine_branch(2,y,(),set(),a) for y,a in enumerate((1,2,4))]
    specimens.append(gs.prepare_mixture(atoms,2))
    a=gm.affine_branch(3,0,cc.identity(3),set(),7)
    b=gm.affine_branch(3,0,cc.identity(3),{0},7)
    zero=gs.prepare_mixture([a,b],3)
    assert zero['mass']==0
    try:gs.sample_mixture(zero,3,NoCoins(),gs.sample_stats())
    except ValueError:bump('zero_mass_refusal')
    else:raise AssertionError('zero mass sampled')
    records=[]
    for mix in specimens:
        width=mix['width'];table=values(mix);L=2 if width<3 else 3
        expected,tv=direct_distribution(table,L);frequencies=[0]*len(table)
        for word in range(1 << (width*L)):
            tape=Tape(word,width*L);stats=gs.sample_stats()
            y,sign=gs.sample_mixture(mix,L,tape,stats)
            assert sign==(1 if table[y]>0 else -1)
            assert tape.used==stats['random_bits']<=width*L
            frequencies[y]+=1;bump('exhaustive_sampler_tapes')
        actual=[Fraction(n,1 << (width*L)) for n in frequencies]
        assert actual==expected
        records.append(dict(width=width,branches=len(mix['branches']),mass=mix['mass'],L=L,tv=str(tv)))
        bump('exact_quantized_distributions')
    # A 40-bit hidden mixture sampled with polynomial prefix work and no table.
    width=40;P=hidden_basis(width,rng);offset=rng.getrandbits(width);branches=[]
    for i,a in enumerate((1,3,7,15)):
        phase=pd.substitute_boolean({3 << (2*i)},qr.affine_forms(offset,P,width))
        branches.append(gm.affine_branch(width,0,cc.identity(width),phase,a))
    mix=gs.prepare_mixture(branches,width);stats=gs.sample_stats()
    y,sign=gs.sample_mixture(mix,12,rng,stats)
    assert sign==(1 if sum(branch_value(b,y) for b in branches)>0 else -1)
    assert stats['prefix_norm_calls']==width and stats['prefix_gaussian_sums']<=81*width
    assert stats['random_bits']<=12*width
    bump('rank40_table_free_sample')
    return records,dict(width=width,mass=mix['mass'],stats=stats)


def terminal_law(node,L=None):
    groups=node['groups'];tables=[values(g) for g in groups];laws=[]
    for group,table in zip(groups,tables):
        laws.append(direct_distribution(table,L)[0] if L is not None
                    else [Fraction(abs(v),group['mass']) for v in table])
    answer={-1:Fraction(0),1:Fraction(0)}
    for ys in product(*(range(len(t)) for t in tables)):
        probability=Fraction(1);sign=node['sign'];xs=[]
        for group,table,law,y in zip(groups,tables,laws,ys):
            probability*=law[y]
            if not probability:break
            sign*=1 if table[y]>0 else -1;xs.append(cc.action(group['lifts'],y))
        if not probability:continue
        for (a,b),matrix in node['edges'].items():
            sign*=(-1)**((xs[a]&cc.action(matrix,xs[b])).bit_count()%2)
        answer[sign]+=probability
    assert sum(answer.values())==1
    return answer


def tree_law(root,L=None):
    kind=root['kind']
    if root['mass']==0:return {0:Fraction(1)}
    if kind=='constant':return {root['sign']:Fraction(1)}
    if kind=='push':return tree_law(root['child'],L)
    if kind=='terminal':
        ones=sum(cc.anf_evaluate(root['phase'],x) for x in range(1 << root['n']))
        return {-1:Fraction(ones,1 << root['n']),1:1-Fraction(ones,1 << root['n'])}
    if kind=='controls':return terminal_law(root,L)
    distribution={root['sign']:Fraction(1)}
    for child in root['children']:
        following={}
        for a,p in distribution.items():
            for b,q in tree_law(child,L).items():following[a*b]=following.get(a*b,0)+p*q
        distribution=following
    return distribution


def direct_sample(root,L,coins):
    """Literal-prefix reference independent of Gaussian norm/intersection sampling."""
    kind=root['kind']
    if kind=='constant':return root['sign']
    if kind=='push':return direct_sample(root['child'],L,coins)
    if kind=='product':
        sign=root['sign']
        for child in reversed(root['children']):sign*=direct_sample(child,L,coins)
        return sign
    if kind=='terminal':return (-1)**cc.anf_evaluate(root['phase'],coins.getrandbits(root['n']))
    sign=root['sign'];xs=[]
    for group in root['groups']:
        table=values(group);prefix=0
        for j in range(group['width']):
            allowed=[x for x in range(len(table)) if x&((1 << j)-1)==prefix]
            mass=sum(abs(table[x]) for x in allowed)
            zero=sum(abs(table[x]) for x in allowed if not x >> j&1)
            if zero==mass:bit=0
            elif zero==0:bit=1
            else:bit=int(coins.getrandbits(L)>=(zero << L)//mass)
            prefix|=bit << j
        sign*=1 if table[prefix]>0 else -1;xs.append(cc.action(group['lifts'],prefix))
    for (a,b),matrix in root['edges'].items():
        sign*=(-1)**((xs[a]&cc.action(matrix,xs[b])).bit_count()%2)
    return sign


def recursive_checks(rng):
    fixtures=[(0,set()),(0,{0}),(2,{3}),(2,{1,3,0}),(10,{7,56,1 << 9,0}),
              (12,{7,56,448,3584,1|(1 << 3),0}),
              (11,field_phase(3,11)^{(1 << 9)|(1 << 10),0})]
    for n in (6,9,12):
        for _ in range(3):
            phase={7 << (3*j) for j in range(n//3)}^{m for m in cc.anf_masks(n,2) if rng.randrange(4)==0}
            fixtures.append((n,pd.substitute_boolean(phase,qr.affine_forms(rng.getrandbits(n),hidden_basis(n,rng),n))))
    kinds=set()
    for n,phase in fixtures:
        tree,prepared=gs.compile_sum(phase,n);root=prepared['root'];Z=root['mass']
        expected=brute(phase,n);law=tree_law(root)
        assert Z*sum(sign*p for sign,p in law.items())==expected
        L=5
        if Z:
            approximate=tree_law(root,L)
            drift=abs(sum(sign*p for sign,p in approximate.items())-Fraction(expected,Z))
            assert drift<=Fraction(2*root['boundary_bits'],1 << L)
            length=root['boundary_bits']*L+root['uniform_bits']
            for _ in range(12):
                word=rng.getrandbits(length);a=Tape(word,length);b=Tape(word,length);stats=gs.sample_stats()
                assert gs.sample_sign(root,L,a,stats)==direct_sample(root,L,b)
                assert a.used==b.used==stats['random_bits']
                bump('independent_recursive_sample_signs')
        pending=[root]
        while pending:
            v=pending.pop();kinds.add(v['kind'])
            assert v['mass']<=1 << v['n'] and v['boundary_bits']+v['uniform_bits']<=v['n']
            if v['kind']=='push':pending.append(v['child'])
            elif v['kind']=='product':pending.extend(v['children'])
        bump('independent_recursive_signed_expectations')
    # A valid tighter pair envelope is not the uniform proposal's normalizer.
    tree,_=pe.compile_sum(field_phase(3,11),9,max_kernel_dimension=9)
    prepared=gs.prepare_tree(tree);root=prepared['root']
    assert root['kind']=='terminal' and root['mass']==512 and tree['bound']<512
    assert root['mass']*sum(s*p for s,p in tree_law(root).items())==120
    bump('uncapped_normalizer_trap')
    assert kinds=={'zero','constant','push','product','terminal','controls'},kinds
    return dict(kinds=sorted(kinds),normalizer_trap=dict(envelope=tree['bound'],proposal=root['mass'],signed=120))


def confidence_checks():
    records=[]
    for K,b,h,pplus in [(Fraction(3,4),2,2,Fraction(1,3)),
                        (Fraction(1),1,3,Fraction(2,5)),
                        (Fraction(3,2),2,1,Fraction(1,2))]:
        eps=Fraction(1,1 << b);target=2*K*K*(1 << (2*b))*(h+1)
        N=(target.numerator+target.denominator-1)//target.denominator
        mean=K*(2*pplus-1);tail=Fraction(0)
        for j in range(N+1):
            estimate=K*Fraction(2*j-N,N)
            if abs(estimate-mean)>=eps:
                tail+=comb(N,j)*pplus**j*(1-pplus)**(N-j)
        assert tail<=Fraction(1,1 << h)
        records.append(dict(K=str(K),bits=b,h=h,samples=N,exact_tail=str(tail)))
        bump('exact_binomial_confidence_tails')
    return records


def native_checks(rng):
    records=[];cases=[(1,4,None,False,False,6),(2,3,None,True,True,5),
        (3,8,BOUNDARY_EDGES,False,False,7),(4,8,BOUNDARY_EDGES,True,False,6),
        (8,3,[(0,1),(1,2),(2,0)],False,False,2)]
    for k,g,edges,flip,hidden,bits in cases:
        if edges is None:edges=list(combinations(range(g),2))
        desc=dense_source(k,g,flip,edges);p=graph_probability(k,g,edges)
        if flip:p=1-p
        if hidden:desc=transform_physical(desc,rng)
        native=cc.compile_native(desc);result=gs.reduce_native(desc[1],native['gates'],desc[4],desc[5])
        root=result['proposal']['root'];D=1 << (2*desc[1]);K=Fraction(root['mass'],D)
        assert K<=(1-Fraction(1,1 << (k+1)))**g<=1
        plan=gs.evaluation_plan(result,bits,5)
        assert plan['mode']=='sampling' and plan['samples']<=2*(6)*(1 << (2*bits))+1
        with patch.object(pe,'exact_tree',side_effect=AssertionError('forbidden exact readout')),\
             patch.object(cb,'evaluate_controls',side_effect=AssertionError('forbidden joint enumeration')):
            answer=gs.evaluate_source(result,bits,5,rng,max_samples=1000)
        assert answer['mode']=='sampling' and answer['probability'] is None
        assert answer['stats']['samples']==plan['samples']
        assert answer['stats']['random_bits']<=plan['random_bit_bound']
        assert answer['error_bound']<Fraction(1,1 << bits)
        if desc[1]<=15:
            assert p==fast_independent_probability(desc);bump('independent_native_state_references')
            if desc[1]<=12:check_native(native,p);bump('literal_native_reference')
        for _ in range(6):
            xs=[rng.getrandbits(desc[1]) for _ in range(3)]
            assert cc.anf_evaluate(result['phase'],sum(x << (j*desc[1]) for j,x in enumerate(xs)))==boolean_output_phase(desc,xs)
            bump('original_phase_identities')
        for b,h in [(1,1),(bits,5),(180,7),(4096,65)]:
            schedule=gs.evaluation_plan(result,b,h,allow_envelope=False)
            N=schedule['samples'];L=schedule['random_precision'];eps=Fraction(1,1 << b)
            if N:
                threshold=2*(h+1)*K*K*(1 << (2*b))
                assert N-1<threshold<=N
                assert K*Fraction(root['boundary_bits'],1 << L)<=eps/32
                assert schedule['bias_bound']+eps*Fraction(3,4)<eps
            bump('integer_precision_schedules')
        refused=gs.evaluate_source(result,180,7,NoCoins(),allow_envelope=False,max_samples=0)
        assert refused['mode']=='budget_refused' and refused['stats']['random_bits']==0
        bump('high_precision_budget_refusals')
        record=dict(k=k,g=g,n=desc[1],hidden=hidden,flip=flip,source_bits=native['source_bits'],
                    native_records=len(native['gates']),probability=str(p),K=str(K),bits=bits,
                    samples=plan['samples'],random_precision=plan['random_precision'],
                    estimate=str(answer['estimate']),certified_error=str(answer['error_bound']),
                    realized_error=str(abs(answer['estimate']-p)),
                    realized_covered=abs(answer['estimate']-p)<=answer['error_bound'],
                    failure_probability=str(answer['failure_probability']),stats=answer['stats'],
                    previous_joint_budget=result['cost']['gaussian_sums'])
        records.append(record);bump('complete_native_sampling_outputs')
        print('Native finite-bit sampling:',record,flush=True)
    # Paid general normalized-mass boundary; no unbounded sampling is attempted.
    boundaries=[]
    for k in (2,3):
        desc=all_aux_cycle(k,3);native=cc.compile_native(desc)
        result=gs.reduce_native(desc[1],native['gates'],desc[4],desc[5]);plan=gs.evaluation_plan(result,2,2)
        ratio=Fraction((1 << (4*k))-(1 << (2*k)),1 << (3*k+1))
        assert plan['mode']=='sampling' and plan['K']==ratio**3>1
        refused=gs.evaluate_source(result,2,2,NoCoins(),max_samples=0)
        assert refused['mode']=='budget_refused'
        boundaries.append(dict(k=k,g=3,K=str(plan['K']),samples=plan['samples'],random_bit_bound=plan['random_bit_bound']))
        bump('exponential_mass_boundary')
    # Exact and coarse branches consume no coins; source gates still replayed.
    desc=dense_source(1,1,edges=[]);native=cc.compile_native(desc)
    result=gs.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    answer=gs.evaluate_source(result,180,7,NoCoins())
    assert answer['mode']=='deterministic' and answer['probability']==graph_probability(1,1,[])
    bump('deterministic_no_coin_output')
    desc=dense_source(2,3,edges=[(0,1),(1,2),(2,0)])
    result=gs.reduce_source(desc);answer=gs.evaluate_source(result,1,7,NoCoins())
    assert answer['mode']=='envelope' and answer['stats']['random_bits']==0
    bump('midpoint_no_coin_output')
    # One linear output character has exactly zero expectation.
    desc=['cubic-field-v1',2,[1,2],[[3]],0,0];native=cc.compile_native(desc)
    result=gs.reduce_native(desc[1],native['gates'],desc[4],desc[5])
    answer=gs.evaluate_source(result,180,7,NoCoins())
    assert answer['mode']=='zero' and answer['probability']==Fraction(1,2)
    check_native(native,Fraction(1,2))
    bump('zero_no_coin_output')
    return records,boundaries


def main():
    rng=random.Random(1730526)
    mixtures,large=mixture_checks(rng);recursive=recursive_checks(rng);tails=confidence_checks()
    print('Exact conditional laws, recursive normalization and finite confidence checks pass',flush=True)
    native,boundary=native_checks(rng)
    prior=ROOT/'artifacts/s173-gaussian-message-norm-checks.json';old=json.loads(prior.read_text());hashes={}
    for path in ['src/gaussian_mass_sampling.py','src/check_gaussian_mass_sampling.py']+list(old['hashes']):
        raw=(ROOT/path).read_bytes();ast.parse(raw.decode())
        hashes[path]=dict(raw_sha256=hashlib.sha256(raw).hexdigest(),
                         canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest())
        if path in old['hashes']:assert hashes[path]==old['hashes'][path],path
    receipt=dict(status='pass',seed=1730526,counts=COUNTS,conditional_distributions=mixtures,
                 large_boundary_sample=large,recursive=recursive,exact_confidence_tails=tails,
                 native_sources=native,normalized_mass_boundaries=boundary,hashes=hashes,
                 prior_receipt_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
                 scope='Complete finite-bit normalized sampler with actual recursive mass and explicit K^2 sample cost. First-auxiliary graph family has K<=1 uniformly in width. Seeded finite outputs do not prove confidence; the concentration proof is separate. General mass can remain exponential; no universal or hard-language claim.')
    target=ROOT/'artifacts/s173-gaussian-mass-sampling-checks.json'
    target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(status='pass',counts=COUNTS,receipt=str(target)),indent=2))


if __name__=='__main__':main()
