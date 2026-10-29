"""S173/R05-15: source-derived pair envelopes before exact readout."""
from fractions import Fraction
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import gaussian_boundary_factorization as gb
import gaussian_interface_transfer as it
import gaussian_block_cuts as bc
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd


def pair_mass(phase,width,direction):
    """Sum the absolute weight of all translation pairs by one Gaussian sum."""
    if type(width) is not int or width<1 or not 0<direction<(1 << width):
        raise ValueError('nonzero direction in a positive-width block required')
    pivot=(direction&-direction).bit_length()-1
    columns=tuple(1 << j for j in range(width) if j!=pivot)
    first=pd.substitute_boolean(phase,qr.affine_forms(0,columns,width))
    second=pd.substitute_boolean(phase,qr.affine_forms(direction,columns,width))
    derivative=first^second
    if any(term.bit_count()>2 for term in derivative):
        raise ValueError('pair derivative must be quadratic')
    mass=(1 << (width-1))+lf.quadratic_value(derivative,width-1)
    assert 0<=mass<=1 << width and mass%2==0
    return mass


def block_envelope(phase,width,rows,max_kernel_dimension=5):
    if type(max_kernel_dimension) is not int or max_kernel_dimension<0:
        raise ValueError('nonnegative kernel-dimension cap required')
    kernel=tuple(cc.nullspace(rows,width));dimension=len(kernel)
    best=(1 << width,0);trials=0
    if dimension<=max_kernel_dimension:
        for word in range(1,1 << dimension):
            direction=cc.action(kernel,word)
            best=min(best,(pair_mass(phase,width,direction),direction));trials+=1
    assert not best[1] or all((r&best[1]).bit_count()%2==0 for r in rows)
    return dict(width=width,kernel_dimension=dimension,bound=best[0],direction=best[1],
                trials=trials,capped=dimension>max_kernel_dimension)


def terminal_envelope(decomposition,max_kernel_dimension=5):
    phases,_,boundaries=gb.split_phase(decomposition)
    blocks=tuple(block_envelope(p,len(block),rows,max_kernel_dimension)
                 for p,block,rows in zip(phases,decomposition['blocks'],boundaries))
    bound=1
    for block in blocks:bound*=block['bound']
    return dict(bound=bound,blocks=blocks,trials=sum(b['trials'] for b in blocks),
                capped_blocks=sum(b['capped'] for b in blocks))


def propagate(tree):
    """Exact integer upper bounds, including every recursive scale and product."""
    pending=[(tree,False)]
    while pending:
        node,visited=pending.pop();kind=node['kind']
        if kind=='zero':bound=0
        elif kind=='constant':bound=abs(node['value'])
        elif kind in ('terminal','controls'):bound=node['pair_envelope']['bound']
        elif not visited:
            pending.append((node,True))
            children=node['children'] if kind=='product' else [node['child']]
            pending.extend((child,False) for child in children);continue
        elif kind=='push':bound=node['child']['bound'] << node['push']['exponent']
        elif kind=='product':
            bound=1
            for child in node['children']:bound*=child['bound']
        else:raise ValueError('unknown tree node')
        # Every node represents a signed sum over exactly its declared n bits.
        node['bound']=min(bound,1 << node['n'])
    return tree['bound']


def prepare_tree(tree,max_kernel_dimension=5):
    if type(max_kernel_dimension) is not int or max_kernel_dimension<0:
        raise ValueError('nonnegative kernel-dimension cap required')
    previous=qr.tree_cost(tree);pending=[tree];certificates=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='terminal':
            width=node['n'];source=gb.discover(node['phase'],width)
            envelope=terminal_envelope(source['decomposition'],max_kernel_dimension)
            certificates.append(envelope)
            node['pair_envelope']=envelope
            if source['accepted']:
                node.update(kind='constant' if source['value'] else 'zero',value=source['value'])
            elif 'joint' in source:
                node.update(kind='controls',certificate=source['joint'],source=source)
            else:
                factor=lf.discover_factor(node['phase'],width)
                if factor is not None:
                    node.update(kind='constant' if factor['value'] else 'zero',value=factor['value'])
    bound=propagate(tree)
    return dict(previous=previous,current=cb.tree_cost(tree),bound=bound,certificates=certificates,
                pair_trials=sum(c['trials'] for c in certificates),
                capped_blocks=sum(c['capped_blocks'] for c in certificates),
                max_kernel_dimension=max_kernel_dimension)


def compile_sum(phase,width,max_kernel_dimension=5):
    tree=qr.compile_sum(phase,width)
    return tree,prepare_tree(tree,max_kernel_dimension)


def reduce_source(desc,max_kernel_dimension=5):
    result=qr.reduce_source(desc)
    result['pair_certification']=prepare_tree(result['tree'],max_kernel_dimension)
    result['cost']=result['pair_certification']['current']
    return result


def reduce_native(n,gates,basis,output,max_kernel_dimension=5):
    return reduce_source(cc.recognize_native(n,gates,basis,output),max_kernel_dimension)


def exact_tree(tree):
    """Retained bounded-table policies, then paid exact Gaussian/point fallback."""
    stats=dict(gaussian_sums=0,point_evaluations=0,scalar_leaves=0,zero_pruned=0,
               interface_attempts=0,interface_accepted=0,cut_attempts=0,cut_accepted=0,
               cut_rank_candidates=0,cut_leaf_entries=0,cut_join_pairs=0)
    # Complete every bounded-table attempt before exponential readout, so a
    # newly discovered zero can prune unsupported siblings regardless of order.
    nodes=[];pending=[tree];known={};bounds={}
    while pending:
        node=pending.pop();nodes.append(node);kind=node['kind'];key=id(node)
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            source=node['source'];stats['interface_attempts']+=1
            transfer=it.transfer(source,max_edge_rank=2)
            if transfer['accepted']:
                known[key]=transfer['value'];stats['interface_accepted']+=1
            else:
                stats['cut_attempts']+=1
                cut=bc.contract(source,max_leaf_rank=4,max_cut_rank=4)
                stats['cut_rank_candidates']+=len(cut.get('plan',{}).get('candidates',()))
                if cut['accepted']:
                    known[key]=cut['value'];stats['cut_accepted']+=1
                    stats['cut_leaf_entries']+=cut['stats']['leaf_entries']
                    stats['cut_join_pairs']+=cut['stats']['join_pairs']
    for node in reversed(nodes):
        key=id(node);kind=node['kind'];bound=node['bound']
        if key in known:bound=abs(known[key])
        elif kind=='push':bound=bounds[id(node['child'])] << node['push']['exponent']
        elif kind=='product':
            bound=1
            for child in node['children']:bound*=bounds[id(child)]
        bounds[key]=min(bound,node['bound'])
    pending=[(tree,False)];values={}
    while pending:
        node,visited=pending.pop();kind=node['kind'];key=id(node)
        if bounds[key]==0:
            values[key]=0;stats['zero_pruned']+=1
        elif key in known:values[key]=known[key]
        elif kind=='constant':
            values[key]=node['value'];stats['scalar_leaves']+=1
        elif kind=='terminal':
            values[key]=sum((-1)**cc.anf_evaluate(node['phase'],x) for x in range(1 << node['n']))
            stats['point_evaluations']+=1 << node['n']
        elif kind=='controls':
            values[key]=cb.evaluate_controls(node['certificate'])
            stats['gaussian_sums']+=1 << node['certificate']['control_rank']
        elif not visited:
            pending.append((node,True))
            children=node['children'] if kind=='product' else [node['child']]
            pending.extend((child,False) for child in children)
        elif kind=='push':
            values[key]=values.pop(id(node['child'])) << node['push']['exponent']
        elif kind=='product':
            value=node['sign']
            for child in node['children']:value*=values.pop(id(child))
            values[key]=value
        else:raise ValueError('unknown tree node')
        if key in values:assert abs(values[key])<=node['bound']
    stats['fallback_work']=stats['gaussian_sums']+stats['point_evaluations']+stats['scalar_leaves']
    return values[id(tree)],stats


def evaluate_source(result,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision required')
    _,n,J,phases,basis,output=result['descriptor']
    den=1 << (n*len(phases));bound=result['tree']['bound'];epsilon=Fraction(1,1 << bits)
    if (bound << bits)<2*den:
        error=Fraction(bound,2*den);midpoint=Fraction(1,2)
        answer=dict(mode='envelope',estimate=midpoint,probability=None,signed=None,
                    interval=(max(Fraction(0),midpoint-error),min(Fraction(1),midpoint+error)),
                    error_bound=error,fallback_work=0,stats={})
    else:
        signed,stats=exact_tree(result['tree']);p=Fraction(den-signed,2*den)
        if not 0<=p<=1:raise AssertionError('invalid original acceptance')
        estimate=Fraction((p.numerator << bits)//p.denominator,1 << bits)
        answer=dict(mode='exact_fallback',estimate=estimate,probability=p,signed=signed,
                    interval=(p,p),error_bound=p-estimate,fallback_work=stats['fallback_work'],stats=stats)
    assert answer['error_bound']<epsilon
    answer.update(bits=bits,root_bound=bound,normalizer=den,
                  pair_trials=result['pair_certification']['pair_trials'])
    return answer
