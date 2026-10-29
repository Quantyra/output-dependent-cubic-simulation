"""S173/R05-17: finite-bit sampling from exact local Gaussian absolute masses."""
from fractions import Fraction
import gaussian_message_norms as gm
import gaussian_interface_transfer as it
import cubic_centroid_descent as cc
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve


def branch_value(branch,y):
    z=solve(branch['span'],y^branch['origin'])
    return 0 if z is None else branch['amplitude']*((-1)**cc.anf_evaluate(branch['phase'],z))


def restrict_bit(branches,position,value):
    """Keep the ambient coordinates; restrict independent support coordinates."""
    answer=[]
    for branch in branches:
        width=branch['width']
        if not 0<=position<width or value not in (0,1):raise ValueError('valid bit constraint required')
        row=sum(((c >> position)&1) << j for j,c in enumerate(branch['columns']))
        rhs=value^((branch['origin'] >> position)&1)
        if not row:
            if not rhs:answer.append(branch)
            continue
        affine=qr.affine_space([(row,rhs)],len(branch['columns']))
        if affine is None:continue
        origin,columns=affine
        phase=pd.substitute_boolean(branch['phase'],qr.affine_forms(origin,columns,len(branch['columns'])))
        answer.append(gm.affine_branch(width,branch['origin']^cc.action(branch['columns'],origin),
                        tuple(cc.action(branch['columns'],v) for v in columns),phase,branch['amplitude']))
    return tuple(answer)


def prepare_mixture(branches,width):
    branches=tuple(branches);norm=gm.absolute_mass(branches,width)
    return dict(branches=branches,width=width,mass=norm['value'],norm=norm)


def draw(coins,bits,stats):
    if bits==0:return 0
    value=coins.getrandbits(bits)
    if type(value) is not int or not 0<=value<(1 << bits):raise ValueError('invalid fair-bit source output')
    stats['random_bits']+=bits;stats['random_calls']+=1
    return value


def sample_mixture(mixture,precision,coins,stats):
    if type(precision) is not int or precision<1:raise ValueError('positive random precision required')
    branches=mixture['branches'];mass=mixture['mass'];width=mixture['width'];y=0
    if mass<=0:raise ValueError('cannot sample a zero-mass mixture')
    for j in range(width):
        zero=restrict_bit(branches,j,0);norm=gm.absolute_mass(zero,width);m0=norm['value']
        stats['prefix_norm_calls']+=1;stats['prefix_gaussian_sums']+=norm['gaussian_sums']
        assert 0<=m0<=mass
        if m0==mass:bit=0
        elif m0==0:bit=1
        else:bit=int(draw(coins,precision,stats)>=(m0 << precision)//mass)
        if bit:
            branches=restrict_bit(branches,j,1);mass-=m0;y|=1 << j
        else:branches=zero;mass=m0
        assert mass>0
    value=sum(branch_value(b,y) for b in mixture['branches'])
    assert value and abs(value)==mass
    stats['signed_boundary_values']+=1
    return y,1 if value>0 else -1


def prepare_terminal(node,stats):
    source=node['source'];groups=[]
    for messages,rows,block in zip(source['messages'],source['boundaries'],source['decomposition']['blocks']):
        branches=tuple(b for message in messages if (b:=gm.source_branch(message,rows)) is not None)
        mixture=prepare_mixture(branches,len(rows))
        stats['mass_norm_calls']+=1
        stats['mass_gaussian_sums']+=mixture['norm']['gaussian_sums']
        columns=ds.transpose_rect(rows,len(block));span=echelon(columns)
        lifts=tuple(solve(span,1 << j) for j in range(len(rows)))
        assert all(v is not None for v in lifts)
        mixture['lifts']=lifts;groups.append(mixture)
    mass=1
    for group in groups:mass*=group['mass']
    return dict(kind='controls',n=node['n'],mass=mass,groups=tuple(groups),
                edges=source['edges'],sign=-1 if 0 in source['decomposition']['phase'] else 1,
                boundary_bits=sum(g['width'] for g in groups),uniform_bits=0)


def prepare_tree(tree):
    """Build the actual proposal, never replacing its mass by an upper envelope."""
    pending=[(tree,False)];prepared={}
    stats=dict(mass_norm_calls=0,mass_gaussian_sums=0)
    while pending:
        node,visited=pending.pop();kind=node['kind'];key=id(node);n=node['n']
        if kind=='zero' or node.get('bound')==0:
            result=dict(kind='zero',n=n,mass=0,boundary_bits=0,uniform_bits=0)
        elif kind=='constant':
            value=node['value']
            result=dict(kind='constant',n=n,mass=abs(value),sign=1 if value>=0 else -1,
                        boundary_bits=0,uniform_bits=0)
        elif kind=='terminal':
            result=dict(kind='terminal',n=n,mass=1 << n,phase=node['phase'],boundary_bits=0,uniform_bits=n)
        elif kind=='controls':result=prepare_terminal(node,stats)
        elif not visited:
            pending.append((node,True))
            children=node['children'] if kind=='product' else [node['child']]
            pending.extend((child,False) for child in children);continue
        elif kind=='push':
            child=prepared[id(node['child'])]
            result=dict(kind=kind,n=n,mass=child['mass'] << node['push']['exponent'],child=child,
                        boundary_bits=child['boundary_bits'],uniform_bits=child['uniform_bits'])
        elif kind=='product':
            children=tuple(prepared[id(child)] for child in node['children']);mass=1
            for child in children:mass*=child['mass']
            result=dict(kind=kind,n=n,mass=mass,children=children,sign=node['sign'],
                        boundary_bits=sum(c['boundary_bits'] for c in children),
                        uniform_bits=sum(c['uniform_bits'] for c in children))
        else:raise ValueError('unknown tree node')
        assert 0<=result['mass']<=1 << n
        assert result['boundary_bits']+result['uniform_bits']<=n
        prepared[key]=result
    return dict(root=prepared[id(tree)],stats=stats)


def sample_sign(root,precision,coins,stats):
    if root['mass']==0:raise ValueError('zero proposal has no sampled sign')
    sign=1;pending=[root]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='constant':sign*=node['sign']
        elif kind=='push':pending.append(node['child'])
        elif kind=='product':
            sign*=node['sign'];pending.extend(node['children'])
        elif kind=='terminal':
            x=draw(coins,node['n'],stats);sign*=(-1)**cc.anf_evaluate(node['phase'],x)
            stats['uniform_points']+=1
        elif kind=='controls':
            sign*=node['sign'];representatives=[]
            for group in node['groups']:
                y,local_sign=sample_mixture(group,precision,coins,stats)
                sign*=local_sign;representatives.append(cc.action(group['lifts'],y))
            for (a,b),matrix in node['edges'].items():
                sign*=(-1)**((representatives[a]&cc.action(matrix,representatives[b])).bit_count()%2)
                stats['terminal_cross_edges']+=1
        else:raise ValueError('invalid nonzero proposal node')
    return sign


def sample_stats():
    return dict(samples=0,random_bits=0,random_calls=0,prefix_norm_calls=0,prefix_gaussian_sums=0,
                signed_boundary_values=0,uniform_points=0,terminal_cross_edges=0)


def compile_sum(phase,width):
    tree,detail=gm.compile_sum(phase,width)
    return tree,prepare_tree(tree)


def reduce_source(desc):
    result=gm.reduce_source(desc);result['proposal']=prepare_tree(result['tree'])
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluation_plan(result,bits,failure_bits,allow_envelope=True):
    if type(bits) is not int or bits<1 or type(failure_bits) is not int or failure_bits<1:
        raise ValueError('positive accuracy and failure exponents required')
    _,n,J,phases,basis,output=result['descriptor'];D=1 << (n*len(phases))
    root=result['proposal']['root'];Z=root['mass'];R=root['boundary_bits'];U=root['uniform_bits']
    epsilon=Fraction(1,1 << bits);K=Fraction(Z,D);bound=result['tree']['bound']
    mode='sampling'
    if Z==0:mode='zero'
    elif R+U==0:mode='deterministic'
    elif allow_envelope and (bound << bits)<2*D:mode='envelope'
    scaled=Z << bits
    N=max(1,(2*(failure_bits+1)*scaled*scaled+D*D-1)//(D*D)) if mode=='sampling' else 0
    # ceil(log2(32 max(1,R) K/epsilon)), computed using integers only.
    ceiling=(32*max(1,R)*scaled+D-1)//D
    precision=max(1,(max(1,ceiling)-1).bit_length())
    bias=K*Fraction(R,1 << precision)
    assert bias<=epsilon/32
    return dict(mode=mode,bits=bits,failure_bits=failure_bits,normalizer=D,proposal_mass=Z,
                K=K,boundary_bits=R,uniform_bits=U,samples=N,random_precision=precision,
                random_bit_bound=N*(R*precision+U),epsilon=epsilon,bias_bound=bias,
                failure_probability=Fraction(1,1 << failure_bits),root_bound=bound)


def evaluate_source(result,bits,failure_bits,coins,allow_envelope=True,max_samples=None):
    plan=evaluation_plan(result,bits,failure_bits,allow_envelope);stats=sample_stats()
    if max_samples is not None:
        if type(max_samples) is not int or max_samples<0:raise ValueError('nonnegative sample cap required')
        if plan['samples']>max_samples:
            return dict(mode='budget_refused',estimate=None,probability=None,plan=plan,stats=stats)
    D=plan['normalizer'];Z=plan['proposal_mass'];root=result['proposal']['root'];mode=plan['mode']
    probability=None
    if mode=='zero':
        estimate=probability=Fraction(1,2);error=Fraction(0);failure=Fraction(0)
    elif mode=='deterministic':
        signed=Z*sample_sign(root,plan['random_precision'],coins,stats)
        probability=Fraction(D-signed,2*D)
        assert 0<=probability<=1
        estimate=Fraction((probability.numerator << bits)//probability.denominator,1 << bits)
        error=probability-estimate;failure=Fraction(0)
    elif mode=='envelope':
        estimate=Fraction(1,2);error=Fraction(plan['root_bound'],2*D);failure=Fraction(0)
    else:
        N=plan['samples'];total=0
        for _ in range(N):
            total+=sample_sign(root,plan['random_precision'],coins,stats);stats['samples']+=1
        raw=Fraction(D*N-Z*total,2*D*N)
        clipped=max(Fraction(0),min(Fraction(1),raw));guard=bits+2
        estimate=Fraction((clipped.numerator << guard)//clipped.denominator,1 << guard)
        error=plan['bias_bound']+plan['epsilon']*Fraction(3,4)
        failure=plan['failure_probability']
    assert 0<=estimate<=1 and error<plan['epsilon']
    assert stats['random_bits']<=plan['random_bit_bound']
    return dict(mode=mode,estimate=estimate,probability=probability,error_bound=error,
                interval=(max(Fraction(0),estimate-error),min(Fraction(1),estimate+error)),
                failure_probability=failure,plan=plan,stats=stats)
