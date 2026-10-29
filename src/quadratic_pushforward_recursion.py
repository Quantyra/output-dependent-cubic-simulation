"""S173/R05-09: recursive quadratic pushforward before cubic enumeration.

Exact binary arithmetic. Gaussian pushforward is established machinery; the
new checked claim is the source-derived recursive terminal cost.
"""
from fractions import Fraction
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve,xor_sum


def affine_space(equations,width):
    pivots={}
    for row,value in equations:
        while row:
            j=row.bit_length()-1
            if j not in pivots:
                pivots[j]=(row,value);break
            other,c=pivots[j];row ^= other;value ^= c
        else:
            if value:return None
    origin=0
    for j in sorted(pivots):
        row,value=pivots[j]
        if ((row&origin).bit_count()&1)^value:origin ^= 1 << j
    kernel=cc.nullspace((row for row,c in pivots.values()),width)
    return origin,tuple(kernel)


def affine_forms(origin,columns,rows):
    return [(sum(((column >> i)&1) << j for j,column in enumerate(columns)),
             (origin >> i)&1) for i in range(rows)]


def quadratic_pushforward(Q,rows,m):
    """Return sum_{Mx=b} (-1)^Q(x) as exact affine-supported quadratic."""
    t=len(rows)
    if any(mask.bit_count()>2 for mask in Q):raise ValueError('quadratic required')
    columns=tuple(sum(((row >> i)&1) << j for j,row in enumerate(rows)) for i in range(m))
    span=echelon(columns)
    if len(span)!=t:raise ValueError('independent output covectors required')
    right=tuple(solve(span,1 << j) for j in range(t))
    kernel=tuple(cc.nullspace(rows,m));change=right+kernel
    assert len(change)==m and len(echelon(change))==m
    phase=pd.substitute_boolean(Q,affine_forms(0,change,m))
    active=set(range(t,m));exponent=0
    while True:
        pair=next((mask for mask in sorted(phase) if mask.bit_count()==2
                   and all(j in active for j in pd.bits(mask))),None)
        if pair is None:break
        i,j=tuple(pd.bits(pair));bi=1 << i;bj=1 << j
        A={mask^bi for mask in phase if mask&bi and not mask&bj}
        B={mask^bj for mask in phase if mask&bj and not mask&bi}
        following={mask for mask in phase if not mask&(bi|bj)}
        for a in A:
            for b in B:
                term=a|b
                if term in following:following.remove(term)
                else:following.add(term)
        phase=following;active -= {i,j};exponent+=1
    equations=[]
    for i in sorted(active):
        coeff={mask^(1 << i) for mask in phase if mask >> i & 1}
        assert all(mask==0 or (mask.bit_count()==1 and mask.bit_length()<=t) for mask in coeff)
        equations.append((xor_sum(mask for mask in coeff if mask),int(0 in coeff)))
    exponent+=len(active)
    free_mask=sum(1 << i for i in active)
    phase={mask for mask in phase if not mask&free_mask}
    assert all(mask.bit_length()<=t for mask in phase)
    support=affine_space(equations,t)
    if support is None:
        return dict(zero=True,output_bits=t,exponent=exponent,equations=equations,
                    origin=0,columns=(),phase=set())
    origin,basis=support
    restricted=pd.substitute_boolean(phase,affine_forms(origin,basis,t))
    return dict(zero=False,output_bits=t,exponent=exponent,equations=equations,
                origin=origin,columns=basis,phase=restricted)


def factor_cubic(poly,n):
    U=ds.image_basis(row for rows in pd.cubic_tensor(poly,n) for row in rows)
    columns=tuple(sum(((u >> i)&1) << j for j,u in enumerate(U)) for i in range(n))
    span=echelon(columns)
    right=tuple(solve(span,1 << j) for j in range(len(U)))
    restricted=pd.substitute_boolean(poly,affine_forms(0,right,n))
    G={mask for mask in restricted if mask.bit_count()==3}
    Q=set(poly)^pd.substitute_boolean(G,[(u,0) for u in U])
    assert max((mask.bit_count() for mask in Q),default=0)<=2
    assert set(poly)==Q^pd.substitute_boolean(G,[(u,0) for u in U])
    return tuple(U),G,Q


def components(poly,n):
    parents=list(range(n))
    def root(a):
        while a!=parents[a]:
            parents[a]=parents[parents[a]];a=parents[a]
        return a
    for mask in poly:
        bits=tuple(pd.bits(mask))
        for i in bits[1:]:parents[root(i)]=root(bits[0])
    groups={}
    for i in range(n):groups.setdefault(root(i),[]).append(i)
    return list(groups.values())


def compile_sum(poly,n):
    """Polynomial preprocessing; explicit stack, no enumeration or Walsh table."""
    root={};pending=[(set(poly),n,root)]
    while pending:
        poly,n,node=pending.pop()
        if any(mask<0 or mask.bit_length()>n or mask.bit_count()>3 for mask in poly):
            raise ValueError('degree-three ANF over declared variables required')
        if n==0:
            node.update(kind='constant',n=0,value=-1 if 0 in poly else 1);continue
        groups=components(poly,n)
        if len(groups)>1:
            children=[]
            for group in groups:
                keep=sum(1 << i for i in group);positions={j:i for i,j in enumerate(group)}
                terms={sum(1 << positions[j] for j in pd.bits(mask))
                       for mask in poly if mask and mask&keep}
                child={};children.append(child);pending.append((terms,len(group),child))
            node.update(kind='product',n=n,sign=-1 if 0 in poly else 1,children=children)
            continue
        U,G,Q=factor_cubic(poly,n);r=len(U)
        if r==n:
            node.update(kind='terminal',n=n,phase=poly,rank=r);continue
        pushed=quadratic_pushforward(Q,U,n)
        if pushed['zero']:
            node.update(kind='zero',n=n,rank=r,push=pushed);continue
        d=len(pushed['columns'])
        terms=pd.substitute_boolean(G,affine_forms(pushed['origin'],pushed['columns'],r))
        terms ^= pushed['phase']
        assert d<=r<n
        child={};node.update(kind='push',n=n,rank=r,push=pushed,child=child)
        pending.append((terms,d,child))
    # A known zero factor annihilates the whole product before any leaf is
    # enumerated. Discovery above was polynomial even in discarded children.
    pending=[(root,False)]
    while pending:
        node,visited=pending.pop();kind=node['kind']
        if kind not in ('product','push'):continue
        children=node['children'] if kind=='product' else [node['child']]
        if not visited:
            pending.append((node,True));pending.extend((child,False) for child in children)
        elif any(child['kind']=='zero' for child in children):
            width=node['n'];node.clear();node.update(kind='zero',n=width,reason='zero_factor')
    return root


def tree_cost(tree):
    cost=dict(nodes=0,terminals=0,work=0,max_width=0,pushes=0);pending=[tree]
    while pending:
        node=pending.pop();kind=node['kind'];cost['nodes']+=1
        if kind=='terminal':
            cost['terminals']+=1;cost['work']+=1 << node['n']
            cost['max_width']=max(cost['max_width'],node['n'])
        elif kind in ('zero','constant'):cost['terminals']+=1;cost['work']+=1
        elif kind=='push':cost['pushes']+=1;pending.append(node['child'])
        else:pending.extend(node['children'])
    return cost


def evaluate_tree(tree):
    pending=[(tree,False)];values={}
    while pending:
        node,visited=pending.pop();kind=node['kind'];key=id(node)
        if kind=='constant':values[key]=node['value']
        elif kind=='zero':values[key]=0
        elif kind=='terminal':
            values[key]=sum(-1 if cc.anf_evaluate(node['phase'],x) else 1
                            for x in range(1 << node['n']))
        elif not visited:
            pending.append((node,True))
            children=node['children'] if kind=='product' else [node['child']]
            pending.extend((child,False) for child in children)
        elif kind=='push':
            values[key]=(1 << node['push']['exponent'])*values.pop(id(node['child']))
        else:
            value=node['sign']
            for child in node['children']:value*=values.pop(id(child))
            values[key]=value
    return values[id(tree)]


def original_output_phase(desc):
    """Literal Boolean doubled-output ANF, before any Gaussian compression."""
    _,n,J,phases,basis,output=desc;L=len(phases);k=2*L-1
    shift=cc.action(cc.inverse(J),1 << output)
    ket=[[(1 << (v*n+j),0) for j in range(n)] for v in range(L)]
    bra=[[(1 << ((L+v)*n+j),0) for j in range(n)] for v in range(L-1)]
    bra.append([(mask,(shift >> j)&1) for j,(mask,c) in enumerate(ket[-1])])
    P=set()
    for phase,x,y in zip(phases,ket,bra):
        P ^= pd.substitute_boolean(phase,x)^pd.substitute_boolean(phase,y)
    boundary={1 << j for j in pd.bits(cc.action(J,basis))}
    P ^= pd.substitute_boolean(boundary,ket[0])^pd.substitute_boolean(boundary,bra[0])
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            for j,col in enumerate(J):
                for i in pd.bits(col):P ^= pd.affine_product((x[i],y[j]))
    return P,k*n


def reduce_source(desc):
    desc=cc.normalize_descriptor(desc)
    phase,m=original_output_phase(desc)
    tree=compile_sum(phase,m)
    return dict(descriptor=desc,phase=phase,physical_bits=m,tree=tree,cost=tree_cost(tree))


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluate_source(result,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision required')
    signed=evaluate_tree(result['tree'])
    _,n,J,phases,basis,output=result['descriptor'];den=1 << (n*len(phases))
    p=Fraction(den-signed,2*den)
    if not 0<=p<=1:raise AssertionError('invalid original acceptance')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(probability=p,rounded=rounded,signed=signed)
