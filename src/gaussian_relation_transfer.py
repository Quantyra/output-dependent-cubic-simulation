"""S173/R05-21: source-derived affine Gaussian relations and exact closure."""
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import gaussian_boundary_factorization as gb
import gaussian_interface_transfer as it
import affine_map_transfer as am
import phase_defect_tensors as pd
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve


def reduced_basis(vectors):
    pivots={j:row for j,(row,mask) in echelon(vectors).items()}
    for j in sorted(pivots):
        for k in pivots:
            if k!=j and (pivots[k] >> j)&1:pivots[k]^=pivots[j]
    return tuple(pivots[j] for j in sorted(pivots))


def canonical(ni,no,origin,columns,phase):
    """Unique affine support and quadratic ANF; constant sign is a scalar."""
    columns=tuple(columns);span=echelon(columns);assert len(span)==len(columns)
    basis=reduced_basis(columns);representative=origin
    for v in basis:
        if (representative >> (v.bit_length()-1))&1:representative^=v
    offset=solve(span,origin^representative)
    change=tuple(solve(span,v) for v in basis)
    assert offset is not None and all(v is not None for v in change)
    Q=pd.substitute_boolean(phase,qr.affine_forms(offset,change,len(columns)))
    sign=-1 if 0 in Q else 1;Q.discard(0)
    return (ni,no,representative,basis,tuple(sorted(Q))),sign


def push(ni,no,phase,origin,columns):
    """Arbitrary-rank affine image of a quadratic signed sum."""
    columns=tuple(columns);image=reduced_basis(columns);span=echelon(image)
    coordinates=tuple(solve(span,v) for v in columns)
    rows=ds.transpose_rect(coordinates,len(image))
    gaussian=qr.quadratic_pushforward(set(phase),rows,len(columns))
    if gaussian['zero']:return None,0
    offset=origin^cc.action(image,gaussian['origin'])
    support=tuple(cc.action(image,v) for v in gaussian['columns'])
    key,sign=canonical(ni,no,offset,support,gaussian['phase'])
    return key,sign*(1 << gaussian['exponent'])


def identity(width):
    return canonical(width,width,0,tuple((1 << j)|(1 << (width+j)) for j in range(width)),())[0]


def compose(first,second):
    ni,nm,a,A,Q=first;mi,no,b,B,R=second
    assert nm==mi
    na=len(A);nb=len(B);middle=(1 << nm)-1
    a_mid=a >> ni;b_mid=b&middle
    mid_columns=tuple(v >> ni for v in A)+tuple(v&middle for v in B)
    equations=[(sum(((v >> j)&1) << i for i,v in enumerate(mid_columns)),((a_mid^b_mid) >> j)&1)
               for j in range(nm)]
    matched=qr.affine_space(equations,na+nb)
    if matched is None:return None,0
    origin,columns=matched
    phase=set(Q)^{mask << na for mask in R}
    phase=pd.substitute_boolean(phase,qr.affine_forms(origin,columns,na+nb))
    left=(1 << ni)-1
    out_origin=(a&left)|((b >> nm) << ni)
    out_columns=tuple(v&left for v in A)+tuple((v >> nm) << ni for v in B)
    out_origin^=cc.action(out_columns,origin)
    out_columns=tuple(cc.action(out_columns,v) for v in columns)
    key,scale=push(ni,no,phase,out_origin,out_columns)
    assert abs(scale)<=1 << nm
    return key,scale


def trace(key):
    ni,no,origin,columns,Q=key
    if ni!=no:raise ValueError('square Gaussian relation required')
    equations=[]
    for j in range(ni):
        row=sum((((v >> j)^(v >> (ni+j)))&1) << i for i,v in enumerate(columns))
        rhs=((origin >> j)^(origin >> (ni+j)))&1
        equations.append((row,rhs))
    fixed=qr.affine_space(equations,len(columns))
    if fixed is None:return 0,False
    offset,basis=fixed
    phase=pd.substitute_boolean(Q,qr.affine_forms(offset,basis,len(columns)))
    return lf.quadratic_value(phase,len(basis)),True


def kernel_value(key,u,v):
    ni,no,origin,columns,Q=key
    point=solve(echelon(columns),(u|(v << ni))^origin)
    return 0 if point is None else (-1)**cc.anf_evaluate(Q,point)


def local_relation(message,incoming,outgoing,pairing):
    free=len(message['kernel']);ni=len(incoming);no=len(outgoing)
    assert len(pairing)==no
    rows=tuple(it.signature(message['kernel'],r) for r in incoming)
    phase=set(message['quadratic'])
    for j,column in enumerate(pairing):
        covector=cc.action(outgoing,column);row=it.signature(message['kernel'],covector)
        terms={(1 << (free+j))|(1 << i) for i in pd.bits(row)}
        if (covector&message['origin']).bit_count()%2:terms.add(1 << (free+j))
        phase ^= terms
    columns=tuple(sum(((row >> i)&1) << j for j,row in enumerate(rows)) for i in range(free))
    columns+=tuple(1 << (ni+j) for j in range(no))
    return push(ni,no,phase,it.signature(incoming,message['origin']),columns)


def transfer(source,state_cap=67):
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation-state cap required')
    if 'messages' not in source:return dict(accepted=False,reason='unsupported_local_control')
    blocks=source['decomposition']['blocks'];edges=source['edges']
    orders=it.graph_orders(len(blocks),edges)
    if orders is None:return dict(accepted=False,reason='interaction_degree')
    interfaces={key:it.edge_interface(H,len(blocks[key[0]])) for key,H in edges.items()}
    def endpoint(u,v):
        if v is None:return ()
        e=interfaces[tuple(sorted((u,v)))]
        return e['left'] if u<v else e['right']
    def pairing(u,v):
        if v is None:return ()
        M=interfaces[tuple(sorted((u,v)))]['pairing']
        return M if u<v else cc.transpose(M)
    stats=dict(local_gaussian_kernels=0,relation_products=0,zero_products=0,peak_states=1,
               trace_gaussian_sums=0,peak_coefficient_bits=1,boundary_table_entries=0)
    total=-1 if 0 in source['decomposition']['phase'] else 1;components=[]
    for component in orders:
        order=component['vertices'];cycle=component['cycle'];g=len(order)
        width=len(endpoint(order[0],order[-1] if cycle else None))
        states={identity(width):1};history=[];local_records=[]
        for j,u in enumerate(order):
            previous=order[j-1] if j else (order[-1] if cycle else None)
            following=order[j+1] if j+1<g else (order[0] if cycle else None)
            incoming=endpoint(u,previous);outgoing=endpoint(u,following);operators={}
            for message in source['messages'][u]:
                key,c=local_relation(message,incoming,outgoing,pairing(u,following))
                stats['local_gaussian_kernels']+=1
                if c:operators[key]=operators.get(key,0)+c
            operators={key:c for key,c in operators.items() if c}
            local_records.append(dict(block=u,incoming=incoming,outgoing=outgoing,
                                      pairing=pairing(u,following),operators=operators))
            following_states={}
            for a,ca in states.items():
                for b,cb0 in operators.items():
                    key,scale=compose(a,b);stats['relation_products']+=1
                    if not scale:stats['zero_products']+=1;continue
                    value=following_states.get(key,0)+scale*ca*cb0
                    if value:following_states[key]=value
                    else:following_states.pop(key,None)
                    if len(following_states)>state_cap:
                        return dict(accepted=False,reason='relation_state_cap',stats=stats,
                                    required_states=len(following_states),state_cap=state_cap)
            states=following_states
            stats['peak_states']=max(stats['peak_states'],len(states))
            stats['peak_coefficient_bits']=max(stats['peak_coefficient_bits'],
                                               max((abs(c).bit_length() for c in states.values()),default=0))
            history.append(len(states))
        value=0
        for key,c in states.items():
            scalar,used=trace(key);value+=c*scalar;stats['trace_gaussian_sums']+=used
        total*=value
        components.append(dict(**component,value=value,history=tuple(history),states=states,locals=local_records))
    assert abs(total)<=1 << sum(len(b) for b in blocks)
    return dict(accepted=True,reason='finite_gaussian_relation_transfer',value=total,
                stats=stats,components=components,interfaces=interfaces,state_cap=state_cap)


def enhance_tree(tree,state_cap=67):
    retained=gb.enhance_tree(tree);lookup={id(r['joint']):r for r in retained['refusals'] if 'joint' in r}
    pending=[tree];certificates=[];refusals=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            source=lookup[id(node['certificate'])];answer=transfer(source,state_cap)
            if answer['accepted']:
                answer['previous_joint_branches']=source['joint_branches']
                certificates.append(answer);width=node['n'];value=answer['value'];node.clear()
                node.update(kind='constant' if value else 'zero',n=width,value=value)
            else:refusals.append(answer)
    pending=[(tree,False)]
    while pending:
        node,visited=pending.pop();kind=node['kind']
        if kind not in ('product','push'):continue
        children=node['children'] if kind=='product' else [node['child']]
        if not visited:
            pending.append((node,True));pending.extend((x,False) for x in children)
        elif any(x['kind']=='zero' for x in children):
            width=node['n'];node.clear();node.update(kind='zero',n=width)
    cost=cb.tree_cost(tree);assert cost['work']<=retained['current']['work']
    return dict(previous=retained['current'],current=cost,retained=retained,
                certificates=certificates,refusals=refusals,
                relation_products=sum(c['stats']['relation_products'] for c in certificates),
                local_gaussian_kernels=sum(c['stats']['local_gaussian_kernels'] for c in certificates),
                trace_gaussian_sums=sum(c['stats']['trace_gaussian_sums'] for c in certificates))


def reduce_source(desc,state_cap=67):
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation-state cap required')
    result=qr.reduce_source(desc)
    result['relation_transfer']=enhance_tree(result['tree'],state_cap)
    result['cost']=result['relation_transfer']['current']
    return result


def reduce_native(n,gates,basis,output,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),state_cap)


evaluate_source=am.evaluate_source
