"""S173/R05-20: exact transfer by merging signed affine quadratic maps."""
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import gaussian_boundary_factorization as gb
import gaussian_interface_transfer as it
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve


def operator_key(in_width,out_width,columns,origin,phase):
    """Canonical graph kernel, with its constant phase moved to the coefficient."""
    phase=set(phase);sign=-1 if 0 in phase else 1
    phase.discard(0)
    return (in_width,out_width,tuple(columns),origin,tuple(sorted(phase))),sign


def identity(width):
    return operator_key(width,width,cc.identity(width),0,())[0]


def compose(first,second):
    """Kernel product: first sends u to v, second sends v to w."""
    ni,nm,A,a,Q=first;mi,no,B,b,R=second
    assert nm==mi
    columns=tuple(cc.action(B,v) for v in A);origin=cc.action(B,a)^b
    phase=set(Q)^pd.substitute_boolean(R,qr.affine_forms(a,A,nm))
    return operator_key(ni,no,columns,origin,phase)


def trace(key):
    ni,no,A,a,Q=key
    if ni!=no:raise ValueError('square kernel required')
    equations=[(sum(((col >> i)&1) << j for j,col in enumerate(A))^(1 << i),(a >> i)&1)
               for i in range(ni)]
    fixed=qr.affine_space(equations,ni)
    if fixed is None:return 0,False
    origin,columns=fixed
    phase=pd.substitute_boolean(Q,qr.affine_forms(origin,columns,ni))
    return lf.quadratic_value(phase,len(columns)),True


def kernel_value(key,u,v):
    ni,no,A,a,Q=key
    if cc.action(A,u)^a!=v:return 0
    return (-1)**cc.anf_evaluate(Q,u)


def local_operator(message,incoming,outgoing,pairing):
    """Sum a Gaussian local branch and its outgoing edge, with no boundary table."""
    free=len(message['kernel']);ni=len(incoming);no=len(outgoing)
    assert len(pairing)==no
    rows=tuple(it.signature(message['kernel'],r) for r in incoming)
    if len(echelon(rows))!=ni:
        return dict(accepted=False,reason='incoming_projection_not_full')
    phase=set(message['quadratic'])
    for j,column in enumerate(pairing):
        covector=cc.action(outgoing,column)
        row=it.signature(message['kernel'],covector)
        terms={(1 << (free+j))|(1 << i) for i in pd.bits(row)}
        if (covector&message['origin']).bit_count()%2:terms.add(1 << (free+j))
        phase ^= terms
    pushed=qr.quadratic_pushforward(phase,rows+tuple(1 << (free+j) for j in range(no)),free+no)
    if pushed['zero']:return dict(accepted=True,key=None,coefficient=0)
    origin=pushed['origin']^it.signature(incoming,message['origin'])
    support=pushed['columns'];low=(1 << ni)-1
    projected=tuple(v&low for v in support);span=echelon(projected)
    if len(support)!=ni or len(span)!=ni:
        return dict(accepted=False,reason='kernel_not_total_affine_graph',
                    input_width=ni,support_dimension=len(support),projection_rank=len(span))
    input_origin=origin&low;offset=solve(span,input_origin)
    right=tuple(solve(span,1 << i) for i in range(ni))
    high=tuple(v >> ni for v in support)
    columns=tuple(cc.action(high,v) for v in right)
    affine_origin=(origin >> ni)^cc.action(high,offset)
    quadratic=pd.substitute_boolean(pushed['phase'],qr.affine_forms(offset,right,len(support)))
    key,sign=operator_key(ni,no,columns,affine_origin,quadratic)
    return dict(accepted=True,key=key,coefficient=sign*(1 << pushed['exponent']))


def transfer(source,state_cap=64):
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive map-state cap required')
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
    stats=dict(local_gaussian_kernels=0,map_products=0,peak_states=1,
               trace_gaussian_sums=0,peak_coefficient_bits=1,boundary_table_entries=0)
    total=-1 if 0 in source['decomposition']['phase'] else 1
    components=[]
    for component in orders:
        order=component['vertices'];cycle=component['cycle'];g=len(order)
        width=len(endpoint(order[0],order[-1] if cycle else None))
        states={identity(width):1};history=[];local_records=[]
        for j,u in enumerate(order):
            previous=order[j-1] if j else (order[-1] if cycle else None)
            following=order[j+1] if j+1<g else (order[0] if cycle else None)
            incoming=endpoint(u,previous);outgoing=endpoint(u,following)
            operators={}
            for message in source['messages'][u]:
                op=local_operator(message,incoming,outgoing,pairing(u,following))
                stats['local_gaussian_kernels']+=1
                if not op['accepted']:
                    return dict(accepted=False,reason=op['reason'],stats=stats,block=u)
                if op['coefficient']:
                    operators[op['key']]=operators.get(op['key'],0)+op['coefficient']
            operators={key:c for key,c in operators.items() if c}
            local_records.append(dict(block=u,incoming=incoming,outgoing=outgoing,
                                      pairing=pairing(u,following),operators=operators))
            following_states={}
            for a,ca in states.items():
                for b,cb0 in operators.items():
                    key,sign=compose(a,b);stats['map_products']+=1
                    value=following_states.get(key,0)+sign*ca*cb0
                    if value:following_states[key]=value
                    else:following_states.pop(key,None)
                    if len(following_states)>state_cap:
                        return dict(accepted=False,reason='map_state_cap',stats=stats,
                                    required_states=len(following_states),state_cap=state_cap)
            states=following_states
            stats['peak_states']=max(stats['peak_states'],len(states))
            stats['peak_coefficient_bits']=max(stats['peak_coefficient_bits'],
                                               max((abs(c).bit_length() for c in states.values()),default=0))
            history.append(len(states))
        value=0
        for key,c in states.items():
            traced,used=trace(key);value+=c*traced;stats['trace_gaussian_sums']+=used
        total*=value
        components.append(dict(**component,value=value,history=tuple(history),states=states,locals=local_records))
    assert abs(total)<=1 << sum(len(b) for b in blocks)
    return dict(accepted=True,reason='finite_affine_map_transfer',value=total,
                stats=stats,components=components,interfaces=interfaces,state_cap=state_cap)


def enhance_tree(tree,state_cap=64):
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
                map_products=sum(c['stats']['map_products'] for c in certificates),
                local_gaussian_kernels=sum(c['stats']['local_gaussian_kernels'] for c in certificates),
                trace_gaussian_sums=sum(c['stats']['trace_gaussian_sums'] for c in certificates))


def reduce_source(desc,state_cap=64):
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive map-state cap required')
    result=qr.reduce_source(desc)
    result['map_transfer']=enhance_tree(result['tree'],state_cap)
    result['cost']=result['map_transfer']['current']
    return result


def reduce_native(n,gates,basis,output,state_cap=64):
    return reduce_source(cc.recognize_native(n,gates,basis,output),state_cap)


def evaluate_source(result,bits,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision required')
    if max_work is not None:
        if type(max_work) is not int or max_work<0:raise ValueError('nonnegative retained-work cap required')
        if result['cost']['work']>max_work:
            return dict(mode='budget_refused',probability=None,cost=result['cost'])
    answer=cb.evaluate_source(result,bits)
    return dict(answer,mode='exact',error_bound=answer['probability']-answer['rounded'],
                failure_probability=0,random_bits=0,cost=result['cost'])
