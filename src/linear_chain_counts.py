"""S173/R05-22: graded linear-cycle ranks and bulk cyclic-interval counts."""
from fractions import Fraction
import cubic_centroid_descent as cc
from finite_field_descent import echelon


def cycle_profile(matrices,widths):
    """H[j]: V[j+1] -> V[j], stored by columns; no Jordan basis supplied."""
    widths=tuple(widths);g=len(widths);M=sum(widths)
    if g<1 or any(type(k) is not int or k<1 for k in widths):
        raise ValueError('positive vertex dimensions required')
    matrices=tuple(tuple(H) for H in matrices)
    if len(matrices)!=g or any(len(H)!=widths[(j+1)%g] or
            any(type(v) is not int or v<0 or v.bit_length()>widths[j] for v in H)
            for j,H in enumerate(matrices)):
        raise ValueError('invalid rectangular cycle maps')
    paths=[cc.identity(k) for k in widths];ranks=[list(widths)];monodromy=None
    for ell in range(1,M+2):
        paths=[tuple(cc.action(matrices[(j-ell)%g],v) for v in path)
               for j,path in enumerate(paths)]
        ranks.append([len(echelon(path)) for path in paths])
        if ell==g:monodromy=paths[0]
    strings=[]
    for ell in range(1,M+1):
        for j in range(g):
            q=ranks[ell-1][j]-ranks[ell][j]-ranks[ell][(j+1)%g]+ranks[ell+1][(j+1)%g]
            assert q>=0
            if q:strings.append((ell,j,q))
    nil_dimension=sum(ell*q for ell,j,q in strings)
    assert nil_dimension+sum(ranks[M])==M
    assert len(set(ranks[M]))==1 and ranks[M]==ranks[M+1]
    A=monodromy if g%2==0 else cc.compose(monodromy,monodromy)
    dreg=(2 if g%2==0 else 1)*(widths[0]-len(echelon(v^(1 << i) for i,v in enumerate(A))))
    return dict(widths=widths,total_dimension=M,ranks=ranks,strings=tuple(strings),
                regular_dimension=ranks[M][0],regular_nullity=dreg)


def interval_sum(g,strings):
    """Sum_S (-1)^|S| 2^sum min(2, selected occurrences in a string)."""
    if type(g) is not int or g<1:raise ValueError('positive cycle length required')
    strings=tuple(strings)
    if any(type(ell) is not int or ell<1 or not 0<=j<g or type(q) is not int or q<1
           for ell,j,q in strings):raise ValueError('invalid chain multiplicity')
    M=sum(ell*q for ell,j,q in strings)
    # C[end][t]: nonwrapping intervals ending here with start <= t.
    C=[[0]*g for _ in range(g)]
    # W[t][r]: wrapping intervals with end < t and start <= r.
    W=[[0]*g for _ in range(g+1)]
    singleton=[0]*g;long_count=0;short_count=0
    for ell,j,q in strings:
        turns,rest=divmod(ell,g)
        for vertex in range(g):
            occurrences=turns+int((j-vertex)%g<rest)
            singleton[vertex]+=q*min(2,occurrences)
        if ell>=g:long_count+=q;continue
        short_count+=q
        start=(j-ell+1)%g
        if start<=j:
            for t in range(start,g):C[j][t]+=q
        else:
            for t in range(j+1,g+1):
                for r in range(start,g):W[t][r]+=q
    total=1-sum(1 << w for w in singleton)
    stats=dict(first_pairs=0,transitions=0,peak_states=0,peak_integer_bits=abs(total).bit_length())
    if not short_count:
        total+=(g-1) << (2*long_count)
        stats['peak_integer_bits']=max(stats['peak_integer_bits'],abs(total).bit_length())
        return total,stats
    wrap_total=W[g][-1]
    for a in range(g):
        for b in range(a+1,g):
            exponent=sum(C[e][a]+(C[e][b] if e==b else 0) for e in range(a,b+1))
            states={(a,b):1 << exponent};stats['first_pairs']+=1
            for j in range(b+1,g):
                following={}
                for (p,q),value in states.items():
                    for select in (0,1):
                        r,s=(q,j) if select else (p,q)
                        amount=value*(1 << (C[j][r]+C[j][s]))*(-1 if select else 1)
                        following[r,s]=following.get((r,s),0)+amount
                        stats['transitions']+=1
                states={key:value for key,value in following.items() if value}
                stats['peak_states']=max(stats['peak_states'],len(states))
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                                               max((abs(v).bit_length() for v in states.values()),default=0))
            for (p,q),value in states.items():
                wrap=2*wrap_total-W[b][-1]-W[a][-1]+W[a][p]+W[b][q]
                assert wrap>=0
                total+=value << (2*long_count+wrap)
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],abs(total).bit_length())
    stats['peak_integer_bits']=max(stats['peak_integer_bits'],abs(total).bit_length())
    assert stats['peak_integer_bits']<=2*M+g+3
    return total,stats


def cycle_count(matrices,widths):
    profile=cycle_profile(matrices,widths);g=len(widths);M=profile['total_dimension']
    F,stats=interval_sum(g,profile['strings'])
    scaled=(-1)**g*(F+(1 << profile['regular_nullity'])-1)
    value=scaled << (2*M)
    expectation=Fraction(scaled,1 << (M+g))
    assert -1<=expectation<=1
    return dict(profile=profile,alternating_sum=F,value=value,expectation=expectation,
                probability=(1-expectation)/2,stats=stats)

# Source access: propagate the physical copy actions through the retained reader.
import quadratic_pushforward_recursion as qr
import gaussian_boundary_factorization as gb
import gaussian_relation_transfer as gr
import gaussian_interface_transfer as it
import cubic_centroid_controls as cb
import diagonal_control_sampling as dc
import phase_defect_tensors as pd
import field_defect_subspaces as ds
from finite_field_descent import solve


class Refusal(Exception):
    pass


def require(condition,reason):
    if not condition:raise Refusal(reason)


def restrict_action(A,columns):
    span=echelon(columns);values=tuple(solve(span,cc.action(A,v)) for v in columns)
    require(all(v is not None for v in values),'action_does_not_preserve_subspace')
    return values


def quotient_action(A,rows):
    span=echelon(rows)
    coefficients=tuple(solve(span,it.signature(A,row)) for row in rows)
    require(all(v is not None for v in coefficients),'action_does_not_descend')
    return cc.transpose(coefficients)


def physical_copy_actions(desc):
    require(len(desc[3])==2,'requires_two_phase_layers')
    n=desc[1];C=dc.invariant_controls(desc)['controls'];Jinv=cc.inverse(desc[2])
    V=tuple(cc.action(Jinv,c) for c in C)
    gram=tuple(it.signature(C,v) for v in V)
    require(len(echelon(gram))==len(C),'degenerate_control_pairing')
    inverse=cc.inverse(gram)
    Pc=tuple(cc.action(V,cc.action(inverse,it.signature(C,1 << j))) for j in range(n))
    P=cc.identity(n)+(0,)*n+tuple(v << (2*n) for v in Pc)
    S=tuple(1 << (2*n+j) for j in range(n))+tuple(1 << (n+j) for j in range(n))+cc.identity(n)
    assert cc.compose(P,P)==P and cc.compose(S,S)==cc.identity(3*n)
    return P,S


def terminal_actions(tree,phase,actions):
    """Replay only polynomial coordinate changes; annotate terminals by identity."""
    result={};pending=[(tree,set(phase),actions)]
    while pending:
        node,poly,acts=pending.pop();kind=node['kind'];n=node['n']
        if kind=='terminal':result[id(node)]=acts
        elif kind=='push':
            U,G,Q=qr.factor_cubic(poly,n);pushed=node['push']
            child_acts=[]
            for A in acts:
                induced=quotient_action(A,U)
                require(cc.action(induced,pushed['origin'])==pushed['origin'],'affine_support_action')
                child_acts.append(restrict_action(induced,pushed['columns']))
            child_poly=pd.substitute_boolean(G,qr.affine_forms(pushed['origin'],pushed['columns'],len(U)))^pushed['phase']
            pending.append((node['child'],child_poly,tuple(child_acts)))
        elif kind=='product':
            groups=qr.components(poly,n)
            require(len(groups)==len(node['children']),'product_replay')
            for child,group in zip(node['children'],groups):
                columns=tuple(1 << j for j in group);mask=sum(columns)
                positions={v:j for j,v in enumerate(group)}
                terms={sum(1 << positions[j] for j in pd.bits(t)) for t in poly if t and t&mask}
                pending.append((child,terms,tuple(restrict_action(A,columns) for A in acts)))
    return result


def copy_basis(P,S):
    w=len(P);require(w%2==0,'odd_copy_boundary');r=w//2;I=cc.identity(w)
    require(cc.compose(P,P)==P and cc.compose(S,S)==I,'invalid_copy_actions')
    SPS=cc.compose(S,cc.compose(P,S))
    require(tuple(a^b for a,b in zip(P,SPS))==I,'incomplete_copy_split')
    ket=gr.reduced_basis(P);require(len(ket)==r,'unbalanced_copy_split')
    basis=ket+tuple(cc.action(S,v) for v in ket)
    require(len(echelon(basis))==w,'dependent_copy_frame')
    return basis


def reframe(key,input_basis,output_basis):
    ni,no,origin,columns,Q=key
    change=tuple(input_basis)+tuple(v << ni for v in output_basis)
    inv=cc.inverse(change)
    return gr.canonical(ni,no,cc.action(inv,origin),tuple(cc.action(inv,v) for v in columns),Q)


def pair_model(k,a,b,M):
    # incoming=(x,y), outgoing=(p,q); branch one has x=Mq,y=Mp.
    one_columns=tuple((cc.action(M,1 << j) << a)|(1 << (2*a+j)) for j in range(b))
    one_columns+=tuple(cc.action(M,1 << j)|(1 << (2*a+b+j)) for j in range(b))
    one,s1=gr.canonical(2*a,2*b,0,one_columns,())
    zero_columns=tuple((1 << j)|(1 << (a+j)) for j in range(a))
    zero_columns+=tuple(cc.action(M,1 << j)|(1 << (2*a+j))|(1 << (2*a+b+j)) for j in range(b))
    zero,s0=gr.canonical(2*a,2*b,0,zero_columns,())
    return ((zero,(1 << (3*k-a))*s0),(one,-(1 << (2*k))*s1))


def realize_pair(k,a,b,M):
    """Full-column V,U with V^T U=M; fail before any basis search."""
    require(a<=k and b<=k,'edge_rank_exceeds_local_width')
    rows=ds.transpose_rect(M,a);rank=len(echelon(M))
    require(k>=a+b-rank,'infeasible_pairing_dimension')
    completion=list(rows);extra=[]
    for j in range(b):
        if solve(echelon(completion),1 << j) is None:
            completion.append(1 << j);extra.append(1 << j)
    require(len(extra)==b-rank,'pairing_completion')
    U=tuple(v|(it.signature(extra,1 << j) << a) for j,v in enumerate(M))
    V=tuple(1 << j for j in range(a))
    assert len(echelon(U))==b and len(echelon(V))==a
    assert tuple(it.signature(V,v) for v in U)==tuple(M)
    return V,U


def source_cycle(source,actions):
    """Certify exact local kernels, then construct an output-equivalent cycle."""
    require('messages' in source,'unsupported_local_control')
    blocks=source['decomposition']['blocks'];edges=source['edges']
    orders=it.graph_orders(len(blocks),edges);require(orders is not None,'interaction_degree')
    block_actions=[tuple(restrict_action(A,block) for A in actions) for block in blocks]
    interfaces={key:it.edge_interface(H,len(blocks[key[0]])) for key,H in edges.items()}
    def endpoint(u,v):
        if v is None:return ()
        e=interfaces[tuple(sorted((u,v)))]
        return e['left'] if u<v else e['right']
    def pairing(u,v):
        if v is None:return ()
        H=interfaces[tuple(sorted((u,v)))]['pairing']
        return H if u<v else cc.transpose(H)
    total=-1 if 0 in source['decomposition']['phase'] else 1;components=[]
    for component in orders:
        order=component['vertices'];cycle=component['cycle'];g=len(order)
        previous=[order[j-1] if j or cycle else None for j in range(g)]
        following=[order[(j+1)%g] if j+1<g or cycle else None for j in range(g)]
        frames=[]
        for j,u in enumerate(order):
            rows=endpoint(u,previous[j])
            P,S=(quotient_action(A,rows) for A in block_actions[u])
            frames.append(copy_basis(P,S))
        locals=[];Vs=[];Us=[];widths=[];sign=1
        for j,u in enumerate(order):
            width=len(blocks[u]);require(width%4==1,'not_a_doubled_star')
            k=(width-1)//4;require(k>=1,'empty_auxiliary_block');widths.append(k)
            incoming=endpoint(u,previous[j]);outgoing=endpoint(u,following[j])
            output_frame=frames[(j+1)%g] if following[j] is not None else ()
            require(len(source['messages'][u])==2,'not_one_local_control')
            require(len(incoming)%2==0 and len(outgoing)%2==0,'odd_edge_rank')
            a=len(incoming)//2;b=len(outgoing)//2;actual=[]
            for message in source['messages'][u]:
                key,c=gr.local_relation(message,incoming,outgoing,pairing(u,following[j]))
                require(c!=0,'vanishing_model_branch')
                key,s=reframe(key,frames[j],output_frame);actual.append((key,c*s))
            # The reverse graph has full outgoing projection and independent columns.
            candidates=[]
            for key,c in actual:
                ni,no,origin,columns,Q=key
                if origin or Q or len(columns)!=2*b:continue
                projected=tuple(v >> (2*a) for v in columns)
                if len(echelon(projected))!=2*b:continue
                inv=cc.inverse(projected)
                graph=tuple(cc.action(columns,v)&((1 << (2*a))-1) for v in inv)
                M=tuple(v >> a for v in graph[:b])
                if graph==tuple(v << a for v in M)+M:candidates.append(M)
            require(candidates,'missing_reverse_graph')
            accepted=None
            for M in candidates:
                model=pair_model(k,a,b,M)
                if sorted(actual)==sorted(model):accepted=(M,1);break
                if sorted(actual)==sorted((key,-c) for key,c in model):accepted=(M,-1);break
            require(accepted is not None,'local_kernel_model_mismatch')
            M,local_sign=accepted;sign*=local_sign
            V,U=realize_pair(k,a,b,M);Vs.append(V);Us.append(U)
            locals.append(dict(block=u,k=k,incoming_rank=a,outgoing_rank=b,
                               compressed_map=M,sign=local_sign,kernels=actual))
        matrices=[]
        for j,U in enumerate(Us):
            next_width=widths[(j+1)%g]
            V=Vs[(j+1)%g] if cycle or j+1<g else ()
            matrices.append(tuple(cc.action(U,it.signature(V,1 << i)) for i in range(next_width)))
        count=cycle_count(matrices,widths);value=sign*count['value'];total*=value
        components.append(dict(**component,locals=locals,matrices=matrices,count=count,value=value))
    require(abs(total)<=1 << sum(map(len,blocks)),'source_count_range')
    return dict(accepted=True,reason='source_linear_chain_count',value=total,components=components,
                local_gaussian_kernels=2*sum(len(c['vertices']) for c in components))


def reduce_source(desc,state_cap=67):
    """Attempt chain aggregation first, then retain capped exact relation fallback."""
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation-state cap required')
    result=qr.reduce_source(desc);actions={};refusals=[]
    try:actions=terminal_actions(result['tree'],result['phase'],physical_copy_actions(result['descriptor']))
    except Refusal as exc:refusals.append(dict(reason=str(exc)))
    retained=gb.enhance_tree(result['tree'])
    lookup={id(r['joint']):r for r in retained['refusals'] if 'joint' in r}
    pending=[result['tree']];certificates=[];fallback=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            source=lookup[id(node['certificate'])]
            try:
                require(id(node) in actions,'copy_action_access_unavailable')
                answer=source_cycle(source,actions[id(node)])
            except Refusal as exc:
                refusals.append(dict(reason=str(exc)));answer=gr.transfer(source,state_cap)
                fallback.append(answer)
            if answer['accepted']:
                if answer['reason']=='source_linear_chain_count':certificates.append(answer)
                width=node['n'];value=answer['value'];node.clear()
                node.update(kind='constant' if value else 'zero',n=width,value=value)
    # Retained exact evaluator propagates original push/product normalization.
    result['cost']=cb.tree_cost(result['tree'])
    result['chain_counts']=dict(certificates=certificates,refusals=refusals,
                               retained=retained,relation_fallback=fallback)
    return result


def reduce_native(n,gates,basis,output,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),state_cap)


evaluate_source=gr.evaluate_source
