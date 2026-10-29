"""S173/R05-23: exact two-sided linear characters on graded cycles."""
from fractions import Fraction
from functools import lru_cache
import linear_chain_counts as lc
from linear_chain_counts import cc,qr,gb,gr,it,cb,pd,ds,solve,echelon,Refusal,require


def graded_basis(matrices,widths):
    """Construct and certify homogeneous nilpotent strings and a regular basis."""
    profile=lc.cycle_profile(matrices,widths);g=len(widths);M=sum(widths)
    offsets=[];at=0
    for k in widths:offsets.append(at);at+=k
    T=[]
    for j,k in enumerate(widths):
        previous=(j-1)%g
        T.extend(v << offsets[previous] for v in matrices[previous])
    T=tuple(T);powers=[cc.identity(M)]
    for _ in range(M+1):powers.append(cc.compose(T,powers[-1]))
    kernels=[]
    for ell in range(M+2):
        row=[]
        for j,k in enumerate(widths):
            local=powers[ell][offsets[j]:offsets[j]+k]
            row.append(tuple(v << offsets[j] for v in cc.nullspace(ds.transpose_rect(local,M),k)))
        kernels.append(row)
    strings=[];nil_columns=[]
    for ell,j,q in reversed(profile['strings']):
        denominator=list(kernels[ell-1][j])+[cc.action(T,v) for v in kernels[ell+1][(j+1)%g]]
        tops=[]
        for v in kernels[ell][j]:
            if solve(echelon(denominator),v) is None:tops.append(v);denominator.append(v)
        assert len(tops)==q
        for top in tops:
            columns=tuple(cc.action(powers[h],top) for h in range(ell-1,-1,-1))
            assert cc.action(T,columns[0])==0
            assert all(cc.action(T,v)==columns[i-1] for i,v in enumerate(columns) if i)
            start=(j-ell+1)%g
            for i,v in enumerate(columns):
                grade=(start+i)%g
                assert v and v&~(((1 << widths[grade])-1) << offsets[grade])==0
            strings.append(dict(length=ell,top=j,start=start,columns=columns))
            nil_columns.extend(columns)
    regular=[]
    for j,k in enumerate(widths):
        regular.extend(ds.image_basis(powers[M][offsets[j]:offsets[j]+k]))
    regular=tuple(regular)
    assert len(nil_columns)+len(regular)==M
    assert len(echelon(tuple(nil_columns)+regular))==M
    A=lc.restrict_action(T,regular)
    assert len(echelon(A))==len(regular)
    return dict(profile=profile,shift=T,strings=tuple(strings),regular_columns=regular,
                regular_action=A,offsets=tuple(offsets))


def interval_character_sum(g,strings):
    """Signed cyclic subset sum; records (start,length,a_bits,b_bits)."""
    if type(g) is not int or g<1:raise ValueError('positive cycle length required')
    strings=tuple((record[0],record[1],0,record[2]) if len(record)==3 else tuple(record)
                  for record in strings)
    M=sum(ell for start,ell,a,b in strings)
    if any(not 0<=s<g or ell<1 or min(a,b)<0 or max(a,b).bit_length()>ell for s,ell,a,b in strings):
        raise ValueError('invalid string field')
    total=1
    for vertex in range(g):
        value=1
        for start,ell,a,b in strings:
            first=(vertex-start)%g
            if first>=ell:continue
            count=1+(ell-1-first)//g
            last=first+(count-1)*g
            alpha=(a >> last).bit_count()%2;beta=(b&((1 << (first+1))-1)).bit_count()%2
            if count==1:value*=2*(-1)**(alpha*beta)
            elif alpha or beta:value=0;break
            else:value*=4
        total-=value
    stats=dict(first_pairs=0,transitions=0,transition_tables=0,zero_character_transitions=0,
               peak_states=0,peak_integer_bits=abs(total).bit_length())
    @lru_cache(None)
    def weight(r,p,q):
        """q in [0,g), predecessors r<p<q, q-r<=g."""
        assert 0<=q<g and q-g<=r<p<q
        stats['transition_tables']+=1;exponent=0;sign=-1
        for start,ell,a,b in strings:
            s=start if start<=q else start-g
            length=min(ell,g)
            if q<=s+length-1:
                if p<s:
                    exponent+=1
                    if ell<g:
                        alpha=(a >> (q-s)).bit_count()%2
                        beta=(b&((1 << (q-s+1))-1)).bit_count()%2
                        if alpha and beta:sign=-sign
                elif r<s:
                    exponent+=1
                    if (b&((1 << (p-s+1))-1)).bit_count()%2:return None
            # Reverse second-hit test: r,p are the last two interval selections.
            end=(start+ell-1)%g
            end=p+(end-p)%g
            tail_start=end-length+1
            if r>=tail_start and end<q:
                tail=a >> (ell-length)
                if (tail >> (p-tail_start)).bit_count()%2:return None
        return exponent,sign
    def transition(r,p,q):
        shift=(q//g)*g
        return weight(r-shift,p-shift,q-shift)
    for a in range(g):
        for b in range(a+1,g):
            states={(a,b):1};stats['first_pairs']+=1
            for q in range(b+1,g):
                following=dict(states)
                for (r,p),value in states.items():
                    w=transition(r,p,q);stats['transitions']+=1
                    if w is None:stats['zero_character_transitions']+=1;continue
                    exponent,sign=w
                    following[p,q]=following.get((p,q),0)+sign*(value << exponent)
                states={key:value for key,value in following.items() if value}
                stats['peak_states']=max(stats['peak_states'],len(states))
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                    max((abs(v).bit_length() for v in states.values()),default=0))
            for (r,p),value in states.items():
                w1=transition(r,p,a+g);w2=transition(p,a+g,b+g)
                if w1 is not None and w2 is not None:
                    total+=w1[1]*w2[1]*(value << (w1[0]+w2[0]))
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],abs(total).bit_length())
    assert stats['peak_integer_bits']<=2*M+g+3
    return total,stats


def cycle_character(matrices,widths,fields,left_fields=None):
    """Exact cycle sum with arbitrary paired u-side and v-side linear fields."""
    if left_fields is None:left_fields=[0]*len(widths)
    for fs in (fields,left_fields):
        if len(fs)!=len(widths) or any(b<0 or b.bit_length()>k for b,k in zip(fs,widths)):
            raise ValueError('one valid field per vertex required')
    basis=graded_basis(matrices,widths);g=len(widths);M=sum(widths)
    field=sum(b << o for b,o in zip(fields,basis['offsets']))
    left=sum(a << o for a,o in zip(left_fields,basis['offsets']))
    columns=tuple(v for s in basis['strings'] for v in s['columns'])+basis['regular_columns']
    left_coordinates=solve(echelon(columns),left);assert left_coordinates is not None
    strings=[];offset=0
    for s in basis['strings']:
        ell=s['length'];a=(left_coordinates >> offset)&((1 << ell)-1);offset+=ell
        b=it.signature(s['columns'],field)
        strings.append((s['start'],ell,a,b))
    strings=tuple(strings)
    F,stats=interval_character_sum(g,strings)
    A=basis['regular_action'];r=len(A);L=tuple(v^(1 << j) for j,v in enumerate(A))
    kernel=tuple(cc.nullspace(cc.transpose(L),r))
    left_kernel=tuple(cc.nullspace(L,r))
    reg_field=it.signature(basis['regular_columns'],field)
    reg_left=left_coordinates >> offset
    equations=[(it.signature(kernel,v),(v&reg_left).bit_count()%2) for v in left_kernel]
    support=qr.affine_space(equations,len(kernel));regular=0
    if support is not None:
        origin,free=support
        S0=cc.action(kernel,origin);N=tuple(cc.action(kernel,v) for v in free)
        assert len(left_kernel)+len(N)==basis['profile']['regular_nullity']
        if not any((reg_field&v).bit_count()%2 for v in N):
            regular=(-1)**((reg_field&S0).bit_count()%2) << (len(left_kernel)+len(N))
    scaled=(-1)**g*(F+regular-1);expectation=Fraction(scaled,1 << (M+g))
    assert -1<=expectation<=1
    return dict(basis=basis,field_strings=strings,alternating_sum=F,regular_character=regular,
                regular_support=support,value=scaled << (2*M),expectation=expectation,
                probability=(1-expectation)/2,stats=stats)


def pair_model(k,a,b,M,field,shift=0,cross=0):
    """Full canonical local kernels, including the computed linear phase."""
    require(0<=field<(1 << b),'invalid_local_field')
    require(0<=shift<(1 << a) and cross in (0,1),'invalid_local_affine_shift')
    one_columns=tuple((cc.action(M,1 << j) << a)|(1 << (2*a+j)) for j in range(b))
    one_columns+=tuple(cc.action(M,1 << j)|(1 << (2*a+b+j)) for j in range(b))
    one_phase={1 << j for j in pd.bits(field|(field << b))}
    one,s1=gr.canonical(2*a,2*b,shift|(shift << a),one_columns,one_phase)
    zero_columns=tuple((1 << j)|(1 << (a+j)) for j in range(a))
    zero_columns+=tuple(cc.action(M,1 << j)|(1 << (2*a+j))|(1 << (2*a+b+j)) for j in range(b))
    zero_phase={1 << (a+j) for j in pd.bits(field)}
    if cross:zero_phase.add(0)
    zero,s0=gr.canonical(2*a,2*b,shift,zero_columns,zero_phase)
    return ((zero,(1 << (3*k-a))*s0),(one,-(1 << (2*k))*s1))


def realize_fields(V,U,k,shift,field,cross):
    """Solve V^T a=shift, U^T b=field, a dot b=cross in polynomial time."""
    sa=qr.affine_space([(v,(shift >> i)&1) for i,v in enumerate(V)],k)
    sb=qr.affine_space([(u,(field >> i)&1) for i,u in enumerate(U)],k)
    require(sa is not None and sb is not None,'infeasible_linear_field')
    a,A=sa;b,B=sb
    if (a&b).bit_count()%2!=cross:
        av=next((v for v in A if (v&b).bit_count()%2),None)
        bv=next((v for v in B if (v&a).bit_count()%2),None)
        if av is not None:a^=av
        elif bv is not None:b^=bv
        else:
            pair=next(((v,w) for v in A for w in B if (v&w).bit_count()%2),None)
            require(pair is not None,'infeasible_field_pairing')
            a^=pair[0];b^=pair[1]
    assert it.signature(V,a)==shift and it.signature(U,b)==field and (a&b).bit_count()%2==cross
    return a,b


def certify_component(source,block_actions,interfaces,component):
    blocks=source['decomposition']['blocks']
    def endpoint(u,v):
        if v is None:return ()
        e=interfaces[tuple(sorted((u,v)))]
        return e['left'] if u<v else e['right']
    def pairing(u,v):
        if v is None:return ()
        H=interfaces[tuple(sorted((u,v)))]['pairing']
        return H if u<v else cc.transpose(H)
    order=component['vertices'];cycle=component['cycle'];g=len(order)
    previous=[order[j-1] if j or cycle else None for j in range(g)]
    following=[order[(j+1)%g] if j+1<g or cycle else None for j in range(g)]
    frames=[]
    for j,u in enumerate(order):
        rows=endpoint(u,previous[j])
        P,S=(lc.quotient_action(A,rows) for A in block_actions[u])
        frames.append(lc.copy_basis(P,S))
    locals=[];Vs=[];Us=[];widths=[];fields=[];left_fields=[];sign=1
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
            key,s=lc.reframe(key,frames[j],output_frame);actual.append((key,c*s))
        candidates=[]
        for key,c in actual:
            ni,no,origin,columns,Q=key
            if len(columns)!=2*b:continue
            projected=tuple(v >> (2*a) for v in columns)
            if len(echelon(projected))!=2*b:continue
            inv=cc.inverse(projected)
            graph=tuple(cc.action(columns,v)&((1 << (2*a))-1) for v in inv)
            offset=cc.action(inv,origin >> (2*a))
            intercept=(origin^cc.action(columns,offset))&((1 << (2*a))-1)
            shift=intercept&((1 << a)-1)
            if intercept!=shift|(shift << a):continue
            M=tuple(v >> a for v in graph[:b])
            if graph!=tuple(v << a for v in M)+M:continue
            phase=pd.substitute_boolean(Q,qr.affine_forms(offset,inv,2*b));phase.discard(0)
            if any(t.bit_count()!=1 for t in phase):continue
            bits=sum(phase);field=bits&((1 << b)-1)
            if bits!=field|(field << b):continue
            candidates.append((M,field,shift))
        require(candidates,'missing_affine_reverse_graph')
        accepted=None
        for M,field,shift in candidates:
            for cross in (0,1):
                model=pair_model(k,a,b,M,field,shift,cross)
                if sorted(actual)==sorted(model):accepted=(M,field,shift,cross,1);break
                if sorted(actual)==sorted((key,-c) for key,c in model):accepted=(M,field,shift,cross,-1);break
            if accepted is not None:break
        require(accepted is not None,'local_character_model_mismatch')
        M,field,shift,cross,local_sign=accepted;sign*=local_sign
        V,U=lc.realize_pair(k,a,b,M);Vs.append(V);Us.append(U)
        left_field,physical_field=realize_fields(V,U,k,shift,field,cross)
        left_fields.append(left_field)
        fields.append(physical_field)
        locals.append(dict(block=u,k=k,incoming_rank=a,outgoing_rank=b,compressed_map=M,
                           edge_field=field,incoming_shift=shift,field_pairing=cross,
                           surrogate_field=physical_field,surrogate_left_field=left_field,
                           sign=local_sign,kernels=actual))
    matrices=[]
    for j,U in enumerate(Us):
        next_width=widths[(j+1)%g]
        V=Vs[(j+1)%g] if cycle or j+1<g else ()
        matrices.append(tuple(cc.action(U,it.signature(V,1 << i)) for i in range(next_width)))
    count=cycle_character(matrices,widths,fields,left_fields)
    return dict(**component,locals=locals,matrices=matrices,fields=fields,left_fields=left_fields,
                count=count,value=sign*count['value'])


def source_characters(source,actions):
    require('messages' in source,'unsupported_local_control')
    blocks=source['decomposition']['blocks'];edges=source['edges']
    orders=it.graph_orders(len(blocks),edges);require(orders is not None,'interaction_degree')
    block_actions=[tuple(lc.restrict_action(A,block) for A in actions) for block in blocks]
    interfaces={key:it.edge_interface(H,len(blocks[key[0]])) for key,H in edges.items()}
    total=-1 if 0 in source['decomposition']['phase'] else 1;components=[];attempts=[]
    for component in orders:
        try:answer=certify_component(source,block_actions,interfaces,component)
        except Refusal as exc:
            attempts.append(str(exc));reverse=dict(component,vertices=tuple(reversed(component['vertices'])))
            answer=certify_component(source,block_actions,interfaces,reverse)
        total*=answer['value'];components.append(answer)
    require(abs(total)<=1 << sum(map(len,blocks)),'source_count_range')
    return dict(accepted=True,reason='source_linear_chain_character',value=total,components=components,
                orientation_refusals=attempts,local_gaussian_kernel_bound=4*sum(len(c['vertices']) for c in components))


def reduce_source(desc,state_cap=67):
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation-state cap required')
    result=qr.reduce_source(desc);actions={};refusals=[]
    try:actions=lc.terminal_actions(result['tree'],result['phase'],lc.physical_copy_actions(result['descriptor']))
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
                answer=source_characters(source,actions[id(node)])
            except Refusal as exc:
                refusals.append(dict(reason=str(exc)));answer=gr.transfer(source,state_cap);fallback.append(answer)
            if answer['accepted']:
                if answer['reason']=='source_linear_chain_character':certificates.append(answer)
                width=node['n'];value=answer['value'];node.clear()
                node.update(kind='constant' if value else 'zero',n=width,value=value)
    result['cost']=cb.tree_cost(result['tree'])
    result['chain_characters']=dict(certificates=certificates,refusals=refusals,
                                   retained=retained,relation_fallback=fallback)
    return result


def reduce_native(n,gates,basis,output,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),state_cap)


evaluate_source=gr.evaluate_source
