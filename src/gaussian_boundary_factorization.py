"""S173/R05-12: factor signed sums using local Gaussian boundary supports."""
from itertools import product
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve,xor_sum


def fast_centroid(poly,n):
    """Exactly the retained equations/order, assembled from packed tensor rows."""
    tensor=pd.cubic_tensor(poly,n)
    def equations():
        for i,j,k in product(range(n),repeat=3):
            first=tensor[j][k] << (n*i)
            yield first^(tensor[i][k] << (n*j))
            yield first^(tensor[i][j] << (n*k))
    return tuple(cc.unflatten(x,n) for x in cc.nullspace(equations(),n*n))


def primitive_blocks(poly,n):
    if any(m<0 or m.bit_length()>n or m.bit_count()>3 for m in poly):
        raise ValueError('degree-three ANF required')
    if n<1 or len(echelon(row for rows in pd.cubic_tensor(poly,n) for row in rows))!=n:
        raise ValueError('full cubic mode rank required')
    basis=fast_centroid(poly,n);unit=cc.identity(n);zero=(0,)*n
    flat=tuple(cc.flatten(t) for t in basis);span=echelon(flat)
    assert solve(span,cc.flatten(unit)) is not None
    for a in basis:
        for b in basis:
            ab=cc.compose(a,b)
            assert ab==cc.compose(b,a) and solve(span,cc.flatten(ab)) is not None
    defects=tuple(cc.flatten(cb.add_matrix(cc.compose(t,t),t)) for t in basis)
    coefficients=cc.nullspace(ds.transpose_rect(defects,n*n),len(basis))
    idempotents=tuple(cc.unflatten(xor_sum(flat[j] for j in pd.bits(mask)),n)
                      for mask in coefficients)
    projectors=[unit]
    for e in idempotents:
        assert cc.compose(e,e)==e
        following=[]
        for p in projectors:
            a=cc.compose(p,e)
            following.extend(t for t in (a,cb.add_matrix(p,a)) if t!=zero)
        projectors=following
        assert len(projectors)<=n
    assert tuple(xor_sum(p[j] for p in projectors) for j in range(n))==unit
    for i,p in enumerate(projectors):
        assert cc.compose(p,p)==p and p!=zero
        assert all(cc.compose(p,q)==zero for q in projectors[:i])
        assert all(cc.compose(p,e) in (zero,p) for e in idempotents)
    blocks=tuple(ds.image_basis(p) for p in projectors)
    columns=tuple(x for block in blocks for x in block)
    assert len(columns)==n and len(echelon(columns))==n
    phase=pd.substitute_boolean(poly,qr.affine_forms(0,columns,n))
    labels=tuple(j for j,block in enumerate(blocks) for _ in block)
    assert all(len({labels[i] for i in pd.bits(m)})==1 for m in phase if m.bit_count()==3)
    return dict(blocks=blocks,columns=columns,phase=phase,projectors=tuple(projectors),
                centroid_dimension=len(basis),idempotent_dimension=len(idempotents))


def split_phase(decomposition):
    widths=[len(b) for b in decomposition['blocks']]
    labels=[(j,i) for j,w in enumerate(widths) for i in range(w)]
    local=[set() for _ in widths];edges={}
    for mask in decomposition['phase']:
        if not mask:continue
        places=[labels[i] for i in pd.bits(mask)]
        if len({j for j,i in places})==1:
            local[places[0][0]].add(sum(1 << i for j,i in places))
        else:
            assert len(places)==2
            (a,i),(b,j)=places
            assert a<b
            matrix=edges.setdefault((a,b),[0]*widths[b])
            matrix[j] ^= 1 << i
    boundaries=[[] for _ in widths]
    for (a,b),matrix in edges.items():
        boundaries[a].extend(matrix)
        boundaries[b].extend(ds.transpose_rect(matrix,widths[a]))
    return local,{key:tuple(v) for key,v in edges.items()},tuple(ds.image_basis(r) for r in boundaries)


def local_messages(phase,width,boundary,factor):
    kernel=factor['columns'];free=width-factor['control_rank'];messages=[]
    restricted_rows=ds.image_basis(sum(((row&v).bit_count()&1) << j
                                      for j,v in enumerate(kernel)) for row in boundary)
    map_columns=ds.transpose_rect(restricted_rows,free)
    span=echelon(map_columns)
    right=tuple(solve(span,1 << j) for j in range(len(restricted_rows)))
    for t,(origin,quadratic,value) in enumerate(zip(factor['origins'],factor['phases'],factor['values'])):
        pushed=qr.quadratic_pushforward(quadratic,restricted_rows,free)
        message=dict(assignment=t,origin=origin,kernel=kernel,quadratic=quadratic,
                     rows=restricted_rows,push=pushed,value=value)
        if pushed['zero']:
            assert value==0
            message.update(lift_origin=0,lift_columns=())
        else:
            lift_origin=origin^cc.action(kernel,cc.action(right,pushed['origin']))
            lift_columns=tuple(cc.action(kernel,cc.action(right,v)) for v in pushed['columns'])
            message.update(lift_origin=lift_origin,lift_columns=lift_columns)
        messages.append(message)
    return tuple(messages)


def cross_restriction(matrix,a,b):
    """Full bilinear polynomial on two affine supports, including offsets."""
    ao=a['lift_origin'];bo=b['lift_origin']
    ac=a['lift_columns'];bc=b['lift_columns'];left=len(ac);phase=set()
    hb=cc.action(matrix,bo)
    if (ao&hb).bit_count()&1:phase.add(0)
    for i,v in enumerate(ac):
        if (v&hb).bit_count()&1:phase.add(1 << i)
    for j,v in enumerate(bc):
        hv=cc.action(matrix,v)
        if (ao&hv).bit_count()&1:phase.add(1 << (left+j))
        for i,u in enumerate(ac):
            if (u&hv).bit_count()&1:phase.add((1 << i)|(1 << (left+j)))
    return phase


def joint_certificate(poly,n,decomposition,factors):
    invrows=cc.transpose(cc.inverse(decomposition['columns']))
    controls=[];offset=0
    for block,factor in zip(decomposition['blocks'],factors):
        controls.extend(xor_sum(invrows[offset+j] for j in pd.bits(row))
                        for row in factor['controls'])
        offset+=len(block)
    controls=tuple(controls);q=len(controls);kernel=tuple(cc.nullspace(controls,n))
    right=tuple(qr.affine_space([(v,int(i==j)) for i,v in enumerate(controls)],n)[0]
                for j in range(q))
    columns=right+kernel
    assert len(columns)==n and len(echelon(columns))==n
    phase=pd.substitute_boolean(poly,qr.affine_forms(0,columns,n))
    assert all((mask >> q).bit_count()<=2 for mask in phase)
    return dict(n=n,control_rank=q,controls=controls,columns=columns,phase=phase)


def discover(poly,n):
    d=primitive_blocks(poly,n);local,edges,boundaries=split_phase(d)
    factors=[]
    for phase,block in zip(local,d['blocks']):
        factor=lf.discover_factor(phase,len(block))
        if factor is None:
            return dict(accepted=False,reason='unsupported_local_control',decomposition=d)
        factors.append(factor)
    messages=tuple(local_messages(p,len(block),r,f)
                   for p,block,r,f in zip(local,d['blocks'],boundaries,factors))
    result=dict(accepted=False,decomposition=d,edges=edges,boundaries=boundaries,
                factors=tuple(factors),messages=messages,local_branches=sum(len(x) for x in messages),
                joint_branches=1 << sum(f['control_rank'] for f in factors),pair_checks=0)
    if any(all(x['push']['zero'] for x in group) for group in messages):
        result.update(accepted=True,reason='zero_boundary_message',value=0);return result
    for (a,b),matrix in sorted(edges.items()):
        for x in messages[a]:
            if x['push']['zero']:continue
            for y in messages[b]:
                if y['push']['zero']:continue
                result['pair_checks']+=1
                restricted=cross_restriction(matrix,x,y)
                if restricted:
                    result.update(reason='nonvanishing_cross_support',
                                  witness=dict(edge=(a,b),assignments=(x['assignment'],y['assignment']),
                                               phase=restricted))
                    result['joint']=joint_certificate(poly,n,d,factors)
                    return result
    value=-1 if 0 in d['phase'] else 1
    for group in messages:value*=sum(x['value'] for x in group)
    result.update(accepted=True,reason='annihilated_cross_support',value=value)
    return result


def enhance_tree(tree):
    before=qr.tree_cost(tree);pending=[tree];certificates=[];refusals=[];old_factors=0
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='terminal':
            width=node['n'];result=discover(node['phase'],width)
            if result['accepted']:
                certificates.append(result);value=result['value'];node.clear()
                node.update(kind='constant' if value else 'zero',n=width,value=value)
            elif 'joint' in result:
                refusals.append(result);node.clear()
                node.update(kind='controls',n=width,certificate=result['joint'])
            else:
                # Preserve the original global one/two-control fallback.
                factor=lf.discover_factor(node['phase'],width)
                refusals.append(result)
                if factor is not None:
                    value=factor['value'];old_factors+=1;node.clear()
                    node.update(kind='constant' if value else 'zero',n=width,value=value)
    pending=[(tree,False)]
    while pending:
        node,visited=pending.pop();kind=node['kind']
        if kind not in ('product','push'):continue
        children=node['children'] if kind=='product' else [node['child']]
        if not visited:
            pending.append((node,True));pending.extend((x,False) for x in children)
        elif any(x['kind']=='zero' for x in children):
            width=node['n'];node.clear();node.update(kind='zero',n=width)
    cost=cb.tree_cost(tree)
    assert cost['work']<=before['work']
    return dict(previous=before,current=cost,certificates=certificates,refusals=refusals,
                retained_global_factors=old_factors,
                local_branches=sum(c.get('local_branches',0) for c in certificates+refusals),
                pair_checks=sum(c.get('pair_checks',0) for c in certificates+refusals))


def compile_sum(poly,n):
    tree=qr.compile_sum(poly,n)
    return tree,enhance_tree(tree)


def reduce_source(desc):
    result=qr.reduce_source(desc)
    result['support_factorization']=enhance_tree(result['tree'])
    result['cost']=result['support_factorization']['current']
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


evaluate_tree=cb.evaluate_tree
evaluate_source=cb.evaluate_source
