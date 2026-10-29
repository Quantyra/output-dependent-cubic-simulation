"""S173/R05-14: paid block-cut discovery and signed Gaussian joins."""
import gaussian_interface_transfer as it
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve


def cross_matrix(source):
    widths=[len(x) for x in source['decomposition']['blocks']]
    offsets=[];total=0
    for w in widths:offsets.append(total);total+=w
    matrix=[0]*total
    for (a,b),H in source['edges'].items():
        for j,column in enumerate(H):
            for i in pd.bits(column):
                x=offsets[a]+i;y=offsets[b]+j
                matrix[y] ^= 1 << x;matrix[x] ^= 1 << y
    masks=tuple(((1 << w)-1) << o for w,o in zip(widths,offsets))
    assert tuple(matrix)==cc.transpose(matrix)
    return tuple(matrix),masks,tuple(offsets)


def cut_rank(matrix,mask):
    outside=((1 << len(matrix))-1)^mask
    return len(echelon(matrix[i]&outside for i in pd.bits(mask)))


def cut_certificate(matrix,mask):
    outside=((1 << len(matrix))-1)^mask
    positions=tuple(pd.bits(mask))
    columns=tuple(matrix[i]&outside for i in positions)
    basis=ds.image_basis(columns);span=echelon(columns)
    lifts=tuple(sum(1 << positions[i] for i in pd.bits(solve(span,v))) for v in basis)
    assert all(cc.action(matrix,x)&outside==v for x,v in zip(lifts,basis))
    return dict(mask=mask,basis=basis,lifts=lifts,rank=len(basis))


def discover_order(matrix,masks):
    selected=0;remaining=set(range(len(masks)));order=[];ranks=[];candidates=[]
    while remaining:
        choices=[]
        for j in sorted(remaining):
            rank=cut_rank(matrix,selected|masks[j]);choices.append((rank,j))
            candidates.append((len(order),j,rank))
        rank,j=min(choices);selected |= masks[j];remaining.remove(j)
        order.append(j);ranks.append(rank)
    return dict(order=tuple(order),ranks=tuple(ranks),candidates=tuple(candidates),
                max_rank=max(ranks,default=0))


def leaf_table(source,j,matrix,cut,offset):
    width=len(source['decomposition']['blocks'][j])
    columns=tuple(matrix[offset+i] for i in range(width))
    rows=ds.image_basis(ds.transpose_rect(columns,len(matrix)))
    assert len(rows)==cut['rank']
    prepared=tuple(it.prepare_message(m,rows) for m in source['messages'][j])
    values=[]
    for word in range(1 << cut['rank']):
        representative=cc.action(cut['lifts'],word) >> offset
        signature=it.signature(rows,representative)
        values.append(sum(it.message_value(m,signature) for m in prepared))
    return dict(cut=cut,rows=rows,prepared=prepared,values=values)


def join_tables(left,right,parent):
    """Preserve structural signatures even when their signed value is zero."""
    L=left['cut'];R=right['cut']
    assert not L['mask']&R['mask'] and parent['mask']==L['mask']|R['mask']
    outside=~parent['mask'];span=echelon(parent['basis'])
    signatures_l=tuple(cc.action(L['basis'],s) for s in range(1 << L['rank']))
    signatures_r=tuple(cc.action(R['basis'],s) for s in range(1 << R['rank']))
    reps_r=tuple(cc.action(R['lifts'],s) for s in range(1 << R['rank']))
    values=[0]*(1 << parent['rank'])
    for a,sig_a in enumerate(signatures_l):
        for b,sig_b in enumerate(signatures_r):
            gamma=solve(span,(sig_a^sig_b)&outside)
            assert gamma is not None
            sign=-1 if (sig_a&reps_r[b]).bit_count()&1 else 1
            values[gamma]+=sign*left['values'][a]*right['values'][b]
    return dict(cut=parent,values=values,
                pairs=len(signatures_l)*len(signatures_r))


def contract(source,max_leaf_rank=4,max_cut_rank=4):
    for value in (max_leaf_rank,max_cut_rank):
        if type(value) is not int or value<0:raise ValueError('nonnegative rank caps required')
    if 'messages' not in source:
        return dict(accepted=False,reason='unsupported_local_control',tables_built=0)
    matrix,masks,offsets=cross_matrix(source)
    leaf_ranks=tuple(cut_rank(matrix,mask) for mask in masks)
    if max(leaf_ranks,default=0)>max_leaf_rank:
        return dict(accepted=False,reason='leaf_rank',leaf_ranks=leaf_ranks,tables_built=0)
    plan=discover_order(matrix,masks)
    if plan['max_rank']>max_cut_rank:
        return dict(accepted=False,reason='selected_cut_rank',plan=plan,
                    leaf_ranks=leaf_ranks,tables_built=0)
    leaves={j:leaf_table(source,j,matrix,cut_certificate(matrix,masks[j]),offsets[j])
            for j in range(len(masks))}
    current=dict(cut=cut_certificate(matrix,0),values=[1]);prefixes=[];mask=0
    stats=dict(leaf_entries=sum(len(t['values']) for t in leaves.values()),
               branch_lookups=sum(len(leaves[j]['values'])*len(source['messages'][j]) for j in leaves),
               prefix_entries=1,join_pairs=0,rank_candidates=len(plan['candidates']),
               peak_integer_bits=1)
    for j in plan['order']:
        mask |= masks[j]
        current=join_tables(current,leaves[j],cut_certificate(matrix,mask))
        prefixes.append(dict(block=j,**current))
        stats['prefix_entries']+=len(current['values']);stats['join_pairs']+=current['pairs']
        stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                                      max(abs(x).bit_length() for x in current['values']))
    assert current['cut']['rank']==0 and len(current['values'])==1
    sign=-1 if 0 in source['decomposition']['phase'] else 1
    value=sign*current['values'][0]
    assert abs(value)<=1 << len(matrix)
    return dict(accepted=True,reason='signed_block_cut_contraction',value=value,matrix=matrix,
                masks=masks,offsets=offsets,plan=plan,leaves=leaves,prefixes=prefixes,stats=stats)


def enhance_tree(tree,max_leaf_rank=4,max_cut_rank=4):
    retained=it.enhance_tree(tree)
    lookup={id(r['joint']):r for r in retained['retained']['refusals'] if 'joint' in r}
    pending=[tree];certificates=[];refusals=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            source=lookup[id(node['certificate'])]
            result=contract(source,max_leaf_rank,max_cut_rank)
            if result['accepted']:
                result['previous_joint_branches']=source['joint_branches']
                result['local_branches']=source['local_branches']
                certificates.append(result);width=node['n'];value=result['value'];node.clear()
                node.update(kind='constant' if value else 'zero',n=width,value=value)
            else:refusals.append(result)
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
    assert cost['work']<=retained['current']['work']
    return dict(previous=retained['current'],current=cost,retained=retained,
                certificates=certificates,refusals=refusals,
                leaf_entries=sum(c['stats']['leaf_entries'] for c in certificates),
                join_pairs=sum(c['stats']['join_pairs'] for c in certificates),
                rank_candidates=sum(c.get('stats',{}).get('rank_candidates',
                                    len(c.get('plan',{}).get('candidates',()))) for c in certificates+refusals))


def compile_sum(poly,n,max_leaf_rank=4,max_cut_rank=4):
    tree=qr.compile_sum(poly,n)
    return tree,enhance_tree(tree,max_leaf_rank,max_cut_rank)


def reduce_source(desc,max_leaf_rank=4,max_cut_rank=4):
    result=qr.reduce_source(desc)
    result['block_cut_contraction']=enhance_tree(result['tree'],max_leaf_rank,max_cut_rank)
    result['cost']=result['block_cut_contraction']['current']
    return result


def reduce_native(n,gates,basis,output,max_leaf_rank=4,max_cut_rank=4):
    return reduce_source(cc.recognize_native(n,gates,basis,output),max_leaf_rank,max_cut_rank)


evaluate_tree=cb.evaluate_tree
evaluate_source=cb.evaluate_source
