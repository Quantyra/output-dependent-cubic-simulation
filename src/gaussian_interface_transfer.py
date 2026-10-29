"""S173/R05-13: source-derived signed interfaces and path/cycle transfer."""
import gaussian_boundary_factorization as gb
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve


def signature(rows,x):
    return sum(((r&x).bit_count()&1) << j for j,r in enumerate(rows))


def edge_interface(matrix,left_width):
    """Exact quotient of x^T H y; matrix is stored by columns."""
    left=ds.image_basis(matrix)
    right=ds.image_basis(ds.transpose_rect(matrix,left_width))
    rank=len(left)
    assert rank==len(right)
    def representatives(rows,width):
        columns=ds.transpose_rect(rows,width);span=echelon(columns)
        return tuple(solve(span,1 << j) for j in range(len(rows)))
    a=representatives(left,left_width);b=representatives(right,len(matrix))
    pairing=tuple(signature(a,cc.action(matrix,v)) for v in b)
    assert len(echelon(pairing))==rank
    return dict(rank=rank,left=left,right=right,left_lifts=a,right_lifts=b,
                pairing=pairing)


def prepare_message(message,rows):
    """Map possibly dependent endpoint rows to independent Gaussian outputs."""
    U=message['rows'];span=echelon(U)
    coefficients=[]
    for row in rows:
        restricted=signature(message['kernel'],row)
        value=solve(span,restricted)
        assert value is not None
        coefficients.append(value)
    columns=ds.transpose_rect(coefficients,len(U))
    assert len(echelon(columns))==len(U)
    pushed=message['push']
    return dict(signature_origin=signature(rows,message['origin']),
                signature_span=echelon(columns),
                support_span=echelon(pushed['columns']),push=pushed)


def message_value(prepared,value):
    pushed=prepared['push']
    if pushed['zero']:return 0
    y=solve(prepared['signature_span'],value^prepared['signature_origin'])
    if y is None:return 0
    z=solve(prepared['support_span'],y^pushed['origin'])
    if z is None:return 0
    return (-1 if cc.anf_evaluate(pushed['phase'],z) else 1) << pushed['exponent']


def graph_orders(vertices,edges):
    adjacency=[[] for _ in range(vertices)]
    for a,b in edges:adjacency[a].append(b);adjacency[b].append(a)
    if any(len(row)>2 for row in adjacency):return None
    remaining=set(range(vertices));orders=[]
    while remaining:
        seed=min(remaining);component=set();pending=[seed]
        while pending:
            u=pending.pop()
            if u in component:continue
            component.add(u);pending.extend(adjacency[u])
        ends=sorted(u for u in component if len(adjacency[u])<2)
        cycle=not ends;start=ends[0] if ends else min(component)
        order=[];previous=None;u=start
        while True:
            order.append(u)
            choices=sorted(v for v in adjacency[u] if v!=previous)
            if not choices:break
            v=choices[0]
            if v==start:break
            previous,u=u,v
        assert set(order)==component and len(order)==len(component)
        orders.append(dict(vertices=tuple(order),cycle=cycle))
        remaining-=component
    return tuple(orders)


def multiply(a,b,stats):
    assert len(a[0])==len(b)
    rows=len(a);middle=len(b);columns=len(b[0])
    stats['multiply_adds']+=rows*middle*columns
    result=[[sum(a[i][j]*b[j][k] for j in range(middle))
             for k in range(columns)] for i in range(rows)]
    stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                                  max((abs(x).bit_length() for row in result for x in row),default=0))
    return result


def transfer(result,max_edge_rank=2):
    """No control-product enumeration. Refuse before tables if graph/rank fail."""
    if type(max_edge_rank) is not int or max_edge_rank<0:
        raise ValueError('nonnegative edge-rank cap required')
    if 'messages' not in result:
        return dict(accepted=False,reason='unsupported_local_control')
    d=result['decomposition'];edges=result['edges'];blocks=d['blocks']
    orders=graph_orders(len(blocks),edges)
    if orders is None:return dict(accepted=False,reason='interaction_degree',tables_built=0)
    interfaces={key:edge_interface(H,len(blocks[key[0]])) for key,H in edges.items()}
    largest=max((e['rank'] for e in interfaces.values()),default=0)
    if largest>max_edge_rank:
        return dict(accepted=False,reason='edge_rank',max_rank=largest,tables_built=0)
    edge_tables={}
    for key,e in interfaces.items():
        size=1 << e['rank']
        edge_tables[key]=[[(-1)**((u&cc.action(e['pairing'],v)).bit_count()&1)
                           for v in range(size)] for u in range(size)]
    def endpoint(u,v):
        if v is None:return ()
        key=tuple(sorted((u,v)));e=interfaces[key]
        return e['left'] if u< v else e['right']
    def edge_table(u,v):
        table=edge_tables[tuple(sorted((u,v)))]
        return table if u<v else [list(row) for row in zip(*table)]
    stats=dict(interface_entries=0,branch_lookups=0,edge_entries=sum(len(x)**2 for x in edge_tables.values()),
               multiply_adds=0,peak_integer_bits=0)
    tables={};components=[];total=-1 if 0 in d['phase'] else 1
    for component in orders:
        order=component['vertices'];cycle=component['cycle'];count=len(order)
        first_rows=endpoint(order[0],order[-1] if cycle else None)
        size=1 << len(first_rows)
        accumulated=[[int(i==j) for j in range(size)] for i in range(size)]
        for j,u in enumerate(order):
            previous=order[j-1] if j else (order[-1] if cycle else None)
            following=order[j+1] if j+1<count else (order[0] if cycle else None)
            incoming=endpoint(u,previous);outgoing=endpoint(u,following)
            rows=incoming+outgoing
            prepared=tuple(prepare_message(m,rows) for m in result['messages'][u])
            left=1 << len(incoming);right=1 << len(outgoing)
            table=[[sum(message_value(m,a|(b << len(incoming))) for m in prepared)
                    for b in range(right)] for a in range(left)]
            stats['interface_entries']+=left*right
            stats['branch_lookups']+=left*right*len(prepared)
            stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                                           max((abs(x).bit_length() for row in table for x in row),default=0))
            tables[u]=dict(rows=rows,incoming=len(incoming),outgoing=len(outgoing),
                           prepared=prepared,values=table)
            accumulated=multiply(accumulated,table,stats)
            if following is not None:accumulated=multiply(accumulated,edge_table(u,following),stats)
        scalar=sum(accumulated[i][i] for i in range(len(accumulated))) if cycle else accumulated[0][0]
        total*=scalar;components.append(dict(**component,value=scalar))
    assert abs(total)<=1 << sum(len(x) for x in blocks)
    return dict(accepted=True,reason='signed_interface_transfer',value=total,max_rank=largest,
                interfaces=interfaces,edge_tables=edge_tables,tables=tables,
                components=components,stats=stats)


def enhance_tree(tree,max_edge_rank=2):
    retained=gb.enhance_tree(tree)
    pending=[tree];certificates=[];refusals=[]
    lookup={id(r['joint']):r for r in retained['refusals'] if 'joint' in r}
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            source=lookup[id(node['certificate'])]
            result=transfer(source,max_edge_rank)
            if result['accepted']:
                result['previous_joint_branches']=source['joint_branches']
                result['local_branches']=source['local_branches']
                certificates.append(result)
                width=node['n'];value=result['value'];node.clear()
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
                interface_entries=sum(c['stats']['interface_entries'] for c in certificates),
                branch_lookups=sum(c['stats']['branch_lookups'] for c in certificates),
                multiply_adds=sum(c['stats']['multiply_adds'] for c in certificates))


def compile_sum(poly,n,max_edge_rank=2):
    tree=qr.compile_sum(poly,n)
    return tree,enhance_tree(tree,max_edge_rank)


def reduce_source(desc,max_edge_rank=2):
    result=qr.reduce_source(desc)
    result['interface_transfer']=enhance_tree(result['tree'],max_edge_rank)
    result['cost']=result['interface_transfer']['current']
    return result


def reduce_native(n,gates,basis,output,max_edge_rank=2):
    return reduce_source(cc.recognize_native(n,gates,basis,output),max_edge_rank)


evaluate_tree=cb.evaluate_tree
evaluate_source=cb.evaluate_source
