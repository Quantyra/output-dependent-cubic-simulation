"""S173/R05-10: discover one or two controlling cubic covectors.

This extends the retained R05-09 tree without changing its source or receipt.
Every accepted factor space is checked by all full affine phase restrictions.
The two-form search tests an explicit basis, not all its linear combinations.
"""
from itertools import combinations
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
from magic_residual_counts import quadratic_sum


def linear_wedge_kernel(poly,n):
    cubic={mask for mask in poly if mask.bit_count()==3}
    def equations():
        for indices in combinations(range(n),4):
            mask=sum(1 << j for j in indices)
            row=sum(1 << j for j in indices if mask^(1 << j) in cubic)
            if row:yield row
    return tuple(cc.nullspace(equations(),n))


def quadratic_value(poly,n):
    if any(mask.bit_count()>2 for mask in poly):raise ValueError('quadratic required')
    return quadratic_sum(int(0 in poly),
                         {m.bit_length()-1 for m in poly if m.bit_count()==1},
                         {tuple(pd.bits(m)) for m in poly if m.bit_count()==2},n)


def quadratic_wedge_kernel(poly,n):
    cubic={mask for mask in poly if mask.bit_count()==3}
    pairs=tuple((1 << i)|(1 << j) for i,j in combinations(range(n),2))
    positions={mask:j for j,mask in enumerate(pairs)}
    def equations():
        for indices in combinations(range(n),5):
            mask=sum(1 << j for j in indices);row=0
            for i,j in combinations(indices,2):
                pair=(1 << i)|(1 << j)
                if mask^pair in cubic:row ^= 1 << positions[pair]
            if row:yield row
    return pairs,tuple(cc.nullspace(equations(),len(pairs)))


def two_form_matrix(value,pairs,n):
    columns=[0]*n
    for j in pd.bits(value):
        a,b=tuple(pd.bits(pairs[j]));columns[a] ^= 1 << b;columns[b] ^= 1 << a
    return tuple(columns)


def discover_factor(poly,n):
    poly=set(poly)
    if any(mask<0 or mask.bit_length()>n or mask.bit_count()>3 for mask in poly):
        raise ValueError('degree-three ANF required')
    kernel=linear_wedge_kernel(poly,n)
    if kernel:
        controls=(kernel[0],);quadratic_dimension=None;form=None
    else:
        pairs,second=quadratic_wedge_kernel(poly,n);quadratic_dimension=len(second)
        controls=None;form=None
        for candidate in second:
            image=ds.image_basis(two_form_matrix(candidate,pairs,n))
            if len(image)==2:
                controls=image;form=candidate;break
        if controls is None:return None
    r=len(controls);columns=tuple(cc.nullspace(controls,n))
    assert len(columns)==n-r
    origins=[];phases=[];values=[]
    for bits in range(1 << r):
        origin,_=qr.affine_space([(u,(bits >> j)&1) for j,u in enumerate(controls)],n)
        phase=pd.substitute_boolean(poly,qr.affine_forms(origin,columns,n))
        if any(mask.bit_count()>2 for mask in phase):
            raise AssertionError('exterior factor did not remove all cubic terms')
        origins.append(origin);phases.append(phase);values.append(quadratic_value(phase,n-r))
    return dict(control_rank=r,controls=controls,factor=controls[0] if r==1 else None,
                linear_kernel=kernel,quadratic_kernel_dimension=quadratic_dimension,
                two_form=form,origins=origins,columns=columns,
                phases=phases,values=values,value=sum(values))


def enhance_tree(tree):
    """Mutate only a newly compiled tree, never a retained on-disk artifact."""
    before=qr.tree_cost(tree);pending=[tree];tested=accepted=systems=0;certificates=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='product':pending.extend(node['children'])
        elif kind=='push':pending.append(node['child'])
        elif kind=='terminal':
            tested+=1;certificate=discover_factor(node['phase'],node['n'])
            systems+=1 if certificate is not None and certificate['control_rank']==1 else 2
            if certificate is None:
                node['factor_kernel_dimension']=0
                continue
            accepted+=1;certificate['n']=node['n']
            certificates.append(certificate)
            width=node['n'];value=certificate['value']
            node.clear();node.update(kind='constant' if value else 'zero',n=width,
                                     value=value,method='conditioned_quadratic_fibers')
    # Newly evaluated zero factors can remove still unsupported cubic siblings.
    pending=[(tree,False)]
    while pending:
        node,visited=pending.pop();kind=node['kind']
        if kind not in ('product','push'):continue
        children=node['children'] if kind=='product' else [node['child']]
        if not visited:
            pending.append((node,True));pending.extend((child,False) for child in children)
        elif any(child['kind']=='zero' for child in children):
            width=node['n'];node.clear();node.update(kind='zero',n=width,reason='factor_zero')
    after=qr.tree_cost(tree)
    assert after['work']<=before['work']
    return dict(previous=before,current=after,factor_tests=tested,factors_found=accepted,
                wedge_systems=systems,quadratic_sums=sum(len(c['values']) for c in certificates),
                certificates=certificates)


def compile_sum(poly,n):
    tree=qr.compile_sum(poly,n)
    details=enhance_tree(tree)
    return tree,details


def reduce_source(desc):
    result=qr.reduce_source(desc)
    result['factor_discovery']=enhance_tree(result['tree'])
    result['cost']=result['factor_discovery']['current']
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluate_source(result,bits):
    return qr.evaluate_source(result,bits)
