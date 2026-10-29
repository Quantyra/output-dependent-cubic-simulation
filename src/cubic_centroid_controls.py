"""S173/R05-11: centroid blocks and streamed joint quadratic readout.

Centroid idempotent discovery was already proved in the S089 phase-center note.
This extension retains quadratic interactions and conditions local cubic controls
rather than enumerating every coordinate in their connected component.
"""
from fractions import Fraction
import cubic_centroid_descent as cc
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve,xor_sum


def add_matrix(a,b):
    return tuple(x^y for x,y in zip(a,b))


def centroid_blocks(poly,n):
    """Polynomial construction of all primitive binary cubic summands."""
    if any(m<0 or m.bit_length()>n or m.bit_count()>3 for m in poly):
        raise ValueError('degree-three ANF required')
    if n<1 or len(ds.image_basis(row for rows in pd.cubic_tensor(poly,n)
                                for row in rows))!=n:
        raise ValueError('full cubic mode rank required')
    basis=tuple(cc.centroid(n,poly));unit=cc.identity(n);zero=(0,)*n
    flat=tuple(cc.flatten(t) for t in basis);span=echelon(flat)
    assert solve(span,cc.flatten(unit)) is not None
    # Explicit algebra checks also charge discovery on unsupported terminals.
    for a in basis:
        for b in basis:
            product=cc.compose(a,b)
            assert product==cc.compose(b,a)
            assert solve(span,cc.flatten(product)) is not None
    defects=tuple(cc.flatten(add_matrix(cc.compose(t,t),t)) for t in basis)
    coefficients=cc.nullspace(ds.transpose_rect(defects,n*n),len(basis))
    idempotents=tuple(cc.unflatten(xor_sum(flat[j] for j in pd.bits(mask)),n)
                      for mask in coefficients)
    for e in idempotents:assert cc.compose(e,e)==e
    projectors=[unit];splits=0
    for e in idempotents:
        following=[]
        for p in projectors:
            a=cc.compose(p,e);b=add_matrix(p,a);splits+=1
            following.extend(t for t in (a,b) if t!=zero)
        projectors=following
        assert len(projectors)<=n
    assert tuple(xor_sum(p[j] for p in projectors) for j in range(n))==unit
    for i,p in enumerate(projectors):
        assert p!=zero and cc.compose(p,p)==p
        for q in projectors[:i]:assert cc.compose(p,q)==zero
        for e in idempotents:assert cc.compose(p,e) in (zero,p)
    blocks=tuple(ds.image_basis(p) for p in projectors)
    columns=tuple(v for block in blocks for v in block)
    assert len(columns)==n and len(echelon(columns))==n
    transformed=pd.substitute_boolean(poly,qr.affine_forms(0,columns,n))
    labels=tuple(j for j,block in enumerate(blocks) for _ in block)
    assert all(len({labels[i] for i in pd.bits(mask)})==1
               for mask in transformed if mask.bit_count()==3)
    return dict(centroid_dimension=len(basis),idempotent_dimension=len(idempotents),
                centroid_basis=basis,idempotents=idempotents,projectors=tuple(projectors),
                blocks=blocks,columns=columns,phase=transformed,splits=splits)


def discover_controls(poly,n):
    """Return a compact certificate; never enumerate joint assignments."""
    decomposition=centroid_blocks(poly,n)
    inv=cc.inverse(decomposition['columns']);inverse_rows=cc.transpose(inv)
    controls=[];local=[];offset=0
    for block in decomposition['blocks']:
        width=len(block);keep=((1 << width)-1) << offset
        phase={mask >> offset for mask in decomposition['phase']
               if mask and mask&keep==mask}
        # At most four local Gaussian sums; their values are not combined:
        # the original phase may have arbitrary quadratic couplings.
        factor=lf.discover_factor(phase,width)
        if factor is None:
            return None,dict(reason='unsupported_primitive_block',
                             block_width=width,decomposition=decomposition)
        for control in factor['controls']:
            controls.append(xor_sum(inverse_rows[offset+j] for j in pd.bits(control)))
        local.append(dict(width=width,controls=factor['controls'],
                          rank=factor['control_rank'],
                          quadratic_kernel_dimension=factor['quadratic_kernel_dimension']))
        offset+=width
    controls=tuple(controls);q=len(controls)
    assert len(echelon(controls))==q
    kernel=tuple(cc.nullspace(controls,n));right=[]
    for j in range(q):
        solution=qr.affine_space([(v,int(i==j)) for i,v in enumerate(controls)],n)
        assert solution is not None
        right.append(solution[0])
    columns=tuple(right)+kernel
    assert len(columns)==n and len(echelon(columns))==n
    phase=pd.substitute_boolean(poly,qr.affine_forms(0,columns,n))
    # Cubic dependence on controls is allowed. No cubic in free variables remains.
    assert all((mask >> q).bit_count()<=2 for mask in phase)
    return dict(n=n,control_rank=q,controls=controls,columns=columns,phase=phase,
                decomposition=decomposition,local=tuple(local),
                assignments=1 << q),dict(reason='ok')


def restricted_quadratic(certificate,assignment):
    q=certificate['control_rank']
    if not 0<=assignment<(1 << q):raise ValueError('invalid control assignment')
    low=(1 << q)-1;phase=set()
    for mask in certificate['phase']:
        control=mask&low
        if assignment&control==control:
            term=mask >> q
            if term in phase:phase.remove(term)
            else:phase.add(term)
    assert all(mask.bit_count()<=2 for mask in phase)
    return phase


def evaluate_controls(certificate):
    q=certificate['control_rank'];width=certificate['n']-q
    return sum(lf.quadratic_value(restricted_quadratic(certificate,x),width)
               for x in range(1 << q))


def tree_cost(tree):
    result=dict(nodes=0,terminals=0,work=0,max_width=0,pushes=0,
                control_leaves=0,gaussian_sums=0,max_controls=0,unsupported_work=0)
    pending=[tree]
    while pending:
        node=pending.pop();kind=node['kind'];result['nodes']+=1
        if kind=='terminal':
            work=1 << node['n'];result['terminals']+=1;result['work']+=work
            result['unsupported_work']+=work
            result['max_width']=max(result['max_width'],node['n'])
        elif kind=='controls':
            q=node['certificate']['control_rank'];result['terminals']+=1
            result['control_leaves']+=1;result['gaussian_sums']+=1 << q
            result['work']+=1 << q;result['max_controls']=max(result['max_controls'],q)
        elif kind in ('zero','constant'):result['terminals']+=1;result['work']+=1
        elif kind=='push':result['pushes']+=1;pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        else:raise ValueError('unknown tree node')
    return result


def enhance_tree(tree):
    previous=qr.tree_cost(tree)
    retained=lf.enhance_tree(tree)
    pending=[tree];accepted=[];refused=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='terminal':
            width=node['n'];certificate,reason=discover_controls(node['phase'],width)
            if certificate is None:
                refused.append(reason);continue
            accepted.append(certificate)
            node.clear();node.update(kind='controls',n=width,certificate=certificate)
    cost=tree_cost(tree)
    assert cost['work']<=retained['current']['work']<=previous['work']
    return dict(previous=previous,retained=retained,current=cost,
                certificates=accepted,refusals=refused,
                block_tests=len(accepted)+len(refused))


def compile_sum(poly,n):
    tree=qr.compile_sum(poly,n)
    return tree,enhance_tree(tree)


def evaluate_tree(tree):
    pending=[(tree,False)];values={}
    while pending:
        node,visited=pending.pop();kind=node['kind'];key=id(node)
        if kind=='constant':values[key]=node['value']
        elif kind=='zero':values[key]=0
        elif kind=='terminal':
            values[key]=sum(-1 if cc.anf_evaluate(node['phase'],x) else 1
                            for x in range(1 << node['n']))
        elif kind=='controls':values[key]=evaluate_controls(node['certificate'])
        elif not visited:
            pending.append((node,True))
            children=node['children'] if kind=='product' else [node['child']]
            pending.extend((child,False) for child in children)
        elif kind=='push':
            values[key]=(1 << node['push']['exponent'])*values.pop(id(node['child']))
        elif kind=='product':
            value=node['sign']
            for child in node['children']:value*=values.pop(id(child))
            values[key]=value
        else:raise ValueError('unknown tree node')
    return values[id(tree)]


def reduce_source(desc):
    result=qr.reduce_source(desc)
    result['centroid_controls']=enhance_tree(result['tree'])
    result['cost']=result['centroid_controls']['current']
    return result


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
