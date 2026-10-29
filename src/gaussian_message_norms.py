"""S173/R05-16: exact absolute mass of bounded Gaussian boundary mixtures."""
from itertools import product
import cubic_centroid_descent as cc
import cubic_linear_factors as lf
import gaussian_boundary_factorization as gb
import gaussian_interface_transfer as it
import gaussian_pair_envelopes as pe
import quadratic_pushforward_recursion as qr
import field_defect_subspaces as ds
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve


def affine_branch(width,origin,columns,phase,amplitude):
    """A signed quadratic on an affine support, in its own free coordinates."""
    columns=tuple(columns);phase=set(phase)
    if type(width) is not int or width<0 or not 0<=origin<(1 << width):
        raise ValueError('valid ambient width and origin required')
    if any(not 0<=v<(1 << width) for v in columns) or len(echelon(columns))!=len(columns):
        raise ValueError('independent support columns required')
    if any(m<0 or m.bit_length()>len(columns) or m.bit_count()>2 for m in phase):
        raise ValueError('quadratic phase in support coordinates required')
    if type(amplitude) is not int or amplitude<=0:raise ValueError('positive integer amplitude required')
    equations=tuple((row,(row&origin).bit_count()%2) for row in cc.nullspace(columns,width))
    return dict(width=width,origin=origin,columns=columns,span=echelon(columns),
                phase=phase,amplitude=amplitude,equations=equations)


def source_branch(message,rows):
    pushed=message['push']
    if pushed['zero']:return None
    U=message['rows'];span=echelon(U)
    coefficients=tuple(solve(span,it.signature(message['kernel'],row)) for row in rows)
    assert all(c is not None for c in coefficients)
    columns=ds.transpose_rect(coefficients,len(U))
    assert len(echelon(columns))==len(U)
    origin=it.signature(rows,message['origin'])^cc.action(columns,pushed['origin'])
    support=tuple(cc.action(columns,c) for c in pushed['columns'])
    return affine_branch(len(rows),origin,support,pushed['phase'],1 << pushed['exponent'])


def absolute_coefficients(amplitudes):
    """Integer coefficients for 2^t*abs(sum_i a_i z_i), on z_i in {-1,0,1}."""
    t=len(amplitudes);coefficients={}
    basis={0:((0,2),(2,-2)),-1:((1,-1),(2,1)),1:((1,1),(2,1))}
    for values in product((-1,0,1),repeat=t):
        magnitude=abs(sum(a*z for a,z in zip(amplitudes,values)))
        if not magnitude:continue
        for terms in product(*(basis[z] for z in values)):
            powers=tuple(e for e,c in terms);coefficient=magnitude
            for e,c in terms:coefficient*=c
            coefficients[powers]=coefficients.get(powers,0)+coefficient
    return {powers:c for powers,c in coefficients.items() if c}


def monomial_sum(branches,powers,width):
    active=[(branch,e) for branch,e in zip(branches,powers) if e]
    if not active:return 1 << width,False
    intersection=qr.affine_space((eq for branch,e in active for eq in branch['equations']),width)
    if intersection is None:return 0,False
    origin,columns=intersection;phase=set()
    for branch,e in active:
        if e==2:continue
        local_origin=solve(branch['span'],origin^branch['origin'])
        local_columns=tuple(solve(branch['span'],v) for v in columns)
        assert local_origin is not None and all(v is not None for v in local_columns)
        phase ^= pd.substitute_boolean(branch['phase'],
                    qr.affine_forms(local_origin,local_columns,len(branch['columns'])))
    return lf.quadratic_value(phase,len(columns)),True


def absolute_mass(branches,width):
    if type(width) is not int or width<0:raise ValueError('nonnegative ambient width required')
    branches=tuple(branches);t=len(branches)
    if t>4:raise ValueError('at most four nonzero Gaussian branches required')
    if any(branch['width']!=width for branch in branches):raise ValueError('ambient widths differ')
    coefficients=absolute_coefficients(tuple(branch['amplitude'] for branch in branches))
    numerator=0;gaussian_sums=0
    for powers,c in coefficients.items():
        value,used=monomial_sum(branches,powers,width)
        numerator+=c*value;gaussian_sums+=used
    denominator=1 << t
    assert numerator>=0 and numerator%denominator==0
    value=numerator//denominator
    triangle=sum(branch['amplitude'] << len(branch['columns']) for branch in branches)
    assert value<=triangle
    return dict(value=value,branches=t,monomials=len(coefficients),gaussian_sums=gaussian_sums,
                expansion_budget=6**t,coefficient_denominator=denominator,
                coefficient_bits=max((abs(c).bit_length() for c in coefficients.values()),default=0),
                triangle_mass=triangle,boundary_rank=width)


def terminal_norm(source):
    blocks=[];bound=1
    for group,rows,block in zip(source['messages'],source['boundaries'],source['decomposition']['blocks']):
        branches=tuple(b for m in group if (b:=source_branch(m,rows)) is not None)
        norm=absolute_mass(branches,len(rows))
        assert norm['value']<=1 << len(block)
        blocks.append(norm);bound*=norm['value']
    return dict(bound=bound,blocks=tuple(blocks),
                gaussian_sums=sum(x['gaussian_sums'] for x in blocks),
                monomials=sum(x['monomials'] for x in blocks),
                expansion_budget=sum(x['expansion_budget'] for x in blocks))


def refine_tree(tree):
    previous=tree['bound'];pending=[tree];certificates=[]
    while pending:
        node=pending.pop();kind=node['kind']
        if kind=='push':pending.append(node['child'])
        elif kind=='product':pending.extend(node['children'])
        elif kind=='controls':
            norm=terminal_norm(node['source']);old=node['pair_envelope']
            assert len(norm['blocks'])==len(old['blocks'])
            assert all(a['value']<=b['bound'] for a,b in zip(norm['blocks'],old['blocks']))
            assert norm['bound']<=old['bound']
            norm['previous_pair_bound']=old['bound'];certificates.append(norm)
            node['gaussian_norm']=norm
            node['pair_envelope']=dict(old,bound=norm['bound'])
    bound=pe.propagate(tree)
    assert bound<=previous
    return dict(previous_bound=previous,bound=bound,certificates=certificates,
                gaussian_sums=sum(c['gaussian_sums'] for c in certificates),
                monomials=sum(c['monomials'] for c in certificates),
                expansion_budget=sum(c['expansion_budget'] for c in certificates))


def compile_sum(phase,width):
    tree,retained=pe.compile_sum(phase,width)
    return tree,dict(retained=retained,**refine_tree(tree))


def reduce_source(desc):
    result=pe.reduce_source(desc)
    result['gaussian_norm']=refine_tree(result['tree'])
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluate_source(result,bits):
    answer=pe.evaluate_source(result,bits)
    answer.update(norm_gaussian_sums=result['gaussian_norm']['gaussian_sums'],
                  norm_monomials=result['gaussian_norm']['monomials'])
    return answer
