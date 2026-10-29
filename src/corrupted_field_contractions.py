"""S173/R05-08: recover hidden fields from corrupted cubic contractions.

The alternative small-cubic-image branch needs no field and uses exact binary
quadratic sums. Finite-field point counting remains an external backend.
"""
from fractions import Fraction
from itertools import combinations
from types import SimpleNamespace
import cubic_centroid_descent as cc
import phase_defect_tensors as pd
import phase_combination_anchors as pa
import field_defect_subspaces as ds
from finite_field_descent import echelon,solve,xor_sum
from magic_residual_counts import quadratic_sum


def contraction(tensor,v):
    n=len(tensor)
    return tuple(sum(((tensor[i][j]&v).bit_count()&1) << i for i in range(n))
                 for j in range(n))


def common_balance(forms):
    n=len(forms[0])
    rows=((B[j] << (n*i))^(B[i] << (n*j))
          for B in forms for i in range(n) for j in range(i+1,n))
    return tuple(cc.unflatten(t,n) for t in cc.nullspace(rows,n*n))


def small_cubic_image(desc,rank_limit):
    """Discover all cubic support directly; verify full phase lifts."""
    _,n,J,phases,basis,output=desc
    U=ds.image_basis(row for phase in phases for rows in pd.cubic_tensor(phase,n) for row in rows)
    if len(U)>rank_limit:return None,'large_original_cubic_image'
    masks=[sum(1 << i for i in indices) for d in range(4) for indices in combinations(range(n),d)]
    rec=SimpleNamespace(masks=masks,positions={m:i for i,m in enumerate(masks)})
    cubic_mask=sum(1 << j for j,m in enumerate(masks) if m.bit_count()==3)
    specs,columns=pd.selector_columns(U,rec,3)
    span=echelon([c&cubic_mask for c in columns]);parts=[]
    for phase in phases:
        packed=pd.packed_anf(phase,rec)
        coefficients=solve(span,packed&cubic_mask)
        if coefficients is None:return None,'cubic_image_lift_failure'
        remainder=packed^xor_sum(c for j,c in enumerate(columns) if coefficients >> j & 1)
        if remainder&cubic_mask:return None,'cubic_image_remainder_failure'
        residual={m for j,m in enumerate(specs) if coefficients >> j & 1}
        quad={m for j,m in enumerate(masks) if remainder >> j & 1}
        assert set(phase)==quad^pd.substitute_boolean(residual,[(u,0) for u in U])
        parts.append(dict(quadratic=quad,residual=residual))
    L=len(phases);k=2*L-1;r=len(U);shift=cc.action(cc.inverse(J),1 << output)
    ket=[[(1 << (v*n+j),0) for j in range(n)] for v in range(L)]
    bra=[[(1 << ((L+v)*n+j),0) for j in range(n)] for v in range(L-1)]
    bra.append([(mask,(shift >> j)&1) for j,(mask,_) in enumerate(ket[-1])])
    Q=set()
    for part,x,y in zip(parts,ket,bra):
        Q ^= pd.substitute_boolean(part['quadratic'],x)
        Q ^= pd.substitute_boolean(part['quadratic'],y)
    linear={1 << j for j in pd.bits(cc.action(J,basis))}
    Q ^= pd.substitute_boolean(linear,ket[0])
    Q ^= pd.substitute_boolean(linear,bra[0])
    for word in (ket,bra):
        for x,y in zip(word,word[1:]):
            for j,col in enumerate(J):
                for i in pd.bits(col):Q ^= pd.affine_product((x[i],y[j]))
    G=set();delta=sum(((u&shift).bit_count()&1) << i for i,u in enumerate(U))
    for v,part in enumerate(parts):
        x=[(1 << (v*r+i),0) for i in range(r)]
        block=L+v if v<L-1 else L-1
        y=[(1 << (block*r+i),0 if v<L-1 else (delta >> i)&1) for i in range(r)]
        G ^= pd.substitute_boolean(part['residual'],x)
        G ^= pd.substitute_boolean(part['residual'],y)
    degree=max((m.bit_count() for m in G),default=0)
    return dict(method='small_cubic_image',descriptor=desc,phase_parts=parts,
                columns=U,residual_rank=r,k=k,physical_bits=k*n,quadratic=Q,
                selector=G,selector_bits=k*r,active_bits=tuple(pd.bits(pd.xor_or(G))),
                residual_degree=degree,rank_budget=rank_limit),'ok'


def quadratic_branches(result):
    """Signed Gaussian sums, including all inactive physical variables."""
    n=result['descriptor'][1];r=result['residual_rank'];Q=result['quadratic']
    c=int(0 in Q);linear={m.bit_length()-1 for m in Q if m.bit_count()==1}
    pairs={tuple(pd.bits(m)) for m in Q if m.bit_count()==2}
    for z,w in pd.spectrum(result):
        added=xor_sum(u << (v*n) for v in range(result['k'])
                      for i,u in enumerate(result['columns']) if z >> (v*r+i)&1)
        value=quadratic_sum(c,linear^set(pd.bits(added)),pairs,result['physical_bits'])
        yield z,w,value


def evaluate_small_image(result,bits):
    if type(bits) is not int or bits<1:raise ValueError('positive precision required')
    total=0;branches=0
    for z,w,value in quadratic_branches(result):total+=w*value;branches+=1
    scale=1 << result['selector_bits']
    signed,remainder=divmod(total,scale)
    if remainder:raise AssertionError('nonintegral original signed sum')
    _,n,J,phases,basis,output=result['descriptor'];denominator=1 << (n*len(phases))
    p=Fraction(denominator-signed,2*denominator)
    if not 0<=p<=1:raise AssertionError('invalid original probability')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(probability=p,rounded=rounded,signed=signed,branches=branches)


def discover_source(desc,rank_limit,h,rng):
    desc=cc.normalize_descriptor(desc);_,n,J,phases,basis,output=desc
    if (type(rank_limit) is not int or not 0<=rank_limit<=n or type(h) is not int or h<1):
        return None,dict(reason='invalid_parameters',random_bits=0)
    direct,reason=small_cubic_image(desc,rank_limit)
    if direct is not None:
        details=dict(reason='ok',method='small_cubic_image',random_bits=0,total_trials=0)
        direct['discovery']=details
        return direct,details
    if n<3 or n%3:return None,dict(reason='unsupported_field_dimension',random_bits=0)
    s=n//3;limit=8*(1 << (4*rank_limit))*h
    seen=set();rejected={};trials=0
    common=dict(method='four_contractions',trials_per_phase=limit,
                max_total_trials=len(phases)*limit,
                field_size_guarantee=s>=7*rank_limit+5)
    for phase_index,phase in enumerate(phases):
        cubic=tuple(m for m in phase if m.bit_count()==3)
        if not cubic or cubic in seen:continue
        seen.add(cubic);tensor=pd.cubic_tensor(cubic,n)
        for attempt in range(1,limit+1):
            trials+=1
            vectors=[rng.getrandbits(n) for _ in range(4)]
            scalar=rng.getrandbits(s)
            balances=common_balance([contraction(tensor,v) for v in vectors])
            reason='balance_dimension'
            if len(balances)==s:
                flat=[cc.flatten(T) for T in balances];span=echelon(flat)
                reason='balance_missing_identity'
                if solve(span,cc.flatten(cc.identity(n))) is not None:
                    field=ds.certify_generator(n,balances,flat,span,scalar,attempt)
                    reason='not_field_generator'
                    if field is not None:
                        details=dict(common,reason='ok',phase_index=phase_index,
                                     phase_trials=attempt,total_trials=trials,
                                     random_bits=(4*n+s)*trials,rejected=dict(rejected))
                        result,reason=pa.verify_original_source(desc,field,rank_limit,len(phases),details)
                        if result is not None:
                            result['method']='four_contractions'
                            return result,details
            rejected[reason]=rejected.get(reason,0)+1
    return None,dict(common,reason='bounded_contraction_failure',total_trials=trials,
                     random_bits=(4*n+s)*trials,rejected=rejected)


def reduce_native(n,gates,basis,output,rank_limit,h,rng):
    return discover_source(cc.recognize_native(n,gates,basis,output),rank_limit,h,rng)
