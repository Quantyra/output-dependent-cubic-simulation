"""S173/R05-07: deterministic phase-span search for a clean cubic anchor.

All original phases are verified after field recovery. The anchor is a classical
linear combination, never an alteration of the native circuit being evaluated.
"""
from math import comb
import cubic_centroid_descent as cc
import field_defect_subspaces as ds
import phase_defect_tensors as pd
from finite_field_descent import echelon,solve,xor_sum


def source_tensor_basis(phases):
    positions=tuple(sorted({m for p in phases for m in p if m.bit_count()==3}))
    indices={m:i for i,m in enumerate(positions)}
    columns=[];source_indices=[];span={}
    for i,phase in enumerate(phases):
        packed=xor_sum(1 << indices[m] for m in phase if m.bit_count()==3)
        if solve(span,packed) is None:
            columns.append(packed);source_indices.append(i);span=echelon(columns)
    return dict(positions=positions,columns=tuple(columns),source_indices=tuple(source_indices))


def anchor_candidates(basis,prefix_dimension):
    columns=basis['columns'][:prefix_dimension]
    indices=basis['source_indices'][:prefix_dimension]
    previous=packed=source_mask=0
    for ordinal in range(1,1 << prefix_dimension):
        gray=ordinal^(ordinal >> 1);changed=(gray^previous).bit_length()-1
        packed ^= columns[changed];source_mask ^= 1 << indices[changed]
        assert packed
        anchor=tuple(basis['positions'][j] for j in pd.bits(packed))
        yield ordinal,source_mask,anchor
        previous=gray


def residual_tensor_dimension(phases,parts,rec):
    cubic_mask=sum(1 << j for j,m in enumerate(rec.masks) if m.bit_count()==3)
    field_columns={bit:rec.columns[j] for j,(e,bit) in enumerate(rec.specs) if e==(1,1,1)}
    residuals=[]
    for phase,part in zip(phases,parts):
        coefficient=part['field_poly'].get((1,1,1),0)
        compatible=xor_sum(field_columns[j] for j in pd.bits(coefficient))
        residuals.append((pd.packed_anf(phase,rec)^compatible)&cubic_mask)
    return len(echelon(residuals))


def verify_original_source(desc,field,rank_limit,span_limit,details):
    _,n,J,phases,basis,output=desc
    if len(phases)>1:
        correction,reason=ds.recover_subspace(field,J,rank_limit)
        if correction is None:return None,reason
    else:
        correction=dict(rank=0,columns=(),form=(),balanced_matrix=None,
                        pairing=None,method='unused_one_layer')
    rec=cc.PhaseReconstructor(field);parts=[];combined=tuple(correction['columns'])
    for phase in phases:
        part,reason=pd.recover_phase(phase,field,rec,rank_limit)
        if part is None:return None,reason
        parts.append(part);combined=ds.image_basis(combined+part['columns'])
        if len(combined)>rank_limit:return None,'global_rank_budget'
    dimension=residual_tensor_dimension(phases,parts,rec)
    if dimension>span_limit:return None,'residual_tensor_span_budget'
    details['observed_defect_span_dimension']=dimension
    return pd.construct_output(desc,field,correction,parts,details,rank_limit)


def discover_source(desc,rank_limit,h,rng,defect_span_limit=None):
    desc=cc.normalize_descriptor(desc);_,n,J,phases,basis,output=desc
    if (n<3 or n%3 or type(rank_limit) is not int or not 0<=rank_limit<=n
        or type(h) is not int or h<1
        or (defect_span_limit is not None
            and (type(defect_span_limit) is not int or defect_span_limit<0))):
        return None,dict(reason='invalid_parameters',random_bits=0)
    tensor_basis=source_tensor_basis(phases);dimension=len(tensor_basis['columns'])
    span_limit=min(dimension,comb(rank_limit,3) if defect_span_limit is None else defect_span_limit)
    prefix=min(dimension,span_limit+1);limit=(1 << prefix)-1
    s=n//3;rejected={};centroids=trials=scanned=0
    common=dict(tensor_span_dimension=dimension,defect_span_budget=span_limit,
                prefix_dimension=prefix,candidate_limit=limit,
                field_size_guarantee=s>=7*rank_limit+5)
    for ordinal,mask,anchor in anchor_candidates(tensor_basis,prefix):
        scanned+=1;centroid=cc.centroid(n,anchor)
        if len(centroid)!=s:
            reason='anchor_centroid_dimension'
            rejected[reason]=rejected.get(reason,0)+1
            continue
        flat=[cc.flatten(t) for t in centroid];span=echelon(flat)
        if solve(span,cc.flatten(cc.identity(n))) is None:
            reason='anchor_missing_identity'
            rejected[reason]=rejected.get(reason,0)+1
            continue
        centroids+=1
        for attempt in range(1,3*h+1):
            trials+=1;tape=rng.getrandbits(s)
            field=ds.certify_generator(n,centroid,flat,span,tape,attempt)
            reason='not_field_generator'
            if field is not None:
                details=dict(common,reason='ok',anchor_mask=mask,anchor_ordinal=ordinal,
                             candidates_scanned=scanned,centroid_candidates=centroids,
                             anchor_trials=attempt,total_trials=trials,random_bits=s*trials,
                             rejected=dict(rejected))
                result,reason=verify_original_source(desc,field,rank_limit,span_limit,details)
                if result is not None:return result,details
            rejected[reason]=rejected.get(reason,0)+1
    return None,dict(common,reason='bounded_anchor_span_failure',candidates_scanned=scanned,
                     centroid_candidates=centroids,total_trials=trials,
                     random_bits=s*trials,rejected=rejected)


def reduce_native(n,gates,basis,output,rank_limit,h,rng,defect_span_limit=None):
    return discover_source(cc.recognize_native(n,gates,basis,output),rank_limit,h,rng,defect_span_limit)
