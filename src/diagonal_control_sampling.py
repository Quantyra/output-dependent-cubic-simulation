"""S173/R05-18: source-certified diagonal-control Gaussian sampling."""
from fractions import Fraction
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import phase_defect_tensors as pd
import gaussian_mass_sampling as gs
from finite_field_descent import echelon


def translate(phase,vector,n):
    return pd.substitute_boolean(phase,[(1 << j,(vector >> j)&1) for j in range(n)])


def invariant_controls(desc):
    """All covectors whose computational characters commute with the readout."""
    _,n,J,phases,basis,output=desc
    delta=cc.action(cc.inverse(J),1 << output)
    phase=set(phases[1])^translate(set(phases[1]),delta,n)
    assert all(m.bit_count()<=2 for m in phase)
    polar=[0]*n
    for mask in phase:
        if mask.bit_count()==2:
            a,b=tuple(pd.bits(mask));polar[a]^=1 << b;polar[b]^=1 << a
    radical=tuple(cc.nullspace(polar,n))
    row=sum((cc.anf_evaluate(phase,v)^int(0 in phase)) << j for j,v in enumerate(radical))
    kernel=cc.nullspace([row],len(radical))
    translations=tuple(cc.action(radical,z) for z in kernel)
    controls=tuple(cc.action(J,v) for v in translations)
    assert len(echelon(controls))==len(controls)
    assert all(phase==translate(phase,v,n) for v in translations)
    return dict(phase=phase,delta=delta,radical=radical,translations=translations,controls=controls)


def shared_control_joint(desc,controls,phase):
    """Restrict ket and bra to the same control value, symbolically for every value."""
    n=desc[1];controls=tuple(controls);q=len(controls)
    assert len(echelon(controls))==q
    right=tuple(qr.affine_space([(c,int(i==j)) for i,c in enumerate(controls)],n)[0] for j in range(q))
    kernel=tuple(cc.nullspace(controls,n))
    columns=tuple(v|(v << (2*n)) for v in right)+kernel+tuple(1 << (n+j) for j in range(n))+tuple(v << (2*n) for v in kernel)
    assert len(columns)==3*n-q and len(echelon(columns))==len(columns)
    transformed=pd.substitute_boolean(phase,qr.affine_forms(0,columns,3*n))
    return dict(n=len(columns),control_rank=q,controls=controls,columns=columns,phase=transformed)


def discover(desc,phase):
    if len(desc[3])!=2:return dict(accepted=False,reason='requires_two_phase_layers')
    invariant=invariant_controls(desc)
    joint=shared_control_joint(desc,invariant['controls'],phase);q=joint['control_rank']
    witness=next((m for m in sorted(joint['phase']) if (m >> q).bit_count()>2),None)
    if witness is not None:
        return dict(accepted=False,reason='cubic_survives_invariant_conditioning',
                    invariant=invariant,joint=joint,witness=witness)
    return dict(accepted=True,reason='invariant_control_gaussian_fibers',invariant=invariant,
                joint=joint,control_rank=q,free_width=joint['n']-q,
                normalizer=1 << (2*desc[1]),branch_denominator=1 << (2*desc[1]-q),
                original_quadratic=all(m.bit_count()<=2 for m in phase))


def branch_sum(certificate,word):
    q=certificate['control_rank']
    if type(word) is not int or not 0<=word<(1 << q):raise ValueError('valid control assignment required')
    phase=cb.restricted_quadratic(certificate['joint'],word)
    value=lf.quadratic_value(phase,certificate['free_width'])
    assert abs(value)<=certificate['branch_denominator']
    return value


def reduce_source(desc):
    desc=cc.normalize_descriptor(desc);phase,width=qr.original_output_phase(desc)
    certificate=discover(desc,phase)
    if certificate['accepted']:
        return dict(descriptor=desc,phase=phase,physical_bits=width,diagonal_control=certificate)
    result=gs.reduce_source(desc);result['diagonal_control']=certificate
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluation_plan(result,bits,failure_bits,allow_envelope=True):
    if type(bits) is not int or bits<1 or type(failure_bits) is not int or failure_bits<1:
        raise ValueError('positive accuracy and confidence exponents required')
    certificate=result['diagonal_control']
    if not certificate['accepted']:
        plan=gs.evaluation_plan(result,bits,failure_bits,allow_envelope)
        return dict(plan,route='retained_mass_sampler',refusal=certificate['reason'])
    q=certificate['control_rank'];exact=certificate['original_quadratic']
    N=0 if exact else 2*(failure_bits+1)*(1 << (2*bits))
    return dict(mode='exact_gaussian' if exact else 'diagonal_gaussian',route='diagonal_control',
                bits=bits,failure_bits=failure_bits,epsilon=Fraction(1,1 << bits),
                samples=N,control_rank=q,random_bit_bound=N*q,
                gaussian_sum_bound=1 if exact else N,
                branch_denominator=certificate['branch_denominator'],
                failure_probability=Fraction(0) if exact else Fraction(1,1 << failure_bits))


def evaluate_source(result,bits,failure_bits,coins,allow_envelope=True,max_samples=None):
    plan=evaluation_plan(result,bits,failure_bits,allow_envelope)
    if plan['route']=='retained_mass_sampler':
        answer=gs.evaluate_source(result,bits,failure_bits,coins,allow_envelope,max_samples)
        answer.update(route='retained_mass_sampler',diagonal_refusal=plan['refusal'])
        return answer
    if max_samples is not None:
        if type(max_samples) is not int or max_samples<0:raise ValueError('nonnegative sample cap required')
        if plan['samples']>max_samples:
            return dict(mode='budget_refused',route='diagonal_control',estimate=None,probability=None,plan=plan,
                        stats=dict(gaussian_sums=0,random_bits=0,random_calls=0))
    certificate=result['diagonal_control'];q=certificate['control_rank'];den=certificate['branch_denominator']
    stats=dict(gaussian_sums=0,random_bits=0,random_calls=0);probability=None
    if plan['mode']=='exact_gaussian':
        den=certificate['normalizer']
        value=lf.quadratic_value(result['phase'],result['physical_bits']);stats['gaussian_sums']=1
        probability=Fraction(den-value,2*den);raw=probability;precision=bits
    else:
        total=0;N=plan['samples']
        for _ in range(N):
            word=gs.draw(coins,q,stats);total+=branch_sum(certificate,word);stats['gaussian_sums']+=1
        raw=Fraction(den*N-total,2*den*N);precision=bits+2
    assert 0<=raw<=1
    estimate=Fraction((raw.numerator << precision)//raw.denominator,1 << precision)
    error=probability-estimate if probability is not None else plan['epsilon']*Fraction(3,4)
    assert error<plan['epsilon'] and stats['random_bits']==plan['random_bit_bound']
    return dict(mode=plan['mode'],route='diagonal_control',estimate=estimate,probability=probability,
                error_bound=error,failure_probability=plan['failure_probability'],
                interval=(max(Fraction(0),estimate-error),min(Fraction(1),estimate+error)),plan=plan,stats=stats)
