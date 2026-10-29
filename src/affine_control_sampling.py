"""S173/R05-19: source-derived affine sector matching and Gaussian readout."""
from fractions import Fraction
import cubic_centroid_descent as cc
import cubic_centroid_controls as cb
import cubic_linear_factors as lf
import quadratic_pushforward_recursion as qr
import diagonal_control_sampling as dc
import gaussian_mass_sampling as gs


def signature(rows,word):
    return sum(((r&word).bit_count()%2) << j for j,r in enumerate(rows))


def matching_controls(desc):
    invariant=dc.invariant_controls(desc)
    radical=invariant['radical'];Q=invariant['phase'];n=desc[1]
    controls=tuple(cc.action(desc[2],v) for v in radical)
    eta=sum((cc.anf_evaluate(Q,v)^int(0 in Q)) << j for j,v in enumerate(radical))
    for j,v in enumerate(radical):
        assert Q^dc.translate(Q,v,n)==({0} if (eta >> j)&1 else set())
    offset=qr.affine_space([(c,(eta >> j)&1) for j,c in enumerate(controls)],n)[0]
    assert signature(controls,offset)==eta
    # delta is invariant under Q; the matched offset cannot flip the output character.
    assert not ((offset >> desc[5])&1)
    return dict(invariant=invariant,controls=controls,eta=eta,offset=offset)


def discover(desc,phase):
    if len(desc[3])!=2:return dict(accepted=False,reason='requires_two_phase_layers')
    matching=matching_controls(desc);q=len(matching['controls']);n=desc[1]
    shifted=dc.translate(phase,matching['offset'] << (2*n),3*n)
    joint=dc.shared_control_joint(desc,matching['controls'],shifted)
    witness=next((m for m in sorted(joint['phase']) if (m >> q).bit_count()>2),None)
    if witness is not None:
        return dict(accepted=False,reason='cubic_survives_affine_matching',
                    matching=matching,joint=joint,witness=witness)
    eta=matching['eta'];pivot=(eta&-eta).bit_length()-1 if eta else None
    return dict(accepted=True,reason='affine_matched_gaussian_fibers',matching=matching,
                joint=joint,control_rank=q,free_width=joint['n']-q,
                orbit_pivot=pivot,random_width=q-int(bool(eta)),
                normalizer=1 << (2*n),branch_denominator=1 << (2*n-q),
                original_quadratic=all(m.bit_count()<=2 for m in phase))


def orbit_representative(certificate,word):
    r=certificate['random_width']
    if type(word) is not int or not 0<=word<(1 << r):
        raise ValueError('valid orbit assignment required')
    pivot=certificate['orbit_pivot']
    if pivot is None:return word
    low=(1 << pivot)-1
    return (word&low)|((word&~low) << 1)


def branch_sum(certificate,word):
    return dc.branch_sum(certificate,word)


def reduce_source(desc):
    desc=cc.normalize_descriptor(desc);phase,width=qr.original_output_phase(desc)
    certificate=discover(desc,phase)
    if certificate['accepted']:
        return dict(descriptor=desc,phase=phase,physical_bits=width,affine_control=certificate)
    result=dc.reduce_source(desc);result['affine_control']=certificate
    return result


def reduce_native(n,gates,basis,output):
    return reduce_source(cc.recognize_native(n,gates,basis,output))


def evaluation_plan(result,bits,failure_bits,allow_envelope=True):
    if type(bits) is not int or bits<1 or type(failure_bits) is not int or failure_bits<1:
        raise ValueError('positive accuracy and confidence exponents required')
    certificate=result['affine_control']
    if not certificate['accepted']:
        plan=dc.evaluation_plan(result,bits,failure_bits,allow_envelope)
        return dict(plan,route='retained_reader',affine_refusal=certificate['reason'])
    q=certificate['control_rank'];exact=certificate['original_quadratic']
    N=0 if exact else 2*(failure_bits+1)*(1 << (2*bits))
    return dict(mode='exact_gaussian' if exact else 'affine_gaussian',route='affine_control',
                bits=bits,failure_bits=failure_bits,epsilon=Fraction(1,1 << bits),
                samples=N,control_rank=q,random_width=certificate['random_width'],
                random_bit_bound=N*certificate['random_width'],
                gaussian_sum_bound=1 if exact else N,
                branch_denominator=certificate['branch_denominator'],
                failure_probability=Fraction(0) if exact else Fraction(1,1 << failure_bits))


def evaluate_source(result,bits,failure_bits,coins,allow_envelope=True,max_samples=None):
    plan=evaluation_plan(result,bits,failure_bits,allow_envelope)
    if plan['route']=='retained_reader':
        answer=dc.evaluate_source(result,bits,failure_bits,coins,allow_envelope,max_samples)
        answer['affine_refusal']=plan['affine_refusal']
        return answer
    if max_samples is not None:
        if type(max_samples) is not int or max_samples<0:raise ValueError('nonnegative sample cap required')
        if plan['samples']>max_samples:
            return dict(mode='budget_refused',route='affine_control',estimate=None,probability=None,plan=plan,
                        stats=dict(gaussian_sums=0,random_bits=0,random_calls=0))
    certificate=result['affine_control'];den=certificate['branch_denominator']
    stats=dict(gaussian_sums=0,random_bits=0,random_calls=0);probability=None
    if plan['mode']=='exact_gaussian':
        den=certificate['normalizer']
        value=lf.quadratic_value(result['phase'],result['physical_bits']);stats['gaussian_sums']=1
        probability=Fraction(den-value,2*den);raw=probability;precision=bits
    else:
        total=0;N=plan['samples']
        for _ in range(N):
            word=orbit_representative(certificate,gs.draw(coins,certificate['random_width'],stats))
            total+=branch_sum(certificate,word);stats['gaussian_sums']+=1
        raw=Fraction(den*N-total,2*den*N);precision=bits+2
    assert 0<=raw<=1
    estimate=Fraction((raw.numerator << precision)//raw.denominator,1 << precision)
    error=probability-estimate if probability is not None else plan['epsilon']*Fraction(3,4)
    assert error<plan['epsilon'] and stats['random_bits']==plan['random_bit_bound']
    return dict(mode=plan['mode'],route='affine_control',estimate=estimate,probability=probability,
                error_bound=error,failure_probability=plan['failure_probability'],
                interval=(max(Fraction(0),estimate-error),min(Fraction(1),estimate+error)),plan=plan,stats=stats)
