"""S173/R05-26: source output-displacement sums with Gaussian batching."""
from fractions import Fraction
import one_sided_regular_cancellation as oc
from one_sided_regular_cancellation import ac,cc,qr,pd,ds,echelon,solve,lf,Refusal,require


def derivative(poly,direction,n):
    return set(poly)^pd.substitute_boolean(set(poly),[(1 << j,(direction >> j)&1) for j in range(n)])


def discover(desc):
    require(len(desc[3])==2,'requires_two_phase_layers')
    _,n,J,phases,basis,output=desc;inverse=cc.inverse(J)
    delta=cc.action(inverse,1 << output);q=derivative(phases[1],delta,n)
    require(all(t.bit_count()<=2 for t in q),'nonquadratic_output_derivative')
    coupled=q^{(1 << j)|(1 << (n+j)) for j in range(n)}
    W=qr.quadratic_pushforward(coupled,tuple(1 << (n+j) for j in range(n)),2*n)
    require(not W['zero'],'empty_output_walsh_support')
    r=len(W['columns']);require(r%2==0 and W['exponent']==n-r//2,'output_walsh_rank')
    origin=cc.action(inverse,W['origin'])
    directions=tuple(cc.action(inverse,v) for v in W['columns'])
    require(len(echelon(directions))==r,'dependent_output_displacements')
    shifted_forms=qr.affine_forms(origin,directions,n)
    shifted_forms=[((1 << i)|(row << n),constant) for i,(row,constant) in enumerate(shifted_forms)]
    joint=set(phases[0])^pd.substitute_boolean(set(phases[0]),shifted_forms)^{1 << output}
    joint^={t << n for t in W['phase']}
    boundary=(1 << output)^cc.action(J,basis)
    joint^=pd.substitute_boolean({1 << i for i in pd.bits(boundary)},
                                [(row << n,c) for row,c in qr.affine_forms(origin,directions,n)])
    require(all(t.bit_count()<=3 for t in joint),'displacement_phase_degree')
    # Contract the first cubic tensor along the *actual* displacement support.
    T=pd.cubic_tensor(phases[0],n);pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    images=tuple(sum(((T[i][j]&v).bit_count()%2) << a for a,(i,j) in enumerate(pairs)) for v in directions)
    rows=tuple(sum(((v >> i)&1) << j for j,v in enumerate(images)) for i in range(len(pairs)))
    kernel=tuple(cc.nullspace(rows,r));selected=[];independent=[]
    for j,v in enumerate(images):
        if solve(echelon(independent),v) is None:independent.append(v);selected.append(1 << j)
    s=len(selected);change=tuple(selected)+kernel
    require(s+len(kernel)==r and len(echelon(change))==r,'invalid_displacement_kernel_split')
    forms=[(1 << i,0) for i in range(n)]
    forms.extend((row << n,c) for row,c in qr.affine_forms(0,change,r))
    batched=pd.substitute_boolean(joint,forms)
    control_mask=((1 << s)-1) << n
    require(all(t&control_mask for t in batched if t.bit_count()==3),'nonquadratic_displacement_fiber')
    return dict(accepted=True,reason='source_output_displacement',descriptor=desc,qubits=n,
                delta=delta,output_derivative=q,walsh=W,origin=origin,directions=directions,
                rank=r,active_rank=s,kernel=kernel,change=change,contraction_images=images,
                joint=joint,batched=batched,control_mask=control_mask,
                gaussian_width=n+r-s,gaussian_sums=1 << s,unbatched_sums=1 << r,
                normalizer_exponent=n+r//2)


def fiber(certificate,word):
    n=certificate['qubits'];s=certificate['active_rank']
    if type(word) is not int or not 0<=word<(1 << s):raise ValueError('valid displacement control required')
    low=(1 << n)-1;control=(1 << s)-1;phase=set()
    for term in certificate['batched']:
        pattern=(term >> n)&control
        if pattern&word!=pattern:continue
        reduced=(term&low)|((term >> (n+s)) << n)
        phase^={reduced}
    assert all(t.bit_count()<=2 for t in phase)
    return phase


def reduce_source(desc,rank_cap=4,state_cap=67):
    if type(rank_cap) is not int or rank_cap<0:raise ValueError('nonnegative retained rank cap required')
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive retained state cap required')
    desc=cc.normalize_descriptor(desc)
    try:certificate=discover(desc)
    except Refusal as exc:
        result=oc.reduce_source(desc,rank_cap,state_cap)
        result['displacement']=dict(accepted=False,reason=str(exc));return result
    return dict(descriptor=desc,displacement=certificate)


def reduce_native(n,gates,basis,output,rank_cap=4,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),rank_cap,state_cap)


def evaluate_source(result,bits,max_sums=None,max_terms=None,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    c=result['displacement']
    if not c['accepted']:
        answer=oc.evaluate_source(result,bits,max_sums,max_terms,max_work)
        return dict(answer,displacement_refusal=c['reason'])
    if max_sums is not None:
        if type(max_sums) is not int or max_sums<0:raise ValueError('nonnegative Gaussian cap required')
        if c['gaussian_sums']>max_sums:
            return dict(mode='budget_refused',route='output_displacement',probability=None,
                        required_sums=c['gaussian_sums'],rank=c['rank'],active_rank=c['active_rank'])
    total=sum(lf.quadratic_value(fiber(c,word),c['gaussian_width']) for word in range(c['gaussian_sums']))
    E=Fraction(total,1 << c['normalizer_exponent']);p=(1-E)/2
    require(0<=p<=1,'original_acceptance_range')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(mode='exact',route='output_displacement',probability=p,rounded=rounded,
                error_bound=p-rounded,expectation=E,random_bits=0,failure_probability=0,
                rank=c['rank'],active_rank=c['active_rank'],gaussian_sums=c['gaussian_sums'],
                unbatched_sums=c['unbatched_sums'],gaussian_width=c['gaussian_width'])
