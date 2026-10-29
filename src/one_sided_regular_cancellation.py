"""S173/R05-25: source-certified one-sided cancellation at arbitrary rank."""
from fractions import Fraction
import asymmetric_chain_characters as ac
from asymmetric_chain_characters import ch,lc,cc,qr,gb,gr,it,cb,pd,ds,solve,echelon,lf,Refusal,require


def local_pair(cert,j):
    o=cert['offsets'][j];k=cert['local'][j]['k']
    return {(1 << (o+1+i))|(1 << (o+1+k+i)) for i in range(k)}


def discover(desc):
    """Recover the source before selecting a cancellation-compatible split."""
    cert=ac.canonical_source(desc,rank_cap=desc[1]);n=desc[1]
    remainder=set(cert['remainder'])
    for j in range(len(cert['local'])):
        if cert['control_shifts'] >> j&1:remainder^=local_pair(cert,j)
    labels={};owners={}
    for c,component in enumerate(cert['components']):
        require(component['cycle'],'requires_regular_cycle')
        k=component['widths'][0]
        require(all(w==k for w in component['widths'])
                and all(len(echelon(H))==k for H in component['matrices']),'singular_cycle_edge')
        for j in component['vertices']:
            owners[j]=c;o=cert['offsets'][j]
            labels[o]=(c,j,'t')
            for i in range(k):
                labels[o+1+i]=(c,j,'u');labels[o+1+k+i]=(c,j,'v')
    # A scalar identity mixed block is removed as a control translation,
    # regardless of whether that translation reduces the total polar rank.
    shifts=0
    for j in range(len(cert['local'])):
        mixed={t for t in remainder if t.bit_count()==2
               and all(labels[i][1]==j for i in pd.bits(t))
               and {labels[i][2] for i in pd.bits(t)}=={'u','v'}}
        if mixed:
            require(mixed==local_pair(cert,j),'non_scalar_mixed_auxiliary_block')
            remainder^=mixed;shifts|=1 << j
    phases=[set() for _ in cert['components']];sides=[set() for _ in phases]
    for term in remainder:
        variables=list(pd.bits(term));aux=[i for i in variables if labels[i][2]!='t']
        if not aux:continue  # Shared-control-only phase cancels between copies.
        component=labels[aux[0]][0]
        require(all(labels[i][0]==component for i in variables),'cross_component_control_coupling')
        if len(aux)==2:
            kinds={labels[i][2] for i in aux}
            require(len(kinds)==1,'mixed_auxiliary_remainder')
            sides[component]|=kinds
        phases[component].add(term)
    components=[]
    for c,item in enumerate(cert['components']):
        require(len(sides[c])<=1,'two_sided_quadratic_remainder')
        components.append(dict(**item,remainder=phases[c],side=next(iter(sides[c]),'u'),
                               shifts=sum(((shifts >> u)&1) << j for j,u in enumerate(item['vertices']))))
    return dict(accepted=True,reason='one_sided_regular_cancellation',source=cert,components=components,
                remainder=remainder,control_shifts=shifts,rank=len(echelon(ac.polar(remainder,n))),
                gaussian_sums=len(components))


def conditional_phase(certificate,component,word):
    """Literal 4M-variable residual at a shifted control word."""
    cert=certificate['source'];widths=component['widths'];H=component['matrices']
    g=len(widths);M=sum(widths);offsets=[];at=0;phase=set()
    require(0<=word<(1 << g),'invalid_component_control_word')
    for k in widths:offsets.append(at);at+=k
    for j,k in enumerate(widths):
        o=offsets[j];nxt=offsets[(j+1)%g]
        for i in range(k):
            for c in range(2):
                for d in range(2):
                    if c!=d or not(word >> j&1):
                        phase^={(1 << (c*M+o+i))|(1 << ((2+d)*M+o+i))}
        for b,col in enumerate(H[j]):
            for a in pd.bits(col):
                for c in range(2):phase^={(1 << (c*M+o+a))|(1 << ((2+c)*M+nxt+b))}
    for copy in range(2):
        forms=[(0,0)]*cert['qubits']
        for j,u in enumerate(component['vertices']):
            o=cert['offsets'][u];a=offsets[j];k=widths[j]
            forms[o]=(0,((word^component['shifts']) >> j)&1)
            for i in range(k):
                forms[o+1+i]=(1 << (copy*M+a+i),0)
                forms[o+1+k+i]=(1 << ((2+copy)*M+a+i),0)
        phase^=pd.substitute_boolean(component['remainder'],forms)
    assert all(t.bit_count()<=2 for t in phase)
    return phase,4*M


def reduce_source(desc,rank_cap=4,state_cap=67):
    desc=cc.normalize_descriptor(desc)
    if type(rank_cap) is not int or rank_cap<0:raise ValueError('nonnegative fallback rank cap required')
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation cap required')
    try:certificate=discover(desc)
    except Refusal as exc:
        result=ac.reduce_source(desc,rank_cap,state_cap)
        result['one_sided']=dict(accepted=False,reason=str(exc))
        return result
    return dict(descriptor=desc,one_sided=certificate)


def reduce_native(n,gates,basis,output,rank_cap=4,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),rank_cap,state_cap)


def evaluate_source(result,bits,max_sums=None,max_terms=None,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    cert=result['one_sided']
    if not cert['accepted']:
        answer=ac.evaluate_source(result,bits,max_terms,max_work)
        return dict(answer,one_sided_refusal=cert['reason'])
    if max_sums is not None:
        if type(max_sums) is not int or max_sums<0:raise ValueError('nonnegative Gaussian budget required')
        if cert['gaussian_sums']>max_sums:
            return dict(mode='budget_refused',route='one_sided_regular',probability=None,
                        required_sums=cert['gaussian_sums'])
    E=Fraction((-1)**cert['source']['flip']);records=[];envelope=Fraction(1)
    for component in cert['components']:
        g=len(component['vertices']);M=sum(component['widths']);k=component['widths'][0]
        phase,width=conditional_phase(cert,component,(1 << g)-1)
        value=lf.quadratic_value(phase,width)
        assert value%(1 << (2*M))==0
        character=value//(1 << (2*M))
        factor=Fraction((-1)**(g+component['shifts'].bit_count())*(character-1),1 << (M+g))
        bound=Fraction((1 << (2*k))+1,1 << (M+g))
        assert abs(factor)<=bound
        E*=factor;envelope*=bound
        records.append(dict(controls=g,aux_width=M,exceptional_character=character,
                            expectation=factor,side=component['side'],shifts=component['shifts']))
    p=(1-E)/2;require(0<=p<=1,'original_acceptance_range')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(mode='exact',route='one_sided_regular',probability=p,rounded=rounded,
                error_bound=p-rounded,expectation=E,expectation_envelope=envelope,
                random_bits=0,failure_probability=0,gaussian_sums=len(records),
                rank=cert['rank'],avoided_fourier_terms=cert['source']['terms'],components=records)
