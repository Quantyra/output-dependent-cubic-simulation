"""S173/R05-24: unequal-copy characters via affine-chain memory reset."""
from fractions import Fraction
from functools import lru_cache
import linear_chain_characters as ch
from linear_chain_characters import lc,cc,qr,gb,gr,it,cb,pd,ds,solve,echelon,Refusal,require
import cubic_linear_factors as lf


def copy_action(value,selected,width=1):
    mask=(1 << width)-1;x=value&mask;y=value >> width
    return (x^y)|((x^y) << width) if selected else y|(x << width)


def chain_data(record,zeros,stop=None):
    start,forces,phases=record;ell=len(forces)
    if stop is None:stop=ell
    F=(1,2);c=0;linear=0;constant=0
    for i in range(stop):
        linear^=it.signature(F,phases[i]);constant^=(phases[i]&c).bit_count()%2
        selected=start+i in zeros
        F=tuple(copy_action(v,selected) for v in F)
        c=copy_action(c,selected)^forces[i]
    value=sum((-1)**(((linear&x).bit_count()%2)^constant)
              for x in range(4) if cc.action(F,x)==c)
    return dict(value=value,constant=constant,linear=linear,final=c,matrix=F)


def forced_state(record,at,r,p):
    """State before at, with zero initial state; older controls are erased."""
    start,forces,phases=record
    begin=r if r>=start else start;value=0
    for j in range(begin,at):
        value=copy_action(value,j in (r,p))^forces[j-start]
    return value


def regular_direct(regular,S):
    """Independent polynomial affine Gaussian solve, used for empty/singletons."""
    widths=regular['widths'];g=len(widths);M=sum(widths);Q=set()
    H=regular['matrices'];A=regular['forces'];B=regular['phases']
    k=widths[0] if widths else 0
    for j in range(g):
        for a in range(k):
            for c in range(2):
                for d in range(2):
                    if c!=d or S >> j&1:
                        Q^={(1 << (c*M+j*k+a))|(1 << ((2+d)*M+j*k+a))}
                if A[j] >> (c*k+a)&1:Q^={1 << (c*M+j*k+a)}
                if B[j] >> (c*k+a)&1:Q^={1 << ((2+c)*M+j*k+a)}
        for b,column in enumerate(H[j]):
            for a in pd.bits(column):
                for c in range(2):
                    Q^={(1 << (c*M+j*k+a))|(1 << ((2+c)*M+((j+1)%g)*k+b))}
    value=lf.quadratic_value(Q,4*M);assert value%(1 << (2*M))==0
    return value//(1 << (2*M))


def regular_gap(regular,r,p,q):
    """Unique regular affine state after two selected controls; signed phase."""
    g=len(regular['widths']);k=regular['widths'][0];mask=(1 << k)-1;value=0;phase=0
    for j in range(r,q):
        v=copy_action(value,j in (r,p),k)^regular['forces'][j%g]
        inverse=regular['inverses'][j%g]
        value=cc.action(inverse,v&mask)|(cc.action(inverse,v >> k) << k)
        if j+1>p:phase^=(regular['phases'][(j+1)%g]&value).bit_count()%2
    return phase


def aggregate(g,strings,regular,control_mask):
    """All shared-control characters, with polynomial cyclic-triple discovery."""
    strings=tuple(strings);M=sum(len(a) for s,a,b in strings)+sum(regular['widths'])
    if not 0<=control_mask<(1 << g):raise ValueError('valid control character required')
    def full(S):
        value=regular_direct(regular,S)
        for record in strings:
            start,forces,phases=record
            zeros={start+i for i in range(len(forces)) if S >> ((start+i)%g)&1}
            value*=chain_data(record,zeros)['value']
        return (-1)**((S&control_mask).bit_count()%2)*value
    total=full(0)+sum(full(1 << j) for j in range(g))
    stats=dict(first_pairs=0,selection_transitions=0,triple_weights=0,zero_weights=0,
               peak_states=0,peak_integer_bits=abs(total).bit_length(),regular_direct_sums=g+1)
    @lru_cache(None)
    def weight(r,p,q):
        assert 0<=q<g and q-g<=r<p<q
        stats['triple_weights']+=1;exponent=0;signbit=(control_mask >> q)&1
        signbit^=regular_gap(regular,r,p,q)
        for record in strings:
            start,forces,phases=record;ell=len(forces);end=start+ell-1
            # Phase at a site is measured before its local copy matrix acts.
            for i,B in enumerate(phases):
                at=start+i;local=p+1+(at-p-1)%g
                if local<=q:
                    shift=at-local
                    c=forced_state(record,at,r+shift,p+shift)
                    signbit^=(B&c).bit_count()%2
            # Endpoint is after its final control; its event belongs to [p,q).
            local=p+(end-p)%g
            if local<q:
                shift=end-local;rr=r+shift;pp=p+shift
                if rr>=start:
                    if forced_state(record,end+1,rr,pp)!=0:return None
                    exponent+=2
                else:
                    zeros={pp} if pp>=start else set()
                    data=chain_data(record,zeros);factor=data['value']*((-1)**data['constant'])
                    if not factor:return None
                    exponent+=abs(factor).bit_length()-1
                    if factor<0:signbit^=1
            # Character of initial state stops immediately after the second zero.
            at=start+(q-start)%g;shift=at-q;rr=r+shift;pp=p+shift
            if rr<start<=pp and at<=end:
                data=chain_data(record,{pp,at},stop=at-start+1)
                if data['linear']:return None
        return exponent,(-1)**signbit
    def transition(r,p,q):
        shift=(q//g)*g
        return weight(r-shift,p-shift,q-shift)
    for a in range(g):
        for b in range(a+1,g):
            states={(a,b):1};stats['first_pairs']+=1
            for q in range(b+1,g):
                following=dict(states)
                for (r,p),value in states.items():
                    w=transition(r,p,q);stats['selection_transitions']+=1
                    if w is None:stats['zero_weights']+=1;continue
                    following[p,q]=following.get((p,q),0)+w[1]*(value << w[0])
                states={key:value for key,value in following.items() if value}
                stats['peak_states']=max(stats['peak_states'],len(states))
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],
                    max((abs(v).bit_length() for v in states.values()),default=0))
            for (r,p),value in states.items():
                w1=transition(r,p,a+g);w2=transition(p,a+g,b+g)
                if w1 is not None and w2 is not None:
                    total+=w1[1]*w2[1]*(value << (w1[0]+w2[0]))
                stats['peak_integer_bits']=max(stats['peak_integer_bits'],abs(total).bit_length())
    assert stats['peak_integer_bits']<=2*M+g+3
    return (-1)**control_mask.bit_count()*total,stats


def cycle_character(matrices,widths,forces,phases,control_mask=None,basis=None):
    """Forces/phases are pairs of per-vertex field arrays, one per copy."""
    g=len(widths);M=sum(widths)
    if control_mask is None:control_mask=(1 << g)-1
    for pair in (forces,phases):
        if len(pair)!=2:raise ValueError('two copies required')
        for fs in pair:
            if len(fs)!=g or any(v<0 or v.bit_length()>k for v,k in zip(fs,widths)):
                raise ValueError('valid vertex fields required')
    if basis is None:basis=ch.graded_basis(matrices,widths)
    offsets=basis['offsets']
    # Reorder the regular basis by its actual output grade.
    by_grade=[]
    for j,k in enumerate(widths):
        mask=((1 << k)-1) << offsets[j]
        by_grade.append(tuple(v for v in basis['regular_columns'] if v&mask))
    regular_columns=tuple(v for group in by_grade for v in group);r=len(by_grade[0])
    assert all(len(group)==r for group in by_grade)
    nil_columns=tuple(v for s in basis['strings'] for v in s['columns'])
    columns=nil_columns+regular_columns;span=echelon(columns)
    aa=[];bb=[]
    for copy in range(2):
        packed_a=sum(v << o for v,o in zip(forces[copy],offsets))
        packed_b=sum(v << o for v,o in zip(phases[copy],offsets))
        aa.append(solve(span,packed_a));bb.append(it.signature(columns,packed_b))
        assert aa[-1] is not None
    strings=[];at=0
    for s in basis['strings']:
        ell=s['length']
        A=tuple(((aa[0] >> (at+i))&1)|(((aa[1] >> (at+i))&1) << 1) for i in range(ell))
        B=tuple(((bb[0] >> (at+i))&1)|(((bb[1] >> (at+i))&1) << 1) for i in range(ell))
        strings.append((s['start'],A,B));at+=ell
    RH=[]
    for j in range(g):
        target=echelon(by_grade[j])
        H=tuple(solve(target,cc.action(basis['shift'],v)) for v in by_grade[(j+1)%g])
        assert all(v is not None for v in H) and len(echelon(H))==r
        RH.append(H)
    mask=(1 << r)-1
    A=[((aa[0] >> (at+j*r))&mask)|(((aa[1] >> (at+j*r))&mask) << r) for j in range(g)]
    B=[((bb[0] >> (at+j*r))&mask)|(((bb[1] >> (at+j*r))&mask) << r) for j in range(g)]
    regular=dict(widths=[r]*g,matrices=RH,inverses=[cc.inverse(H) for H in RH],forces=A,phases=B)
    value,stats=aggregate(g,strings,regular,control_mask)
    return dict(value=value << (2*M),normalized_value=Fraction(value,1 << (M+g)),
                basis=basis,strings=strings,regular=regular,stats=stats)


def polar(poly,width):
    result=[0]*width
    for term in poly:
        if term.bit_count()==2:
            i,j=tuple(pd.bits(term));result[i]^=1 << j;result[j]^=1 << i
    return tuple(result)


def hyperbolic_frame(poly,width,prescribed_u=(),prescribed_v=()):
    """Complete two disjoint singular subspaces to complementary hyperbolic halves."""
    require(width%2==0 and 0 not in poly and all(t.bit_count()<=2 for t in poly),'invalid_quadratic_refinement')
    Omega=polar(poly,width);require(len(echelon(Omega))==width,'degenerate_auxiliary_form')
    def pairing(x,y):return (x&cc.action(Omega,y)).bit_count()%2
    def value(x):return cc.anf_evaluate(poly,x)
    A=list(ds.image_basis(prescribed_u));B=list(ds.image_basis(prescribed_v))
    require(len(echelon(A+B))==len(A)+len(B),'intersecting_endpoint_subspaces')
    for group in (A,B):
        require(all(value(v)==0 for v in group) and all(not pairing(x,y) for x in group for y in group),
                'nonsingular_endpoint_subspace')
    X=[];Y=[]
    while True:
        pair=next(((a,b) for a in A for b in B if pairing(a,b)),None)
        if pair is None:break
        a,b=pair;X.append(a);Y.append(b)
        def project(v):return v^(a if pairing(v,b) else 0)^(b if pairing(v,a) else 0)
        A=list(ds.image_basis(project(v) for v in A))
        B=list(ds.image_basis(project(v) for v in B))
    pending=[(v,0) for v in A]+[(v,1) for v in B]
    while pending:
        x,side=pending.pop(0)
        equations=[(cc.action(Omega,x),1)]
        equations += [(cc.action(Omega,v),0) for v in X+Y+[v for v,s in pending]]
        solution=qr.affine_space(equations,width);require(solution is not None,'singular_flag_completion')
        y=solution[0]
        if value(y):y^=x
        if side:X.append(y);Y.append(x)
        else:X.append(x);Y.append(y)
    while len(X)<width//2:
        W=cc.nullspace([cc.action(Omega,v) for v in X+Y],width)
        x=next((v for v in W if value(v)==0),None)
        if x is None:
            pair=next(((a,b) for i,a in enumerate(W) for b in W[i+1:] if not pairing(a,b)),None)
            if pair is not None:x=pair[0]^pair[1]
            elif len(W)>=3:x=W[0]^W[1]^W[2]
            else:raise Refusal('anisotropic_auxiliary_form')
        require(x!=0 and value(x)==0,'missing_singular_vector')
        solution=qr.affine_space([(cc.action(Omega,x),1)]+[(cc.action(Omega,v),0) for v in X+Y],width)
        require(solution is not None,'hyperbolic_partner')
        y=solution[0]
        if value(y):y^=x
        X.append(x);Y.append(y)
    frame=tuple(X+Y);k=width//2
    require(len(echelon(frame))==width,'dependent_hyperbolic_frame')
    expected={(1 << i)|(1 << (k+i)) for i in range(k)}
    require(pd.substitute_boolean(poly,qr.affine_forms(0,frame,width))==expected,'quadratic_refinement_mismatch')
    require(all(solve(echelon(X),v) is not None for v in prescribed_u)
            and all(solve(echelon(Y),v) is not None for v in prescribed_v),'endpoint_flag_mismatch')
    return frame


def canonical_source(desc,rank_cap=4):
    """Recover a full physical coordinate map and a verified quadratic remainder."""
    require(len(desc[3])==2,'requires_two_phase_layers')
    n=desc[1];phase1=set(desc[3][1]);phase1.discard(0)
    require(len(echelon(row for rows in pd.cubic_tensor(phase1,n) for row in rows))==n,'incomplete_cubic_mode')
    decomposition=gb.primitive_blocks(phase1,n);blocks=decomposition['blocks']
    P,S=lc.physical_copy_actions(desc);Pc=tuple(v >> (2*n) for v in P[2*n:])
    controls=lc.dc.invariant_controls(desc)['controls']
    initial=[];local=[];offsets=[];offset=0
    for block in blocks:
        w=len(block);require(w>=3 and w%2==1,'not_an_original_star')
        C=ds.image_basis(it.signature(block,c) for c in controls)
        require(len(C)==1,'not_one_original_control');c=C[0]
        projection=lc.restrict_action(Pc,block);heads=ds.image_basis(projection)
        require(len(heads)==1 and (c&heads[0]).bit_count()%2==1,'control_projection_mismatch')
        h=heads[0];K=tuple(cc.nullspace([c],w))
        require(all(cc.action(projection,v)==0 for v in K),'control_kernel_mismatch')
        f=pd.substitute_boolean(phase1,qr.affine_forms(0,block,n))
        require(not pd.substitute_boolean(f,qr.affine_forms(0,K,w)),'nonzero_zero_control_phase')
        q=pd.substitute_boolean(f,qr.affine_forms(h,K,w));flip=int(0 in q);q.discard(0)
        require(all(t.bit_count()<=2 for t in q),'nonquadratic_control_fiber')
        Omega=polar(q,w-1);require(len(echelon(Omega))==w-1,'degenerate_control_fiber')
        columns=tuple(cc.action(block,v) for v in (h,)+K)
        initial.extend(columns);offsets.append(offset);offset+=w
        local.append(dict(width=w,k=(w-1)//2,h=h,K=K,phase=q,flip=flip,polar=Omega,block=block))
    initial=tuple(initial)
    forms=qr.affine_forms(0,initial,n)
    first=pd.substitute_boolean(set(desc[3][0]),forms)
    last=pd.substitute_boolean(phase1,forms)
    expected=set()
    for o,item in zip(offsets,local):
        expected^={(1 << o)|(t << (o+1)) for t in item['phase']}
        if item['flip']:expected^={1 << o}
    require(last==expected,'last_phase_block_mismatch')
    difference=first^last;require(all(t.bit_count()<=2 for t in difference),'cubic_layer_mismatch')
    labels=[(j,i) for j,item in enumerate(local) for i in range(item['width'])]
    edges={}
    for t in difference:
        if t.bit_count()!=2:continue
        (a,i),(b,j)=[labels[v] for v in pd.bits(t)]
        if a==b or i==0 or j==0:continue
        H=edges.setdefault((a,b),[0]*(local[b]['width']-1))
        H[j-1]^=1 << (i-1)
    edges={key:tuple(H) for key,H in edges.items() if any(H)}
    orders=it.graph_orders(len(local),edges);require(orders is not None,'original_auxiliary_graph_degree')
    interfaces={key:it.edge_interface(H,local[key[0]]['width']-1) for key,H in edges.items()}
    def endpoint(u,v):
        if v is None:return ()
        e=interfaces[tuple(sorted((u,v)))]
        return e['left'] if u<v else e['right']
    frames={}
    for component in orders:
        order=component['vertices'];cycle=component['cycle']
        for j,u in enumerate(order):
            previous=order[j-1] if j or cycle else None
            following=order[(j+1)%len(order)] if j+1<len(order) or cycle else None
            item=local[u];inverse=cc.inverse(item['polar'])
            A=tuple(cc.action(inverse,v) for v in endpoint(u,previous))
            B=tuple(cc.action(inverse,v) for v in endpoint(u,following))
            frames[u]=hyperbolic_frame(item['phase'],item['width']-1,A,B)
    columns=[]
    for j,item in enumerate(local):
        columns.append(cc.action(item['block'],item['h']))
        columns.extend(cc.action(item['block'],cc.action(item['K'],v)) for v in frames[j])
    columns=tuple(columns);require(len(echelon(columns))==n,'dependent_physical_frame')
    p0=pd.substitute_boolean(set(desc[3][0]),qr.affine_forms(0,columns,n))
    p1=pd.substitute_boolean(set(desc[3][1]),qr.affine_forms(0,columns,n))
    stars=set();qaux=set();control_positions=[]
    for o,item in zip(offsets,local):
        k=item['k'];control_positions.append(o)
        for i in range(k):
            pair=(1 << (o+1+i))|(1 << (o+1+k+i));qaux.add(pair);stars.add(pair|(1 << o))
    require({t for t in p1 if t.bit_count()>1}==stars
            and all(t==0 or t.bit_count()>1 or t.bit_length()-1 in control_positions for t in p1),
            'last_phase_normal_form')
    J=cc.compose(cc.transpose(columns),cc.compose(tuple(desc[2]),columns))
    require(all(J[o]==1 << o for o in control_positions),'control_fourier_pairing')
    require(pd.substitute_boolean(qaux,[(row,0) for row in cc.transpose(J)])==qaux,'auxiliary_fourier_isometry')
    delta=cc.action(cc.inverse(columns),cc.action(cc.inverse(tuple(desc[2])),1 << desc[5]))
    require(delta==sum(1 << o for o in control_positions),'not_all_control_parity')
    base=set(stars);components=[]
    for component in orders:
        order=component['vertices'];cycle=component['cycle'];matrices=[];widths=[local[u]['k'] for u in order]
        for j,u in enumerate(order):
            nxt=order[(j+1)%len(order)];ku=local[u]['k'];kv=local[nxt]['k'];ou=offsets[u];ov=offsets[nxt]
            H=[0]*kv
            if cycle or j+1<len(order):
                for b in range(kv):
                    for a in range(ku):
                        term=(1 << (ou+1+a))|(1 << (ov+1+kv+b))
                        if term in p0:H[b]^=1 << a;base.add(term)
            matrices.append(tuple(H))
        components.append(dict(**component,widths=widths,matrices=tuple(matrices),
                               basis=ch.graded_basis(matrices,widths)))
    remainder=p0^base
    require(all(t.bit_count()<=2 for t in remainder),'first_phase_normal_form')
    # Every cross-auxiliary term must have entered the recovered directed cycle.
    new_labels={}
    for j,item in enumerate(local):
        for i in range(item['width']):new_labels[offsets[j]+i]=(j,i)
    for term in remainder:
        if term.bit_count()!=2:continue
        (a,i),(b,j)=[new_labels[v] for v in pd.bits(term)]
        require(a==b or i==0 or j==0,'unresolved_cross_auxiliary_quadratic')
    boundary=it.signature(columns,cc.action(tuple(desc[2]),desc[4]))
    remainder^={1 << i for i in pd.bits(boundary)}
    # A local uv term is a control translation, not a necessary Fourier defect.
    local_quadratics=[]
    for o,item in zip(offsets,local):
        k=item['k'];local_quadratics.append({(1 << (o+1+i))|(1 << (o+1+k+i)) for i in range(k)})
    initial_rank=len(echelon(polar(remainder,n)));current_rank=initial_rank
    shifts=0;rank_trials=0;rank_history=[];changed=True
    while changed:
        changed=False
        for j,Qj in enumerate(local_quadratics):
            candidate=remainder^Qj;candidate_rank=len(echelon(polar(candidate,n)));rank_trials+=1
            if candidate_rank<current_rank:
                rank_history.append((j,current_rank,candidate_rank));changed=True
                shifts^=1 << j;remainder=candidate;base^=Qj;current_rank=candidate_rank
    Q=set(remainder)
    for i in range(n):Q^={(1 << i)|(1 << (n+i))}
    pushed=qr.quadratic_pushforward(Q,tuple(1 << (n+i) for i in range(n)),2*n)
    require(not pushed['zero'],'zero_quadratic_walsh_transform')
    rank=len(pushed['columns'])
    require(rank==current_rank and rank%2==0 and pushed['exponent']==n-rank//2,'quadratic_walsh_rank')
    require(rank<=rank_cap,'quadratic_rank_cap')
    flip=sum(1 for o in control_positions if (1 << o) in p1)%2
    return dict(accepted=True,reason='full_source_quadratic_cycle',descriptor=desc,columns=columns,
                transformed_phases=(p0,p1),pairing=J,stars=stars,base=base,remainder=remainder,
                offsets=tuple(offsets),local=local,components=components,walsh=pushed,rank=rank,flip=flip,
                terms=1 << (2*rank),qubits=n,total_aux=sum(item['k'] for item in local),control_shifts=shifts,
                initial_rank=initial_rank,rank_trials=rank_trials,rank_history=rank_history)


def reduce_source(desc,rank_cap=4,state_cap=67):
    if type(rank_cap) is not int or rank_cap<0:raise ValueError('nonnegative quadratic rank cap required')
    if type(state_cap) is not int or state_cap<1:raise ValueError('positive relation cap required')
    desc=cc.normalize_descriptor(desc)
    try:certificate=canonical_source(desc,rank_cap)
    except Refusal as exc:
        result=ch.reduce_source(desc,state_cap);result['asymmetric_count']=dict(accepted=False,reason=str(exc))
        return result
    return dict(descriptor=desc,asymmetric_count=certificate)


def reduce_native(n,gates,basis,output,rank_cap=4,state_cap=67):
    return reduce_source(cc.recognize_native(n,gates,basis,output),rank_cap,state_cap)


def evaluate_source(result,bits,max_terms=None,max_work=None):
    if type(bits) is not int or bits<1:raise ValueError('positive precision bits required')
    cert=result['asymmetric_count']
    if not cert['accepted']:
        answer=ch.evaluate_source(result,bits,max_work)
        return dict(answer,route='retained_character_reader',refusal=cert['reason'])
    if max_terms is not None:
        if type(max_terms) is not int or max_terms<0:raise ValueError('nonnegative term cap required')
        if cert['terms']>max_terms:
            return dict(mode='budget_refused',probability=None,required_terms=cert['terms'],route='asymmetric_count')
    rank=cert['rank'];W=cert['walsh']
    def frequency(z):
        return W['origin']^cc.action(W['columns'],z),(-1)**cc.anf_evaluate(W['phase'],z)
    total=Fraction(0);calls=0;transitions=0
    for z in range(1 << rank):
        alpha,sa=frequency(z)
        for w in range(1 << rank):
            beta,sb=frequency(w)
            value=Fraction(sa*sb)
            for component in cert['components']:
                order=component['vertices'];A=[[],[]];B=[[],[]];delta=0;shifts=0
                for j,u in enumerate(order):
                    o=cert['offsets'][u];k=cert['local'][u]['k'];mask=(1 << k)-1
                    if 1^((alpha >> o)&1)^((beta >> o)&1):delta|=1 << j
                    if cert['control_shifts'] >> u&1:shifts|=1 << j
                    for c,freq in enumerate((alpha,beta)):
                        A[c].append((freq >> (o+1))&mask)
                        B[c].append((freq >> (o+1+k))&mask)
                answer=cycle_character(component['matrices'],component['widths'],A,B,delta,basis=component['basis'])
                value*=(-1)**((delta&shifts).bit_count()%2)*answer['normalized_value'];calls+=1
                transitions+=answer['stats']['selection_transitions']
            total+=value
    expectation=(-1)**cert['flip']*total/(1 << rank);p=(1-expectation)/2
    require(0<=p<=1,'original_acceptance_range')
    rounded=Fraction((p.numerator << bits)//p.denominator,1 << bits)
    return dict(mode='exact',route='asymmetric_count',probability=p,rounded=rounded,error_bound=p-rounded,
                expectation=expectation,random_bits=0,failure_probability=0,rank=rank,terms=cert['terms'],
                character_calls=calls,selection_transitions=transitions)
