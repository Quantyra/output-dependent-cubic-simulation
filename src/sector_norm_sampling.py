"""S175: joint sector/equatorial norm sampling with exact Gaussian integers.

The norm primitive is Bravyi et al., arXiv:1808.00128v2, Sec. 4.3.
This module integrates it with the source-derived R05-29 sector compiler.
No state vector, supplied stabilizer decomposition or nested estimator is used.
"""
from fractions import Fraction
import sector_cubic_sampling as ss
from sector_cubic_sampling import cc, qr, pd, sc, lf, af, echelon, solve, require, draw


def add4(poly, term, coefficient):
    value = (poly.get(term, 0) + coefficient) % 4
    if value:
        poly[term] = value
    else:
        poly.pop(term, None)


def substitute4(poly, forms):
    """Pull a Z4 quadratic with even cross coefficients through an affine map."""
    out = {}
    for term, coefficient in poly.items():
        indices = tuple(pd.bits(term))
        if not indices:
            add4(out, 0, coefficient)
        elif len(indices) == 1:
            row, constant = forms[indices[0]]
            add4(out, 0, coefficient * constant)
            positions = tuple(pd.bits(row))
            for j in positions:
                add4(out, 1 << j, coefficient * (1 - 2 * constant))
            for p, j in enumerate(positions):
                for k in positions[p + 1:]:
                    add4(out, (1 << j) | (1 << k), 2 * coefficient)
        else:
            require(len(indices) == 2 and coefficient == 2, 'invalid_z4_quadratic')
            product = {0}
            for j in indices:
                row, constant = forms[j]
                terms = {1 << k for k in pd.bits(row)} | ({0} if constant else set())
                new = set()
                for a in product:
                    for b in terms:
                        new.symmetric_difference_update({a | b})
                product = new
            for monomial in product:
                add4(out, monomial, 2)
    return out


def gaussian4(poly, width):
    """Exact (real, imaginary) integer sum, using two binary quadratic sums."""
    require(all(0 <= m < (1 << width) for m in poly), 'z4_width')
    phase = set()
    odd = []
    constant = poly.get(0, 0)
    for term, coefficient in poly.items():
        if not term:
            continue
        require(term.bit_count() <= 2 and (term.bit_count() == 1 or coefficient == 2),
                'nonquadratic_z4_phase')
        if coefficient // 2:
            phase.symmetric_difference_update({term})
        if coefficient % 2:
            odd.append(term)
    for j, a in enumerate(odd):
        for b in odd[j + 1:]:
            phase.symmetric_difference_update({a | b})
    first = lf.quadratic_value(phase, width)
    second = lf.quadratic_value(phase.symmetric_difference(odd), width)
    require((first + second) % 2 == 0 and (first - second) % 2 == 0,
            'nonintegral_gaussian_integer')
    value = ((first + second) // 2, (first - second) // 2)
    return (value, (-value[1], value[0]), (-value[0], -value[1]),
            (value[1], -value[0]))[constant]


def fixed_prefix(poly, count, assignment):
    return sc.fiber(dict(phase=poly, control_count=count), assignment)


def prepare(result):
    """Construct both low-rank summands from the original source certificate."""
    cert = result['sector_cubic']
    if not cert['accepted']:
        return dict(result, norm_sector=dict(accepted=False, reason=cert['reason']))
    desc = result['descriptor']
    _, n, J, phases, basis, _ = desc
    source = result['displacement']
    D, r = source['directions'], source['rank']
    c, k = cert['sector_rank'], cert['restricted_control_rank']
    Cright = cert['columns'][:c]
    eta = result['matching']['eta']
    shift = solve(echelon(D), source['origin'] ^ cc.action(Cright, eta))
    require(shift is not None, 'source_sector_offset')
    # Variables are (a,y,t), where x=R*a+D*y and x'=R*(a+eta)+D*t.
    xforms = qr.affine_forms(0, Cright + tuple(v for v in D) + (0,) * r, n)
    tforms = qr.affine_forms(cc.action(Cright, eta), Cright + (0,) * r + tuple(D), n)
    zforms = [((1 << (c + j)) | (1 << (c + r + j)), (shift >> j) & 1)
              for j in range(r)]
    full = pd.substitute_boolean(source['joint'], xforms + zforms)
    phase0 = set(phases[0]) ^ {1 << j for j in pd.bits(cc.action(J, basis))}
    g0 = pd.substitute_boolean(phase0, xforms)
    g1 = pd.substitute_boolean(phase0, tforms)
    kernel = full ^ g0 ^ g1
    require(all(m.bit_count() <= 2 for m in kernel), 'sector_kernel_not_quadratic')
    cross = tuple(sum(int(((1 << (c + i)) | (1 << (c + r + j))) in kernel) << j
                      for j in range(r)) for i in range(r))
    require(len(echelon(cross)) == r, 'sector_kernel_not_unitary')
    U = result['discovery']['controls']
    right = tuple(qr.affine_space([(u, int(i == j)) for i, u in enumerate(U)], r)[0]
                  for j in range(k))
    frame = right + tuple(result['discovery']['kernel'])
    require(len(frame) == r and len(echelon(frame)) == r, 'invalid_norm_frame')
    acols = tuple(1 << j for j in range(c)) + tuple(v << (c + r) for v in frame)
    bcols = tuple(1 << j for j in range(c)) + tuple(v << c for v in frame)
    bcols += tuple(1 << (c + r + j) for j in range(r))
    apoly = pd.substitute_boolean(g1, qr.affine_forms(0, acols, c + 2 * r))
    bpoly = pd.substitute_boolean(g0 ^ kernel, qr.affine_forms(0, bcols, c + 2 * r))
    mask = (1 << (c + k)) - 1
    require(all(m & mask for p in (apoly, bpoly) for m in p if m.bit_count() == 3),
            'norm_control_does_not_remove_cubic')
    norm = dict(accepted=True, rank=r, sectors=c, controls=k, frame=frame,
                state_phase=g0, partner_phase=g1, kernel_phase=kernel,
                a_phase=apoly, b_phase=bpoly, gaussian_widths=(r-k, 2*r-k),
                equatorial_bits=2*r+r*(r-1)//2, norm_denominator=1 << (2*r))
    return dict(result, norm_sector=norm)


def equatorial_phase(width, word):
    phase = {}
    for j in range(width):
        add4(phase, 1 << j, -(word & 3))
        word >>= 2
    for j in range(width):
        for k in range(j + 1, width):
            add4(phase, (1 << j) | (1 << k), 2 * (word & 1))
            word >>= 1
    require(word == 0, 'equatorial_word_out_of_range')
    return phase


def norm_numerator(prepared, sector, graph_word):
    """Numerator of Z=2^r |<phi|psi_partner+O psi>|^2; denominator 2^(2r)."""
    cert = prepared['norm_sector']
    r, c, k = cert['rank'], cert['sectors'], cert['controls']
    require(type(sector) is int and 0 <= sector < (1 << c), 'invalid_sector')
    require(type(graph_word) is int and 0 <= graph_word < (1 << cert['equatorial_bits']),
            'invalid_equatorial_word')
    graph = equatorial_phase(r, graph_word)
    framed = substitute4(graph, qr.affine_forms(0, cert['frame'], r))
    atotal, btotal = [0, 0], [0, 0]
    for u in range(1 << k):
        assignment = sector | (u << c)
        aq = {m: 2 for m in fixed_prefix(cert['a_phase'], c+k, assignment)}
        forms = [(0, (u >> j) & 1) for j in range(k)]
        forms += [(1 << j, 0) for j in range(r-k)]
        for m, v in substitute4(framed, forms).items():
            add4(aq, m, v)
        bq = {m: 2 for m in fixed_prefix(cert['b_phase'], c+k, assignment)}
        for m, v in graph.items():
            add4(bq, m << (r-k), v)
        av, bv = gaussian4(aq, r-k), gaussian4(bq, 2*r-k)
        for j in range(2):
            atotal[j] += av[j]
            btotal[j] += bv[j]
    amplitude = [((1 << (r//2)) * atotal[j] + btotal[j]) for j in range(2)]
    return sum(v*v for v in amplitude)


def evaluation_plan(prepared, bits):
    old = ss.evaluation_plan(prepared, bits)
    if old['mode'] != 'sector_cubic_sampling':
        return old
    cert = prepared['norm_sector']
    h, r, k = prepared['failure_bits'], cert['rank'], cert['controls']
    group_size, groups = 32 * (1 << (2*bits)), 2*h+3
    samples = group_size * groups
    random_width = prepared['sector_cubic']['random_width'] + cert['equatorial_bits']
    return dict(mode='sector_norm_sampling', bits=bits, failure_bits=h,
                epsilon=Fraction(1, 1 << bits), group_size=group_size, groups=groups,
                samples=samples, gaussians_per_sample=4*(1 << k),
                gaussian_sum_bound=4*(1 << k)*samples,
                sample_random_bits=random_width*samples,
                discovery_random_bits=prepared['discovery']['stats']['random_bits'],
                random_bit_bound=prepared['discovery']['stats']['random_bits']+random_width*samples,
                failure_probability=Fraction(1, 1 << h),
                guarantee_requires='two_layers_with_shortcut_or_small_restricted_controls_and_full_rank_anchor')


def evaluate_source(prepared, bits, coins, max_samples=None, max_gaussians=None):
    plan = evaluation_plan(prepared, bits)
    if plan['mode'] != 'sector_norm_sampling':
        return ss.evaluate_source(prepared, bits, coins, max_samples, max_gaussians)
    for cap in (max_samples, max_gaussians):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('nonnegative evaluation cap required')
    stats = dict(random_bits=0, random_calls=0, gaussian_sums=0)
    if ((max_samples is not None and plan['samples'] > max_samples) or
        (max_gaussians is not None and plan['gaussian_sum_bound'] > max_gaussians)):
        return dict(mode='budget_refused', estimate=None, plan=plan, stats=stats)
    cert = prepared['norm_sector']
    sector_cert = prepared['sector_cubic']
    den, size = cert['norm_denominator'], plan['group_size']
    sums = []
    for _ in range(plan['groups']):
        total = 0
        for _ in range(size):
            a = af.orbit_representative(sector_cert, draw(coins, sector_cert['random_width'], stats))
            word = draw(coins, cert['equatorial_bits'], stats)
            total += norm_numerator(prepared, a, word) - 2*den
            stats['gaussian_sums'] += plan['gaussians_per_sample']
        sums.append(total)
    median = sorted(sums)[len(sums)//2]
    raw = (1 - Fraction(median, 2*den*size))/2
    raw = max(Fraction(0), min(Fraction(1), raw))
    estimate = Fraction((raw.numerator << (bits+2))//raw.denominator, 1 << (bits+2))
    require(stats['random_bits'] == plan['sample_random_bits'], 'norm_random_bit_accounting')
    return dict(mode=plan['mode'], estimate=estimate, probability=None,
                error_bound=Fraction(3, 1 << (bits+2)),
                failure_probability=plan['failure_probability'], plan=plan, stats=stats)


def simulate_native(n, gates, basis, output, bits, control_cap, failure_bits, coins,
                    max_samples=None, max_gaussians=None):
    prepared = prepare(ss.reduce_native(n, gates, basis, output, control_cap, failure_bits, coins))
    return evaluate_source(prepared, bits, coins, max_samples, max_gaussians)
