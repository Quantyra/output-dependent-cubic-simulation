# Joint sector and norm estimation with complete source costs

Date: 2026-10-28. Publication story: S175. Research baseline: `75694fa51add1c5293168349c4d29af9ef4030ea`, R05-29.
Status: mathematical construction with exact executable checks; no Lean certification or novelty certification.

Implementation: [sector_norm_sampling.py](../src/sector_norm_sampling.py). Checks: [check_sector_norm_sampling.py](../src/check_sector_norm_sampling.py). Receipt: [s175-sector-norm-checks.json](../artifacts/s175-sector-norm-checks.json).

The readout factor can be reduced from `4^k` to `2^k`, with a larger explicit sampling constant and the same source-discovery promises. The norm-estimation ingredient is established: Bravyi, Browne, Calpin, Campbell, Gosset and Howard, [arXiv:1808.00128v2, section 4.3, Lemma 2](https://arxiv.org/html/1808.00128v2#S4.SS3), gives an unbiased norm-square estimator using equatorial stabilizer states, variance at most the squared norm-square, and work linear in the supplied stabilizer decomposition length. The work here constructs that decomposition/access from the sector source and combines its randomness with sector sampling without nesting two accuracy requirements.

## Source semantics and a Clifford kernel

Retain the literal two-phase source from [R05-29](../manuscript/main.tex): a symmetric invertible binary Fourier matrix J, basis input beta, output e, and Boolean cubic phases f0,f1. Put Q(v)=f1(v)+f1(v+J^-1 e). Let the quadratic Walsh transform of Q have affine support J(d0+S), where S has even dimension r. Its normalized nonzero values have magnitude `2^(-r/2)` and a computed quadratic sign w(z). Let D be the computed basis matrix of S, and C the full-row-rank annihilator of S, with c=n-r rows, right inverse R, and eta=C d0. Solve D s=d0+R eta.

The conditional first-phase states on the reduced r coordinates are

    psi_a(y) = 2^(-r/2) (-1)^[f0(Ra+Dy)+(J beta).(Ra+Dy)].

They have unit norm for every a, independent of the difficulty of discovering controls. Their physical supports Cx=a are orthogonal and have exactly uniform mass `2^-c`.

The physical observable is

    O = F_J D_f1 F_J Z_e F_J D_f1 F_J
      = F_J D_Q F_J Z_e.

The second expression follows from conjugating Z_e to translation by J^-1 e. Therefore O is Clifford: Q is quadratic. It is also real, Hermitian and unitary by the first expression. Its Walsh support maps sector a only into sector a+eta. In reduced coordinates, its kernel is

    O_a(t,y) = 2^(-r/2) (-1)^q_a(y,t),
    q_a(y,t) = w(y+t+s) + e.(Ra+Dy).

The output derivative is invariant under J^-1 e, so e annihilates S and e.d0=0. The e term is constant within the sector; the cross bilinear matrix of q_a is nonsingular. Both facts also follow from the sector restriction of the unitary O. The implementation derives q_a by substituting the two physical points into the full original output polynomial, then cancelling the two source state phases. It verifies the quadratic degree and nonsingular cross matrix from the original source rather than accepting an operator supplied by the caller.

Thus, exactly as in the original bounded-sector identity,

    X_a = <psi_(a+eta), O_a psi_a>,
    |X_a| <= 1,   X_a=X_(a+eta),
    E = average_a X_a,   p=(1-E)/2.

All amplitudes are real. For u_a=psi_(a+eta)+O_a psi_a,

    ||u_a||^2 = 2+2 X_a,          0 <= ||u_a||^2 <= 4.       (1)

Nonzero input characters, affine origins, lower-degree terms and matching offsets remain in these identities. There is no postselection normalization to estimate.

## Constructing access in linear branch count

The retained source compiler finds k independent covectors U on S and verifies that the restricted cubic tensor vanishes on K^3, K=ker U. Choose a right inverse of U and a basis of K. Fixing U y leaves a quadratic phase on r-k free variables in each psi_a. Each state is therefore the sum of `2^k` explicitly normalized stabilizer states with coefficients `2^(-k/2)`. Applying the constructed Clifford O_a preserves that property. The sum in (1) uses at most `2^(k+1)` terms; this is a constructed representation, not a promised minimal stabilizer rank.

The implementation avoids a separate tableau dependency. Draw a quadratic Z4 phase

    z_A(t) = sum_j d_j t_j + 2 sum_(j<l) a_jl t_j t_l,

where the d_j are independent uniform elements of Z4 and the a_jl are independent fair bits. This uses exactly `d_r=2r+r(r-1)/2` bits. The sampled equatorial state is `phi_A(t)=2^(-r/2) i^z_A(t)`.

After fixing U, compute the following two sums with all coefficients/phases retained:

    A = sum_t i^(-z_A(t)) (-1)^g_(a+eta)(t),
    B = sum_(y,t) i^(-z_A(t)) (-1)^[g_a(y)+q_a(y,t)].

A uses `2^k` Z4 quadratic sums of width r-k, and B uses `2^k` sums of width 2r-k. Their combination is

    Z_(a,A) = 2^r |<phi_A,u_a>|^2
            = |2^(r/2) A+B|^2 / 2^(2r).                   (2)

Since r is even, the numerator and denominator in (2) are integers. In particular, no floating-point cancellation, square-root approximation, coefficient-norm oracle or per-sector norm subroutine accuracy is needed.

For completeness, the implementation reduces a Z4 quadratic sum to two binary ones. Write its odd linear part as a parity L, using

    sum_(j in I) x_j = L(x)+2 sum_(j<l in I) x_j x_l (mod 4).

Absorb the pair terms and even coefficients into a Boolean quadratic q. Up to the constant power of i, with G0=sum_x (-1)^q(x) and G1=sum_x (-1)^[q(x)+L(x)], the answer is `(G0+G1)/2 + i(G0-G1)/2`. Each numerator is even. This gives exactly `4*2^k` calls to the existing real quadratic-sum routine per joint draw. Affine pullback of the Z4 phase is also quadratic and is performed explicitly.

## One estimator and one accuracy budget

Draw an orbit representative a uniformly, using c bits if eta=0 and c-1 otherwise. Independently draw A. Define

    Y = Z_(a,A)/2 - 1.

The cited norm lemma gives `E[Y|a]=X_a` and `Var(Y|a)<=(1+X_a)^2`. This remains valid when the norm vanishes: then Z=0 for every A and Y=-1. Let mu=E_a X_a. The law of total variance yields

    Var(Y) <= E[(1+X)^2] + Var(X)
           = 1+2mu+2E[X^2]-mu^2
           <= 4-(1-mu)^2 <= 4.                            (3)

Only the variance is bounded; individual Y values need not lie in [-1,1]. Do not apply bounded-variable Hoeffding to Y or clip individual samples, which would change its mean.

For integers b,h>=1, let epsilon=2^-b. Use groups of size `L=32*4^b` and an odd number `K=2h+3` of independent groups. Each group averages independent joint draws. Chebyshev and (3) bound a group's probability of error greater than epsilon by 1/8. If the median of group means errs, at least half the groups err, so

    Pr[|median-mu|>epsilon]
        <= 2^K (1/8)^(K/2)
        = 2^(-K/2) < 2^(-h-1).                            (4)

The unchanged discovery routine receives the existing h+1 confidence allocation and fails with probability at most `2^(-h-1)` on its stated anchor promise. A union bound gives total failure less than `2^-h`. Conditional concentration applies uniformly to any sound accepted control frame, including a frame selected by earlier random discovery.

Convert the median to `(1-median)/2`, project that final value to [0,1], and round downward at b+2 fractional bits. Projection does not increase error relative to the true probability, and rounding adds at most epsilon/4. The returned acceptance error is at most `3epsilon/4`. Discovery/refusal and evaluation caps remain explicit; no guarantee is attached to a truncated discovery search that misses its certificate.

## Complete resource bound and its limits

Let B be the literal source bit length, m=n+r, and Qcap the search cap. Define

    A_cap = 4^Qcap (h+2),
    C_cap = 4(Qcap+1) 2^(Qcap^2),
    N = 32*4^b*(2h+3).

The original source parser, full-phase reconstruction, control discovery and verification are unchanged. With dense polynomial substitution and elementary integer arithmetic, a conservative every-tape bound is

    Time O~((B+m+Qcap+2)^12
            +(r+A_cap)(1+C_cap)(m+Qcap+2)^10
            +N*2^(k+2)*(m+Qcap+2)^10
            +(N+K+1)*(m+b+h+Qcap+2)^4).

The first term also pays the new coordinate/kernel construction. The third pays all per-draw restrictions, graph transformations and real quadratic sums; there is no uncharged stabilizer conversion or complex arithmetic. All phase representations have polynomially many coefficients. Integers in a single sum and (2) have O(m) bits, and accumulated group numerators add O(log L) bits. Store K group totals, one sampled graph, and one streamed branch at a time. A conservative space bound is

    O~((B+m+Qcap+2)^8+(m+b+h+Qcap+2)^4).

The total fair-bit cap is

    r*A_cap + N*(c-1_(eta!=0)+2r+r(r-1)/2),

with the actual discovery contribution reduced for deterministic shortcuts. Sampling and Gaussian caps are checked before any readout draw. The exact quadratic shortcut still uses one real Gaussian sum, zero random bits and polynomial precision-bit cost.

The sampled theorem is polynomial in inverse error, not in b. General discovery still costs `2^O(Qcap^2)` under a full-rank-anchor promise; mere existence of a small control space is insufficient. The readout improvement does not improve that discovery exponent. The larger explicit median-of-means constant can make this implementation slower at small k; `2^k` is the exponential-factor statement, not a measured blanket speedup. The retained `4^k` coherent evaluator remains available.

## Executed checks and publication handoff

The checker uses an independent dense sum for Z4 Gaussian values and affine pullbacks, constructs small sector vectors and entire operator matrices, exhausts the equatorial distribution on small ranks, and compares its first/second moments exactly. It checks zero norms, nonzero matching offsets and inputs, hidden coordinates and direct norm numerators against the production branch calculation. Full sampled runs start from literal native gates and compare with independent exact state evolution; retained `4^k` sector evaluation is forbidden during those runs. High-b schedules are inspected with a zero execution budget, not executed as exponentially long samples. Explicit grammar and cap-one refusals remain refusals.

Run from the repository root with a Python 3 standard-library environment:

    python src/check_sector_norm_sampling.py

The receipt records actual counts, seeds, source sizes, per-run operation/random-bit counts, output references, elapsed observations and source hashes. Those finite checks support the implementation; equations (1)-(4) and the source/discovery proofs establish the mathematical guarantee. No hardware/cloud trial, external message or Lean build is involved.

S175's mathematical outcome is an improved readout theorem with complete finite-bit integration. S174 must still determine its relation to other published frameworks, and S176 must compare matching tasks and full costs. This note does not establish priority, practical supremacy, a new universally simulatable language class, or BPP=BQP.

Remaining to-do list: complete S174's theorem-level prior-work comparison and S176's matched-family/cost assessment, then integrate the supported result into the first manuscript before Zenodo hookup.
