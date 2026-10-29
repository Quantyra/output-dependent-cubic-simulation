# Theorem comparison for output dependent cubic simulation

Date: 2026-10-28. Publication story: S174.
Scope: the R05-29 source compiler at `75694fa51add1c5293168349c4d29af9ef4030ea` and the S175 joint norm readout at `2af4aa9c4e4f8e5f9a76e191122f846cadc73eb1`.
Disposition: develop a standalone, bounded methods preprint about the explicit source reduction, promised discovery and complete costs. Present Gaussian conditioning, independent spaces, stabilizer decompositions and norm estimation as established ingredients. Do not claim a new general simulation primitive or priority over all equivalent formulations.

## Exact comparison task

The source is a literal native circuit recognized as three binary Fourier layers interleaved with two real Boolean cubic diagonal phases, with the same symmetric invertible binary matrix J in those Fourier layers. The input is a specified computational basis state and the measured quantity is one output-bit probability. The accuracy contract is additive epsilon with failure delta, including source recognition, discovery, random bits, arithmetic and memory. It is not exact amplitude computation, full-distribution sampling, or arbitrary-depth simulation.

Let Q be the second phase's derivative for the measured output, r its even quadratic polar rank, and S the computed r-dimensional displacement support. Let k be a certified control codimension for the first cubic restricted to S. The general source search has a cap Qcap and a full-rank-anchor promise, with cost `2^O(Qcap^2)` times a source/confidence polynomial. Deterministic admitted shortcuts have their separately stated scope. The resulting readout is `2^k epsilon^-2 log(1/delta)` times a polynomial by S175. The source search can dominate the readout.

## Published statements and precise relationships

| Source and anchor | Published interface relevant here | Relationship to this construction |
|---|---|---|
| Maslov et al., [arXiv:2402.03211v1, section II](https://arxiv.org/html/2402.03211v1#S2) | Fix a cover of cubic variables; the remaining amplitudes are quadratic/Clifford sums. | Directly supplies the conditional Gaussian ingredient. Our affine control basis turns each sector into their covering-set form. The `4^k` pairwise sector evaluator is an application of this machinery. Their specific Harvard/QuEra cover bound is not a bound for every source here. |
| Blaser et al., [arXiv:2609.39918v1, Definition 1, Theorems 41 and 67, section 5.1](https://arxiv.org/html/2609.39918v1) | A supplied independent space permits exact cubic-amplitude evaluation; rank-profile recovery has a high-probability guarantee for their planted distribution. | Our T(K,K,K)=0 certificate is the same independent-space condition, applied after output restriction. The amplitude evaluation is not new. Our recovery theorem is a slower, per-promised-input guarantee with explicit caps, not a faster planted-recovery theorem. |
| Park, Kwon and Jeong, [arXiv:2307.16688v2, supplementary section IV.3, Theorem 4](https://arxiv.org/html/2307.16688v2) | Marginal estimation for Clifford evolution of specified product inputs with nonnegative framed-Wigner access and a quadratic or small-cover output frame. | Output restriction and covering-set marginal estimators are prior art. The literal input/operation hypotheses differ; the reduction below identifies the missing positive product-state access rather than treating their theorem as an oracle. |
| Van den Nest, [arXiv:0911.1624v3, sections 4.1 and 4.3, Theorems 1 and 3](https://arxiv.org/html/0911.1624v3) | Computationally tractable states provide sampling and amplitude access; efficiently computable sparse operators permit expectation estimation. | The first phase state is tractable, but the pulled-back output Clifford has `2^r` entries per row. Large r violates the direct sparse-operator hypothesis. Sector conditioning constructs an alternative access route; it does not extend the abstract theorem beyond its hypotheses. |
| Bravyi et al., [arXiv:1808.00128v2, section 4.3, Lemmas 2-4](https://arxiv.org/html/1808.00128v2#S4.SS3) | Equatorial norm estimation has variance controlled by the norm and cost linear in a supplied stabilizer decomposition. | S175 explicitly reduces our readout to this primitive using at most `2^(k+1)` constructed terms. The new integration pays source conversion and combines sector/norm randomness; neither the norm primitive nor its linear rank dependence is novel. |
| Zhang and Zhang, [arXiv:2409.13809v2, section IV.1, Algorithm 1](https://arxiv.org/html/2409.13809v2#S4.SS1) | Additive estimation of Pauli observables, including normalized averages, after one efficiently evaluable diagonal magic layer and Clifford preparation. | Our original circuit has two diagonal layers. Pulling back the second one produces a Clifford observable, generally not a Pauli. The explicit Pauli expansion below is a reduction with an additional `2^r` variance bound, not a polynomial-cost subsumption at unrestricted r. |

## Conditional covering and norm estimation are subsumed ingredients

For a sector a, choose an invertible coordinate frame `(u,z)` on S with `u=U y` and z spanning K. Vanishing of T on K^3 means every surviving cubic term meets u. Fixing u leaves a quadratic phase, including all affine and lower-degree terms. This is precisely a covering-set decomposition in the new coordinates, with `2^k` branches. In the sector's ket/bra pair, fixing both control assignments gives `4^k` quadratic sums. Thus the exact sector evaluator is a direct application of the published covering/independent-space method; coordinate changes alone do not establish a new primitive.

Each normalized sector state has a `2^k`-term stabilizer representation. The computed output Clifford preserves it. Applying the published norm estimator to their sum gives the S175 readout. The S175 proof supplies the original-source construction, exact coefficients and joint variance bound. This is a source-specific theorem assembled from established components, with an explicit full-cost contract.

## Discovery promises are quantitatively different

Apply Blaser et al.'s notation to the restricted r-dimensional phase: their independent-space dimension is h0=r-k. Theorem 67 has work `O(h0*r^3*2^k)` and exponentially high success probability over their random planted model when h0 exceeds half the ambient dimension by a fixed fraction. Our search does not claim that bound. Under the concrete promise that some v in K has contraction rank 2k, it finds and verifies a control frame for every promised polynomial with failure at most the chosen delta, using at most `4^Qcap` times a confidence factor in probes and `2^O(Qcap^2)` streamed candidates.

The implication used here is deterministic: rank 2k forces the k-dimensional control covectors into the image of the contraction. A nonzero Pfaffian gives the lower bound on the density of useful probes. The planted theorem instead identifies the planted space using typical rank behavior; a low-rank slice need not identify that same space on an arbitrary promised polynomial. Our final certificate check remains sound on atypical inputs. This distinguishes quantifiers and access guarantees, not broad expressive power. Fixed low-rank cubics with large radicals illustrate nonrandom promised inputs; no probability statement about them is inferred from the planted theorem. Small-control existence without an anchor remains unproved for this search.

## Literal framed Wigner and sparse access hypotheses

The first phase-prepared state need not be a product. For a cubic `x1*x2*x3`, its amplitudes across the partition `x1 | (x2,x3)` include the minor `[[1,1],[1,-1]]`, whose determinant is nonzero. Absorbing that cubic phase into the circuit instead introduces a non-Clifford operation: conjugating X1 produces X1 times a nontrivial controlled-Z. Consequently, the literal input-and-Clifford interface of Park et al.'s Theorem 4 does not automatically receive these circuits. A different embedding, positive framed representation or postselection construction would have to include its preparation and normalization costs. We do not prove that no such reduction exists.

For Van den Nest's interface, the first phase state's computational magnitudes are uniform and its amplitudes are directly evaluable, so it is computationally tractable. However, the observable `F_J D_Q F_J Z_e` has exactly `2^r` nonzero entries in each row, of magnitude `2^(-r/2)`. This follows from the computed quadratic Walsh support. For growing r it is not sparse in this basis. Diagonalizing it by a Fourier/Clifford basis change transfers the obligation to tractability of the transformed cubic state, which is not supplied for free. Small-r instances are covered by the sparse framework; the proposed theorem allows large r with small output-restricted k.

## Explicit reduction to a normalized Pauli average

The quadratic phase has the exact Fourier expansion

    D_Q = sum_v alpha_v Z_v,
    alpha_v = 2^-n W_Q(v).

There are `2^r` nonzero coefficients, each with absolute value `2^(-r/2)`. Conjugation by F_J and multiplication by Z_e convert the terms into signed Hermitian Paulis; invariance of the derivative along J^-1 e ensures the relevant commutation. The coefficient absolute sum is `A=2^(r/2)`. Therefore the Clifford observable divided by A is a uniformly sampled signed-Pauli average.

This gives a concrete use of the one-diagonal-layer Pauli-estimation machinery on the original flat cubic phase state. To recover the unnormalized expectation to error epsilon, estimate that normalized average to error epsilon/A. The resulting generic bounded-sample guarantee costs `O(2^r epsilon^-2 log(1/delta))` samples. This is a valid reduction and baseline, not a lower bound: cancellations or a more suitable implementation may do better. The output-restricted-control theorem replaces this generic readout guarantee on its admitted sources, while retaining the additional discovery obligations.

## Contribution statement and disposition

The supported contribution to present is: an explicit source-to-output reduction for the specified two-layer grammar, output-restricted independent-space discovery under disclosed promises, and a fully costed integration of conditional stabilizer norm estimation with examples and method limits. The public text should call this a constructive application/refinement of established simulation methods. It must cite prior output-dependent and covering-set estimators prominently.

This comparison supports a bounded methods preprint without a claim that a fundamentally new simulator, a new general tractability class, or a best-known practical runtime has been established. It does not certify priority or exclude an equivalent theorem elsewhere. S176 must still supply the matched-family evidence and preserve unfavorable baselines. If that evidence shows the proposed framing adds no useful theorem or reproducible access construction, select a technical note or merge rather than inflate novelty.

Remaining to-do list: complete S176's growing-family and matched-cost comparison, then draft the self-contained manuscript with the established ingredients and source-specific contribution distinguished throughout.
