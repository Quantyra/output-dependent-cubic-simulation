# Growing families and matched sector readout comparisons

Date: 2026-10-28. Publication story: S176.
Sources: [prior-work comparison](s174-sector-publication-theorem-comparison-2026-10-28.md), [joint norm theorem](s175-sector-norm-estimation-and-cost-2026-10-28.md), and the frozen R05-29 sector theorem at `75694fa51add1c5293168349c4d29af9ef4030ea`.
Evidence: [source-level checker](../src/check_sector_norm_sampling.py) and [receipt](../artifacts/s175-sector-norm-checks.json), including the exact descriptors used by both readers.

The evidence supports a structural methods preprint. It does not support a claim of general practical superiority: at the small control counts executed here, the retained pairwise evaluator has the smaller prescribed Gaussian budget. The simple unperturbed family also has an elementary exact formula that is cheaper than either sampler.

## Matched task and costs

All comparisons below concern the same designated output probability from the same literal two-layer source, to additive epsilon with failure at most delta. An exact algorithm can meet this task by returning its exact answer; its stronger output is identified explicitly. Let r be the output-displacement dimension, k the verified restricted-control count, and g a control count for the entire first cubic. P denotes the relevant fixed polynomial in source size, dimension and arithmetic precision, not a common measured machine instruction.

| Method | Recognition/discovery obligation | Readout guarantee | What the comparison means |
|---|---|---|---|
| Normalized Pauli expansion of the pulled-back Clifford | Construct Q and its quadratic Walsh support from the source; no control search | `2^r epsilon^-2 log(1/delta) P` via the coefficient absolute-sum bound | The explicit reduction to Zhang-Zhang/tractable-state Pauli estimation in S174; an upper bound for this sampler, not a lower bound against their framework. |
| Global cubic covering plus stabilizer norm estimation | Find a global independent space or account for a supplied certificate | `2^g epsilon^-2 log(1/delta) P` | Grants the established linear-length norm primitive to the global method. The certificate lower bound below is not a stabilizer-rank lower bound. |
| R05-29 coherent sector evaluator | Same original-source restricted-control search as the new reader | `4^k epsilon^-2 log(1/delta) P` | Conditional covering-set/Gaussian method; all interference within a sector is retained before bounded sampling. |
| S175 joint sector/norm evaluator | Same search, plus polynomial kernel/frame construction | `2^k epsilon^-2 log(1/delta) P` | Reduces the readout exponent with larger explicit sample constants and widths. It does not improve general discovery. |
| Elementary closed-form family calculation | Recognize the unperturbed family or its verified transformed presentation | Exact polynomial arithmetic | Wins on the elementary examples when this formula applies. It is not assumed for arbitrary admitted perturbations. |

General restricted discovery contributes the S175 term `2^O(Qcap^2)` under the stated full-rank-anchor promise. The deterministic one-control family below avoids that search. All methods must charge their actual source recognition or certificate construction; a supplied certificate is a favorable comparison for a baseline, not free access granted to our algorithm. Polynomial space is achieved by streaming branches/samples; no exponential table is counted as preprocessing. No wall-time ordering follows solely from these symbolic bounds.

## A growing source family and a control distinction

For even t>=2 use coordinates c,w, the t-by-t matrix X, and t-vectors U,V. There are `n=t^2+2t+2` qubits. Define

    f0 = c*w + sum_ij X_ij U_i V_j,
    f1 = c*w + c*(Qdet(X)+U_0 V_0),
    Qdet = sum_(i,j even) (X_ij X_(i+1,j+1)+X_(i,j+1) X_(i+1,j)).

Measure c and initially use the zero basis input and J=I. The derivative is `w+Qdet(X)+U_0 V_0`. Its polar is nonsingular on X,U0,V0, so S is exactly that coordinate subspace, with `r=t^2+2`. The first cubic restricted to S is `X_00 U_0 V_0`, so k=1 for every t. The source compiler's complete linear exterior test detects that one-control factor without an anchor promise.

For comparison, suppose a global control space has codimension parameter g and kernel K, with the first cubic tensor zero on K^3. Intersect K with the physical X, U and V subspaces. When g<t, the U and V intersections each have dimension at least t-g, while K intersect X has codimension at most g in the matrix space. Tensor vanishing forces each such matrix to annihilate the tensor product of those U,V intersections under the pairing `u^T X v`. That tensor product has dimension at least `(t-g)^2`, but its annihilator constraint has dimension at most g. Therefore

    (t-g)^2 <= g,          g >= t-sqrt(t).

The same obstruction applies to the recorded global two-copy certificate, because all X directions lie in S. Thus the fixed global-control construction has growing g while the output-restricted construction uses k=1. This says nothing about the minimum unrestricted stabilizer rank or all possible simulation algorithms.

The unperturbed output is

    p = 1/4 - 2^(-t-1) + 2^(-2t-1) < 1/4.

Adding the output linear term to f1 complements p and gives the opposite constant promise. This exact formula supplies a reference, not evidence that the source encodes a hard language.

| t | n | r | Restricted k | Generic Pauli variance bound | Global-control lower bound |
|---|---:|---:|---:|---:|---|
| 2 | 10 | 6 | 1 | `2^6` | `g >= 2-sqrt(2)` |
| 4 | 26 | 18 | 1 | `2^18` | `g >= 2` |
| 6 | 50 | 38 | 1 | `2^38` | `g >= 6-sqrt(6)` |
| 8 | 82 | 66 | 1 | `2^66` | `g >= 8-sqrt(8)` |

These are analytic parameter statements. The new norm reader's complete executed runs in the receipt reach 11 qubits, not 82. Earlier R05-29 executions at larger sizes concern the retained coherent reader.

## Variations beyond the closed-form outputs

Arbitrary quadratic and affine additions to f0 preserve its cubic tensor and hence both the restricted certificate and the global-control obstruction. Arbitrary lower-degree additions to f1 change its derivative only by an affine term, preserving the polar and S while possibly changing its affine origin and matching offset. Nonzero basis inputs change linear characters. Invertible physical coordinate changes preserve the tensor/space conditions, with the Fourier matrix transformed as required by the native grammar. The complete theorem covers these variants even when the displayed formula for p no longer applies.

One may also add cubic terms to f0 whose cubic tensor restricts to zero on S, for example a factor vanishing on S times a quadratic. Restricted k remains one. Such additions can change the global obstruction, so the global lower bound is not asserted for every member of that larger class. These variations are encoded in source coefficients and fully verified by the compiler; a supplied hidden basis is not accepted as a discovery oracle.

The finite suite includes mixed phases, a nonzero input, a hidden coordinate transform, nonzero matching offset, two restricted controls and three restricted controls. Exact full-state references use the literal circuit or an independent integer Fourier-state evolution. The receipt stores each descriptor so the two readouts can be reproduced on identical data. No simple-family formula is substituted for an unknown perturbed output.

## Actual small-control comparison

For h=2 and any executed sampled b, the retained reader uses `8*4^b` sectors and `4^k` real Gaussian sums per sector. The new reader uses `224*4^b` joint samples and `4*2^k` real Gaussian sums per sample. Consequently its prescribed Gaussian-call count divided by the retained count is exactly

    112 / 2^k.

It is 56 at k=1, 28 at k=2 and 14 at k=3. The exact quadratic shortcut is unchanged at one real Gaussian call and no randomness. The new Gaussian widths are r-k and 2r-k, versus 2r-2k for the retained sector pairs; calls are therefore not identical work units either. The exponent improvement is real, but the executed examples do not demonstrate a practical win. The crossover of these call budgets alone occurs at k>=7; that arithmetic is not a measured speed crossover and does not include the potentially dominant source search.

The checker records shared native recognition/discovery time once, separate norm preparation, and separate readout observations for both methods at the same b,h. These single local observations include interpreter/machine effects and are not a performance benchmark. It verifies the returned values against independent exact references and preserves the less favorable norm-reader operation counts. High-precision audits inspect integer schedules and refuse before any sampling; they are not full high-b executions.

## Publication consequence

The output-dependent structural parameter gives a concrete difference from generic Pauli absolute-mass and specified global-control certificates on a growing family, with complete original-source recognition. Existing conditional covering already exploits that parameter; S175 refines its readout exponent using a known norm primitive. The useful publication is the self-contained construction, honest cost/precision theorem, broadened variations and reproducible comparison, not an empirical quantum-advantage or simulator-leaderboard claim.

Proceed to S177 as a bounded methods preprint. Keep the elementary-formula baseline, the small-k disadvantage and the discovery exponent visible in the manuscript. Novelty/priority beyond the exact comparison in S174 remains uncertified, and the universal BPP/BQP objective remains separate.

Remaining to-do list: prepare the self-contained S177 manuscript and public reproduction package, then verify the dedicated S179 repository and notify Dan for Zenodo hookup.
