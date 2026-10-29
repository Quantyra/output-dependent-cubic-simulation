# Lean certification after first publication

Status: active target freeze after first publication, verified paper DOI and application of the DOI to citation surfaces. No manuscript theorem is certified yet. The initial preprint did not wait for formalization.

The initial target is the exact published PDF and source. Preserve its hashes and map each stable LaTeX statement label to its mathematical statement, hypotheses, intended declaration and evidence. Confirm a Lean/mathlib toolchain at that time and commit its pins; no placeholder Lean project is represented as certification.

| Dependency stage | Target | Acceptance evidence |
|---|---|---|
| Freeze published target | Actual paper DOI, tag, commit, PDF hash and scope matrix | Published receipt and statement inventory; corrections separated from original |
| Source and sector algebra | Boolean polynomial semantics, Fourier normalization, Walsh support, Clifford kernel, matched-sector identity | Declarations matching Lemma 2.1 and Proposition 2.2, including origins/inputs/lower terms |
| Control discovery | Independent spaces, conditional branches, exterior shortcuts, contraction image, Pfaffian density and capped search | Lemma 3.1 / Theorem 3.2 and explicit algorithm/semantic bridges; promise not silently weakened |
| Estimator and costs | Equatorial moments, joint variance, independence, median amplification, finite arithmetic, rounding and resource bounds | Lemma 4.1 / Theorem 4.2 / Section 5; probabilistic algorithm and bit-cost model made explicit |
| Families and limits | Determinant family, global certificate bound, exact output formula, restricted-control obstruction | Proposition 6.1 and subsequent bounds with every scope qualification |
| Certification audit and successor release | Complete coverage and any corrections | Reproducible build, declaration/axiom audit, no `sorry` or hidden unproved target assumptions, checked statement bridges and honest residual scope |

Formal helpers do not by themselves certify the paper. Imported assumptions, external theorems, execution semantics and unformalized bridges must be listed. If a proof is conditional, the release must call it conditional. A successful Lean build does not establish novelty, practical performance, the correctness of the Python implementation, or universal BPP/BQP consequences.

Once the intended mathematical coverage is complete, prepare a successor manuscript version with the declaration map, exact formal commit, toolchain and audit evidence. Preserve the first archived preprint and explain corrections. The planning workstream tracks these stages as S181-S186 under E004, after first publication S180.
