# Sources and provenance

The manuscript is a self-contained consolidation of the restricted sector construction and its joint norm refinement. Its technical baseline is `75694fa51add1c5293168349c4d29af9ef4030ea`; the integrated norm/comparison evidence is `9dc9391292e31c8b6fafb5b53db47899974a858a`. The exact manuscript export commit, file origins, last-change commits and SHA-256 values are in [PROVENANCE.json](PROVENANCE.json). The originating research repository remains private; it is not needed to reproduce the documented command.

The 67 Python modules are the transitive local import closure of the production norm reader and its checker. Some dependency modules also contain earlier research functions or standalone check entrypoints. Their inclusion preserves imports and provenance; the publication does not claim those other entrypoints as verified public interfaces. No unrelated research history, credential, private inbox or research dataset is exported.

The three `evidence/` notes are dated historical research records. Their then-remaining planning tasks are historical; the current paper and this repository's review/release records govern the candidate. In the norm note, one predecessor link is redirected to the self-contained manuscript; that transformation is recorded. No third-party paper text or source code is bundled.

The primary works consulted, with version and statement anchors, are:

| Source | Used here |
|---|---|
| [Maslov et al., arXiv:2402.03211v1](https://arxiv.org/abs/2402.03211v1), Section II | Conditional covering sets and quadratic sums |
| [Bläser et al., arXiv:2609.39918v1](https://arxiv.org/abs/2609.39918v1), Definition 1, Theorems 41 and 67 | Independent-space condition, supplied-space evaluation and planted-model comparison |
| [Park, Kwon and Jeong, arXiv:2307.16688v2](https://arxiv.org/abs/2307.16688v2), supplement IV.3, Theorem 4 | Prior output-dependent marginal methods and their input/access hypotheses |
| [Van den Nest, arXiv:0911.1624v3](https://arxiv.org/abs/0911.1624v3), Sections 4.1 and 4.3 | Tractable states and sparse-operator interface |
| [Bravyi et al., arXiv:1808.00128v2](https://arxiv.org/abs/1808.00128v2), Section 4.3 | Equatorial norm estimator and linear decomposition-length work |
| [Zhang and Zhang, arXiv:2409.13809v2](https://arxiv.org/abs/2409.13809v2), IV.1, Algorithm 1 | Explicit normalized-Pauli baseline reduction |

Bibliographic metadata was checked against these primary records. The paper's deductions and comparisons are not statements of endorsement by those authors or a priority certificate.

Archive metadata follows [Zenodo's GitHub documentation](https://help.zenodo.org/docs/github/describe-software/zenodo-json/). Its `.zenodo.json` overrides `CITATION.cff` during GitHub ingestion. License texts are obtained from [Apache](https://www.apache.org/licenses/LICENSE-2.0.txt) and [Creative Commons](https://creativecommons.org/licenses/by/4.0/legalcode.txt).
