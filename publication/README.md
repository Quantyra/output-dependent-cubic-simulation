# First publication and DOI sequence

The prepared target is `Quantyra/output-dependent-cubic-simulation`, version `0.1.0`. Dan will enable this actual repository in Zenodo; no release is triggered during repository preparation.

1. Verify the exact pushed candidate, public PDF/source, metadata, author/license choices, hash inventory and reproduction receipt. Record the scientific release decision for that commit.
2. Dan enables the repository in [Zenodo's GitHub settings](https://zenodo.org/account/settings/github/). Confirm the connection before creating a release.
3. Freeze the approved commit under `v0.1.0`, attach the exact manuscript PDF, and publish the authorized GitHub release. The root `.zenodo.json` describes the **source/software companion**, including the paper's separate CC BY license. Verify actual ingestion rather than assuming that a tag succeeded.
4. Publish the **canonical PDF-first paper deposit** using `zenodo-paper.json`, the exact PDF, and the verified source-companion relation. This is a publication/preprint record under CC BY 4.0. A GitHub archive alone does not satisfy the paper gate. Do not create duplicate paper DOI series.
5. Download the public PDF and compare SHA-256 to the frozen manuscript. Record the paper version DOI, paper concept DOI, source-companion DOI(s), record URLs, release URL/tag/commit and hashes in a publication receipt. A reserved identifier or draft is not a published record.
6. Apply the verified paper DOI to the preferred citation, README and citation instructions; link the companion record separately. Keep the frozen PDF/tag unchanged; later PDF changes require a successor version.
7. Only after the manuscript is published and its verified paper DOI is applied, open the Lean work described in [LEAN-PLAN.md](LEAN-PLAN.md).

No publication date, DOI, reserved identifier or ingestion result is prefilled. `zenodo-paper.json` is prepared metadata, not an assertion that a deposit exists. If a single-record workflow is later verified to expose the standalone paper PDF with the correct publication metadata, document that decision before creating a second record.

Zenodo uses `.zenodo.json` when both it and `CITATION.cff` are present; see [its documentation](https://help.zenodo.org/docs/github/describe-software/zenodo-json/). CI runs build/check tasks only and does not publish releases or call Zenodo.
