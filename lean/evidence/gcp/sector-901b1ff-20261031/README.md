# GCP certification evidence: residual coordinate equations

Source commit: `901b1ff9a4b276aa7fc9601431395234e85b64c2`.

The exact Lean source archive is `sector-901b1ff-source.tar` (SHA-256 `a96acbbe34c5664411f465a71ddb78056d2e27b6f08e9bd94b610d46cbd8c192`, 1,413,120 bytes). It includes tracked Lean sources and the exact audit checker while excluding prior evidence archives. The archive hash was verified on the dedicated builder before compiling.

The dedicated GCP builder `quantyra-sector-lean-builder-02` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`; the pinned `lake-manifest.json` SHA-256 is `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. A full `lake build` completed successfully (2,175 jobs). `lake env lean Audit.lean` and `tools/check_lean_audit.py` both passed. The theorem `sourceWalshSum_recorded_interleaved_cast_ne_zero_iff_residualCoordinates_zero` has transitive axioms `propext`, `Classical.choice`, and `Quot.sound`, within the established audit baseline.

The result states that the source Walsh sum is nonzero exactly when all residual transformed-character coordinates vanish. This is a coordinate-equation characterization only. It does not identify the solution set with `l0 + im(Bq)`, prove the rank formula, normalize the Walsh values, establish sector bounds or costs, or certify any of the seven published paper theorems.
