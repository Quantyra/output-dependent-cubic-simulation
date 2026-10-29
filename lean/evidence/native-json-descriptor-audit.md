# Modeled two-phase JSON descriptor validation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeJsonDescriptor.lean` SHA-256 `7297cb6c2a2d5e7bf06707c10f8a047cfc0be7c046b48205be0da22b0df2fdb9`.

Lean 4.30.0 with locked dependencies: `lake build` passed (50 jobs); `NativeJsonExamples.lean` checked actual-format valid input, a singular descriptor, a numeric header with an arbitrary retained body, and non-ASCII rejection. Both audited declarations depend on `[propext, Classical.choice, Quot.sound]`. Any descriptor returned by the modeled conversion or by the composed numeric-header, ASCII and Lean JSON pipeline satisfies `sourceDescriptorValid`.

This is a conditional validation result for the Lean model, not a completeness result or proof of equivalence to Python JSON parsing, byte handling, normalization or its size guard. The retained gate body is not checked against the compiler. Gate semantics, operational cost and all labeled manuscript theorems remain open.
