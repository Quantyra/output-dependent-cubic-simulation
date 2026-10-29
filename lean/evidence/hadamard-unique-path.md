# Unique Hadamard basis path for distinct wires

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardUniquePath.lean` SHA-256 `fb76ec2475c9033894c39d64ecb2806d2ca41ca95ea1e77a871eefcb61511dd7`.

The locked Lean 4.30.0 build passed (126 jobs); all five declarations use `[propext, Classical.choice, Quot.sound]`. For each selected wire absent from the tail, the output bit chooses the sole branch that can contribute; the other branch is zero by untouched-wire support. Consequently, for every duplicate-free wire list, the exact recursive branch expansion collapses to a deterministic selected path, with scales and signs retained. The arbitrary input kernel is the sum of these selected paths over the explicit binary basis.

This does not yet simplify the selected-path coefficient to the closed Walsh dot-product sign and normalization, prove a cost bound, embed amplitudes in complex numbers, establish Python correspondence, sector identities or any paper theorem.
