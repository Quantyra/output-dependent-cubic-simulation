# Multi-wire exact Hadamard basis branching

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardBasisBranching.lean` SHA-256 `497389c50dea598ce23a24230c87a6b323fcc59836d828b3d4a1636fa626409c`.

The locked Lean 4.30.0 build passed (125 jobs); all four declarations use `[propext, Classical.choice, Quot.sound]`. Lean proves a one-wire point input splits into two point-supported branches with exact scale and signs, and proves that arbitrary later wire sequences distribute over them. The resulting recursive binary branch expression equals the exact kernel for every point input, and its sum over the explicit binary basis equals the kernel on any exact-amplitude function. Repeated and empty wire lists are included.

The binary path expansion is not yet simplified to the closed Walsh-character formula, embedded in complex amplitudes, or assigned an efficient cost. Python correspondence, sector identities, costs and all paper theorem labels remain open.
