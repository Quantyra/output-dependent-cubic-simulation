# Exact-amplitude distributivity

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactDistributivity.lean` SHA-256 `a6764c6726de52c63b58235e5d86516903e4ee73113c12043728342828c09535`.

The locked Lean 4.30.0 build passed (119 jobs); all five declarations have exact transitive axioms in the project audit baseline. Lean proves cyclotomic scaling and multiplication identities, dyadic distributivity up to the existing equivalence, and both left and right distributivity in the exact-amplitude quotient. This closes the distributivity gap recorded in the previous increment.

The closed normalized Walsh-sum formula, complex embedding, Python correspondence, circuit-to-sector identities, costs and all paper theorem labels remain open.
