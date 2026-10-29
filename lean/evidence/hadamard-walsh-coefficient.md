# Closed exact all-wire Hadamard Walsh sum

Target: Fourier bridge in section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/HadamardWalshCoefficient.lean` SHA-256 `61efa01998f62497750f38aa3429ccad2d0136cb9e64b16506cb02dc0e9d267a`.

The locked Lean 4.30.0 build passed (128 jobs); six declarations have exact transitive axioms in the project audit baseline. For duplicate-free wires, Lean proves the selected-path coefficient is the original exact amplitude multiplied by one exact Hadamard scale per wire, with sign given by the XOR of input/output bit products. It derives the all-wire finite Walsh-character sum and connects it to exact replay of the Python-ordered modeled Fourier records for a successful Gaussian program, including width zero. The scale is represented as repeated multiplication by the project's exact Hadamard scale, whose square-normalization was established separately.

The sum remains in the project's exact cyclotomic quotient; its embedding into standard complex amplitudes, identification of the CNOT action with the manuscript pairing kernel, actual Python refinement, physical output/sector identities and resource costs are not yet proved. This is not the manuscript's quadratic Walsh-support lemma or certification of any labeled paper theorem.
