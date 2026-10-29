# Executable source phase compiler

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PhaseBlockCompiler.lean` SHA-256 `5b629fbb976b74b6ccf1bbc5fdb5a7b3de3f6c26a57917485d99637cffb15ead`.

The locked Lean 4.30.0 build passed (95 jobs); the two ideal block numerator and exponent declarations use `[propext]`, and the other five use `[propext, Classical.choice, Quot.sound]`. The executable `compilePhaseRecords` function classifies selected mask supports, generates native records, and for every degree-at-most-three phase and available anchor wire is proved to return records whose replay succeeds and implements the source Boolean ANF sign on every represented state and output vector. Finite examples check mixed linear/cubic compilation, empty input and rejection of a degree-four mask; CI runs them.

This is a Lean compiler and modeled interpreter theorem, not Python compiler equivalence. Zero-wire constants, complex embedding, complete circuit behavior, costs and all labeled manuscript theorems remain open.
