# Byte-canonical modeled recognition

Target: source interface in section 2 of https://doi.org/10.5281/zenodo.23754698.
SHA-256 `lean/SectorSimulation/ByteCanonicalRecognizer.lean`: `9e575fd730639e1129792b8ad35235368b8e5389f3dcb12384a85703755bbce4`.
SHA-256 `tools/check_python_lean_bridge.py`: `b763b44a0ea65eea241c4a53ee8dd80f6bd4fc2890a3c494500592cc31c8f500`.

The locked Lean 4.30.0 build passed (116 jobs); each of the three declarations uses `[propext, Classical.choice, Quot.sound]`. The modeled recognizer compares numeric header bytes to the UTF-8 bytes of Lean Json.compress applied to the constructed raw descriptor JSON value, requires canonical phase masks and delegates to the exact-body recognizer. Acceptance implies the prior native replay and derivative guarantees; completeness is conditional on byte equality and existing recognition. Five Python-compiled cases pass. An equivalent JSON header with spaces is accepted by the phase-only model but rejected by both Python and the byte-gated model.

Lean Json.compress is a library partial definition; no general parser/serializer round trip or Lean/Python serializer equivalence is proved. These examples do not prove implementation correspondence. Physical Fourier and complex semantics, input preparation, full costs and all manuscript theorem labels remain open.
