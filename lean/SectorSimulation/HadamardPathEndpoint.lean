import SectorSimulation.HadamardUniquePath
namespace SectorSimulation

def alignPathWire {n : Nat} (wire : Fin n) (basis x : BinaryVector n) : BinaryVector n :=
  if x wire = basis wire then basis else flipWire wire basis

def selectedPathFinal {n : Nat} : List (Fin n) → BinaryVector n → BinaryVector n → BinaryVector n
  | [], basis, _ => basis
  | wire :: rest, basis, x => selectedPathFinal rest (alignPathWire wire basis x) x

def selectedPathCoefficient {n : Nat} : List (Fin n) → ExactAmplitude → BinaryVector n →
    BinaryVector n → ExactAmplitude
  | [], c, _, _ => c
  | wire :: rest, c, basis, x =>
    if x wire = basis wire then
      selectedPathCoefficient rest (if basis wire then exactNeg (exactMul exactHadamardScale c)
        else exactMul exactHadamardScale c) basis x
    else selectedPathCoefficient rest (exactMul exactHadamardScale c) (flipWire wire basis) x

theorem alignPathWire_at {n : Nat} (wire i : Fin n) (basis x : BinaryVector n) :
    alignPathWire wire basis x i = if i = wire then x i else basis i := by
  by_cases he : i = wire
  · subst i
    cases hb : basis wire <;> cases hx : x wire <;> simp [alignPathWire, flipWire, hb, hx]
  · by_cases hx : x wire = basis wire <;> simp [alignPathWire, flipWire, he, hx]

theorem selectedPathFinal_at {n : Nat} (wires : List (Fin n))
    (basis x : BinaryVector n) (i : Fin n) :
    selectedPathFinal wires basis x i = if i ∈ wires then x i else basis i := by
  induction wires generalizing basis with
  | nil => rfl
  | cons wire rest ih =>
    simp only [selectedPathFinal, ih, alignPathWire_at, List.mem_cons]
    by_cases hi : i = wire <;> by_cases hr : i ∈ rest <;> simp [hi, hr]

theorem selectedPathFinal_all {n : Nat} (basis x : BinaryVector n) :
    selectedPathFinal (List.finRange n) basis x = x := by
  funext i
  simp [selectedPathFinal_at, List.mem_finRange]

theorem basisSelectedPath_components {n : Nat} (wires : List (Fin n))
    (c : ExactAmplitude) (basis x : BinaryVector n) :
    basisSelectedPath wires c basis x =
      if x = selectedPathFinal wires basis x then selectedPathCoefficient wires c basis x else exactZero := by
  induction wires generalizing c basis with
  | nil => rfl
  | cons wire rest ih =>
    by_cases he : x wire = basis wire <;>
      simp only [basisSelectedPath, selectedPathFinal, selectedPathCoefficient, alignPathWire, he, if_true, if_false, ih]

theorem hadamardKernel_allWire_basis_coefficient {n : Nat}
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) :
    hadamardKernel (List.finRange n) (basisTerm f basis) x =
      selectedPathCoefficient (List.finRange n) (f basis) basis x := by
  rw [hadamardKernel_basis_uniquePath _ _ _ _ (List.nodup_finRange n), basisSelectedPath_components,
    selectedPathFinal_all]
  simp


theorem hadamardKernel_allWire_coefficient_sum {n : Nat}
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) :
    hadamardKernel (List.finRange n) f x =
      (binaryBasis n).foldr (fun basis acc => exactAdd
        (selectedPathCoefficient (List.finRange n) (f basis) basis x) acc) exactZero := by
  have h := hadamardKernel_uniquePath_sum (List.finRange n) f x (List.nodup_finRange n)
  simpa only [basisSelectedPath_components, selectedPathFinal_all, if_true] using h

end SectorSimulation
