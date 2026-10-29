import SectorSimulation.HadamardBasisBranching
namespace SectorSimulation

theorem basisBranchExpansion_untouched_zero {n : Nat} (wires : List (Fin n))
    (c : ExactAmplitude) (basis x : BinaryVector n) (wire : Fin n)
    (hw : wire ∉ wires) (hx : x wire ≠ basis wire) :
    basisBranchExpansion wires c basis x = exactZero := by
  have h := hadamardKernel_basis_support wires (fun _ => c) basis x wire hw hx
  simpa only [hadamardKernel_basis_branchExpansion] using h

/-- For a wire absent from the tail, the output bit selects the only live branch. -/
theorem basisBranchExpansion_select {n : Nat} (wire : Fin n) (rest : List (Fin n))
    (c : ExactAmplitude) (basis x : BinaryVector n) (hw : wire ∉ rest) :
    basisBranchExpansion (wire :: rest) c basis x =
      if x wire = basis wire then
        basisBranchExpansion rest (if basis wire then exactNeg (exactMul exactHadamardScale c)
          else exactMul exactHadamardScale c) basis x
      else basisBranchExpansion rest (exactMul exactHadamardScale c) (flipWire wire basis) x := by
  by_cases he : x wire = basis wire
  · have hd : x wire ≠ (flipWire wire basis) wire := by
      rw [he]
      simp [flipWire]
    have hz := basisBranchExpansion_untouched_zero rest (exactMul exactHadamardScale c)
      (flipWire wire basis) x wire hw hd
    simp [basisBranchExpansion, he, hz, exactAdd_zero]
  · have hz := basisBranchExpansion_untouched_zero rest
      (if basis wire then exactNeg (exactMul exactHadamardScale c) else exactMul exactHadamardScale c)
      basis x wire hw he
    simp [basisBranchExpansion, he, hz, exactZero_add]

def basisSelectedPath {n : Nat} : List (Fin n) → ExactAmplitude → BinaryVector n →
    BinaryVector n → ExactAmplitude
  | [], c, basis, x => if x = basis then c else exactZero
  | wire :: rest, c, basis, x =>
    if x wire = basis wire then
      basisSelectedPath rest (if basis wire then exactNeg (exactMul exactHadamardScale c)
        else exactMul exactHadamardScale c) basis x
    else basisSelectedPath rest (exactMul exactHadamardScale c) (flipWire wire basis) x

theorem basisBranchExpansion_uniquePath {n : Nat} (wires : List (Fin n))
    (c : ExactAmplitude) (basis x : BinaryVector n) (hn : wires.Nodup) :
    basisBranchExpansion wires c basis x = basisSelectedPath wires c basis x := by
  induction wires generalizing c basis with
  | nil => rfl
  | cons wire rest ih =>
    have hs := List.nodup_cons.mp hn
    rw [basisBranchExpansion_select wire rest c basis x hs.1]
    simp only [basisSelectedPath]
    split <;> apply ih <;> exact hs.2

theorem hadamardKernel_basis_uniquePath {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (basis x : BinaryVector n) (hn : wires.Nodup) :
    hadamardKernel wires (basisTerm f basis) x = basisSelectedPath wires (f basis) basis x := by
  rw [hadamardKernel_basis_branchExpansion, basisBranchExpansion_uniquePath wires _ _ _ hn]


theorem hadamardKernel_uniquePath_sum {n : Nat} (wires : List (Fin n))
    (f : BinaryVector n → ExactAmplitude) (x : BinaryVector n) (hn : wires.Nodup) :
    hadamardKernel wires f x =
      (binaryBasis n).foldr
        (fun basis acc => exactAdd (basisSelectedPath wires (f basis) basis x) acc) exactZero := by
  have h := hadamardKernel_branchExpansion wires f x
  simpa only [basisBranchExpansion_uniquePath wires _ _ _ hn] using h

end SectorSimulation
