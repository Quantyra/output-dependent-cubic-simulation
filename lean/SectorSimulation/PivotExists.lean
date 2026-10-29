import SectorSimulation.PivotInjectivity
namespace SectorSimulation

def lowerPivotVector {n : Nat} (J : BinaryMatrix n) (p : Fin n) : BinaryVector n :=
  fun k => if k.val < p.val then J k p else false

theorem matrixApply_basis {n : Nat} (J : BinaryMatrix n) (p : Fin n) :
    matrixApply J (singletonMask p) = fun r => J r p := by
  funext r
  simpa [matrixApply, singletonMask, Bool.and_comm, eq_comm] using
    identityFold_present (List.finRange n) p (J r) (List.nodup_finRange n) (List.mem_finRange p)

theorem matrixApply_lowerPivot {n : Nat} (J : BinaryMatrix n) (p : Fin n)
    (hprior : ∀ k, k.val < p.val → ∀ r, J r k = decide (r = k)) :
    matrixApply J (lowerPivotVector J p) = lowerPivotVector J p := by
  have heq : matrixApply J (lowerPivotVector J p) = matrixApply identityMatrix (lowerPivotVector J p) := by
    funext r
    unfold matrixApply
    apply congrArg (fun f => (List.finRange n).foldl f false)
    funext acc k
    by_cases hk : k.val < p.val
    · simp [identityMatrix, hprior k hk r]
    · simp [lowerPivotVector, hk]
  rw [heq, matrixApply_identity]

theorem pivot_exists_of_injective {n : Nat} (J : BinaryMatrix n) (p : Fin n)
    (hinj : ∀ x z, matrixApply J x = matrixApply J z → x = z)
    (hprior : ∀ k, k.val < p.val → ∀ r, J r k = decide (r = k)) :
    ∃ row, findPivot J p = some row := by
  cases hf : findPivot J p with
  | some row => exact ⟨row, rfl⟩
  | none =>
    let lower := lowerPivotVector J p
    let witness := vectorXor (singletonMask p) lower
    have hlow : matrixApply J lower = lower := matrixApply_lowerPivot J p hprior
    have hbas : matrixApply J (singletonMask p) = fun r => J r p := matrixApply_basis J p
    have hz : matrixApply J witness = zeroVector := by
      rw [show witness = vectorXor (singletonMask p) lower from rfl, matrixApply_xor, hlow, hbas]
      funext r
      by_cases hr : r.val < p.val
      · simp [vectorXor, lower, lowerPivotVector, zeroVector, hr]
      · have hr2 : p.val ≤ r.val := by omega
        have hv := findPivot_none J p hf r hr2
        simp [vectorXor, lower, lowerPivotVector, zeroVector, hr, hv]
    have hw : witness = zeroVector := hinj witness zeroVector (by rw [hz, matrixApply_zero])
    have hc := congrFun hw p
    simp [witness, vectorXor, singletonMask, lower, lowerPivotVector, zeroVector] at hc

end SectorSimulation
