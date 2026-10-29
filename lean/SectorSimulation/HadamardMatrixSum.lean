import SectorSimulation.HadamardWalshCoefficient
namespace SectorSimulation

theorem matrixApply_inverse_forward {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (x : BinaryVector n) :
    matrixApply J (runCNOTs (rowProgramCNOTs ops) x) = x := by
  have h := runCNOTs_reverse_cancels (rowProgramCNOTs ops) x (rowProgramCNOTs_valid ops)
  rw [gaussianCNOTs_reversed_implements_matrix J ops hp] at h
  exact h

theorem matrixApply_basis_perm {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops) :
    ((binaryBasis n).map (matrixApply J)).Perm (binaryBasis n) := by
  have hinj : Function.Injective (matrixApply J) := by
    intro a b h
    have h' := congrArg (runCNOTs (rowProgramCNOTs ops)) h
    simpa only [gaussianCNOTs_forward_inverse J ops hp] using h'
  have hn : ((binaryBasis n).map (matrixApply J)).Nodup := by
    exact List.Pairwise.map _ (fun _ _ h h' => h (hinj h')) (binaryBasis_nodup n)
  apply List.perm_iff_count.mpr
  intro x
  rw [hn.count, (binaryBasis_nodup n).count]
  have hm : x ∈ (binaryBasis n).map (matrixApply J) :=
    List.mem_map.mpr ⟨runCNOTs (rowProgramCNOTs ops) x, binaryBasis_complete _, matrixApply_inverse_forward J ops hp x⟩
  simp [hm, binaryBasis_complete]

theorem exactFoldr_perm {α : Type} (xs ys : List α) (h : xs.Perm ys)
    (f : α → ExactAmplitude) :
    xs.foldr (fun a acc => exactAdd (f a) acc) exactZero =
    ys.foldr (fun a acc => exactAdd (f a) acc) exactZero := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [List.foldr_cons, ih]
  | swap a b xs => simp only [List.foldr_cons, exactAdd_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem nativePythonFourier_matrix_sum {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (pythonFourierRecords ops) state = some result ∧
      ∀ x, sharedAmplitude result x =
        (binaryBasis n).foldr (fun basis acc => exactAdd
          (exactSigned (walshWireParity (List.finRange n) (matrixApply J basis) x)
            (iterateHadamardScale n (sharedAmplitude state basis))) acc) exactZero := by
  obtain ⟨result, hr, hf⟩ := nativePythonFourier_walsh_sum J ops hp state
  refine ⟨result, hr, ?_⟩
  intro x
  rw [hf x]
  have h := exactFoldr_perm _ _ (matrixApply_basis_perm J ops hp).symm
    (fun basis => exactSigned (walshWireParity (List.finRange n) basis x)
      (iterateHadamardScale n (sharedAmplitude state (runCNOTs (rowProgramCNOTs ops) basis))))
  simpa only [List.foldr_map, gaussianCNOTs_forward_inverse J ops hp] using h

end SectorSimulation
