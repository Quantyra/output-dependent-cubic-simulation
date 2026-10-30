import SectorSimulation.PairColumnsOrthogonal
namespace SectorSimulation

theorem clearPairColumns_preserves_prior {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v j : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (hu : u ∉ ts) (hv : v ∉ ts) (hj : j ∉ ts) (hn : ts.Nodup)
    (huj : B (matrixColumn J u) (matrixColumn J j) = false)
    (hvj : B (matrixColumn J v) (matrixColumn J j) = false) :
    ∀ t ∈ ts, B (matrixColumn (clearPairColumns B u v ts J).1 t) (matrixColumn J j) =
      B (matrixColumn J t) (matrixColumn J j) := by
  induction ts generalizing J with
  | nil => simp
  | cons a rest ih =>
    have hu' : u ≠ a ∧ u ∉ rest := by simpa using hu
    have hv' : v ≠ a ∧ v ∉ rest := by simpa using hv
    have hj' : j ≠ a ∧ j ∉ rest := by simpa using hj
    have hn' := List.nodup_cons.mp hn
    let K := clearPairColumn B J a u v
    have hku : matrixColumn K u = matrixColumn J u := clearPairColumn_other B J a u v u hu'.1
    have hkv : matrixColumn K v = matrixColumn J v := clearPairColumn_other B J a u v v hv'.1
    have hkj : matrixColumn K j = matrixColumn J j := clearPairColumn_other B J a u v j hj'.1
    have hka : B (matrixColumn K a) (matrixColumn J j) = B (matrixColumn J a) (matrixColumn J j) := by
      dsimp [K]
      rw [clearPairColumn_target B J a u v (Ne.symm hu'.1) (Ne.symm hv'.1)]
      exact clearPolarPair_preserves B _ _ _ _ hadd hzero huj hvj
    intro t ht
    simp only [List.mem_cons] at ht
    simp only [clearPairColumns]
    change B (matrixColumn (clearPairColumns B u v rest K).1 t) (matrixColumn J j) = _
    rcases ht with hta | ht
    · subst t
      rw [clearPairColumns_other B u v a rest K hn'.1]
      exact hka
    · have h := ih K hu'.2 hv'.2 hj'.2 hn'.2 (by simpa [hku, hkj] using huj)
          (by simpa [hkv, hkj] using hvj) a ha
        simpa [hkj, hka] using h
      · rw [clearPairColumns_other B u v a rest K ha]
        exact hka
    · have h := ih K hu'.2 hv'.2 hj'.2 hn'.2 (by simpa [hku, hkj] using huj)
        (by simpa [hkv, hkj] using hvj) t ht
      have hother : matrixColumn K t = matrixColumn J t := by
        by_cases heq : t = a
        · subst t; exact False.elim (hn'.1 ht)
        · exact clearPairColumn_other B J a u v t heq
      simpa [hkj, hother] using h
end SectorSimulation
#print axioms SectorSimulation.clearPairColumns_preserves_prior
