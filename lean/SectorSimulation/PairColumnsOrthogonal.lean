import SectorSimulation.PairColumnInvariant
namespace SectorSimulation

theorem clearPairColumns_orthogonal {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n)
    (hadd : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z))
    (hzero : ∀ z, B (fun _ => false) z = false)
    (huu : B (matrixColumn J u) (matrixColumn J u) = false)
    (hvv : B (matrixColumn J v) (matrixColumn J v) = false)
    (huv : B (matrixColumn J u) (matrixColumn J v) = true)
    (hvu : B (matrixColumn J v) (matrixColumn J u) = true)
    (hu : u ∉ ts) (hv : v ∉ ts) (hn : ts.Nodup) :
    ∀ t ∈ ts, B (matrixColumn (clearPairColumns B u v ts J).1 t) (matrixColumn J u) = false ∧
      B (matrixColumn (clearPairColumns B u v ts J).1 t) (matrixColumn J v) = false := by
  induction ts generalizing J with
  | nil => simp
  | cons a rest ih =>
    have hu' : u ≠ a ∧ u ∉ rest := by simpa using hu
    have hv' : v ≠ a ∧ v ∉ rest := by simpa using hv
    have hn' := List.nodup_cons.mp hn
    let K := clearPairColumn B J a u v
    have hku : matrixColumn K u = matrixColumn J u := clearPairColumn_other B J a u v u hu'.1
    have hkv : matrixColumn K v = matrixColumn J v := clearPairColumn_other B J a u v v hv'.1
    intro t ht
    simp only [List.mem_cons] at ht
    simp only [clearPairColumns]
    change B (matrixColumn (clearPairColumns B u v rest K).1 t) (matrixColumn J u) = false ∧
      B (matrixColumn (clearPairColumns B u v rest K).1 t) (matrixColumn J v) = false
    rcases ht with hta | ht
    · subst t
      rw [clearPairColumns_other B u v a rest K hn'.1]
      dsimp [K]
      rw [clearPairColumn_target B J a u v (Ne.symm hu'.1) (Ne.symm hv'.1)]
      exact clearPolarPair_orthogonal B _ _ _ hadd hzero huu hvv huv hvu
    · have h := ih K (by simpa [hku] using huu) (by simpa [hkv] using hvv)
        (by simpa [hku, hkv] using huv) (by simpa [hku, hkv] using hvu)
        hu'.2 hv'.2 hn'.2 t ht
      simpa [hku, hkv] using h

end SectorSimulation
