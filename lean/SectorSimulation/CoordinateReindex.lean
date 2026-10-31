import SectorSimulation.RecordedMapUnpaired
namespace SectorSimulation

def coordinateReindex {n : Nat} (f : Fin n → Fin n) (x : BinaryVector n) : BinaryVector n :=
  fun i => x (f i)

theorem coordinateReindex_basis_perm {n : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f) (hsurj : ∀ x, ∃ i, f i = x) :
    ((binaryBasis n).map (coordinateReindex f)).Perm (binaryBasis n) := by
  have hvi : Function.Injective (coordinateReindex f) := by
    intro a b hab; funext j
    obtain ⟨i, hi⟩ := hsurj j
    have h := congrFun hab i
    simpa [coordinateReindex, hi] using h
  have hn : ((binaryBasis n).map (coordinateReindex f)).Nodup := by
    exact List.Pairwise.map _ (fun _ _ h h' => h (hvi h')) (binaryBasis_nodup n)
  apply List.perm_iff_count.mpr
  intro x
  rw [hn.count, (binaryBasis_nodup n).count]
  let inv := fun j => Classical.choose (hsurj j)
  have hinv : ∀ j, f (inv j) = j := fun j => Classical.choose_spec (hsurj j)
  have hleft : ∀ i, inv (f i) = i := fun i => hinj (hinv (f i))
  have hm : x ∈ (binaryBasis n).map (coordinateReindex f) := by
    apply List.mem_map.mpr
    refine ⟨fun j => x (inv j), binaryBasis_complete _, ?_⟩
    funext i
    simp [coordinateReindex, hleft]
  simp [hm, binaryBasis_complete]

theorem coordinateReindex_sum {n : Nat} (f : Fin n → Fin n)
    (hinj : Function.Injective f) (hsurj : ∀ x, ∃ i, f i = x)
    (g : BinaryVector n → Int) :
    ((binaryBasis n).map g).sum = ((binaryBasis n).map (fun x => g (coordinateReindex f x))).sum := by
  have h := integerSum_perm _ _ (coordinateReindex_basis_perm f hinj hsurj).symm g
  simpa [List.map_map, Function.comp_def] using h



end SectorSimulation