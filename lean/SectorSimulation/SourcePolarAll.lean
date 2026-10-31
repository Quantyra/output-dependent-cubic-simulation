import SectorSimulation.SourceCrossAll
import SectorSimulation.PolarUnitExt
import SectorSimulation.SourceMixedUnits
import SectorSimulation.QuadraticSourcePolar
namespace SectorSimulation

theorem assemble_coordinate_cases {n : Nat} (P : Fin n → Fin n → Prop)
    (residual : Fin n → Prop) (pairs : List (Fin n × Fin n))
    (cover : ∀ i, residual i ∨ ∃ p ∈ pairs, i = p.1 ∨ i = p.2)
    (symm : ∀ i j, P i j → P j i) (diag : ∀ i, P i i)
    (rr : ∀ i j, residual i → residual j → P i j)
    (rp : ∀ i p, residual i → p ∈ pairs → P i p.1 ∧ P i p.2)
    (same : ∀ p ∈ pairs, P p.1 p.2)
    (cross : ∀ p q, p ∈ pairs → q ∈ pairs → p ≠ q →
      P p.1 q.1 ∧ P p.1 q.2 ∧ P p.2 q.1 ∧ P p.2 q.2) :
    ∀ i j, P i j := by
  intro i j
  rcases cover i with hi | ⟨p, hp, hi | hi⟩ <;>
  rcases cover j with hj | ⟨q, hq, hj | hj⟩
  · exact rr i j hi hj
  · subst j; exact (rp i q hi hq).1
  · subst j; exact (rp i q hi hq).2
  · subst i; exact symm j p.1 ((rp j p hj hp).1)
  · subst i; subst j
    by_cases h : p = q
    · subst q; exact diag _
    · exact (cross p q hp hq h).1
  · subst i; subst j
    by_cases h : p = q
    · subst q; exact same p hp
    · exact (cross p q hp hq h).2.1
  · subst i; exact symm j p.2 ((rp j p hj hp).2)
  · subst i; subst j
    by_cases h : p = q
    · subst q; exact symm _ _ (same p hp)
    · exact (cross p q hp hq h).2.2.1
  · subst i; subst j
    by_cases h : p = q
    · subst q; exact diag _
    · exact (cross p q hp hq h).2.2.2




theorem sourcePolar_all_units {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (J : BinaryMatrix n)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let indices := List.finRange n
    let out := polarEliminate (phasePolar p) fuel indices J
    ∀ i j, phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit i) (coordinateUnit j) =
      phasePolar (recordedPairPhase out.2.2) (coordinateUnit i) (coordinateUnit j) := by
  dsimp only
  let indices := List.finRange n
  let out := polarEliminate (phasePolar p) fuel indices J
  let C := phasePolar (recordedPairPhase out.2.2)
  obtain ⟨ts, _, _, hp, halt, hadd, _⟩ := sourceQuadratic_hasPolar p hdegree
  have ha : ∀ a b z, phasePolar p (binaryShift a b) z = Bool.xor (phasePolar p a z) (phasePolar p b z) := by
    intro a b z; simp only [hp, hadd]
  have hz : ∀ z, phasePolar p (fun _ => false) z = false := by
    intro z; have hh := ha (fun _ => false) (fun _ => false) z; simpa [binaryShift] using hh
  have hl : ∀ x, phasePolar p x x = false := by intro x; rw [hp]; exact halt x
  have hs : ∀ x y, phasePolar p x y = phasePolar p y x := by intro x y; simp only [hp, termsPolar_symmetric]
  obtain ⟨us, _, _, hc, hcalt, _, _⟩ := sourceQuadratic_hasPolar (recordedPairPhase out.2.2) (recordedPairPhase_degree _)
  have cs : ∀ x y, C x y = C y x := by intro x y; dsimp [C]; simp only [hc, termsPolar_symmetric]
  have ca : ∀ x, C x x = false := by intro x; dsimp [C]; rw [hc]; exact hcalt x
  have cover : ∀ i : Fin n, i ∈ unpairedIndices indices out.2.2 ∨ ∃ q ∈ out.2.2, i = q.1 ∨ i = q.2 := by
    intro i
    by_cases h : ∃ q ∈ out.2.2, i = q.1 ∨ i = q.2
    · exact Or.inr h
    · left; simp [unpairedIndices, indices]; intro a b hab; exact ⟨fun he => h ⟨(a,b), hab, Or.inl he⟩, fun he => h ⟨(a,b), hab, Or.inr he⟩⟩
  let P := fun i j => phasePolarFunction (fun x => evalPhase p (matrixApply out.1 x)) (coordinateUnit i) (coordinateUnit j) = C (coordinateUnit i) (coordinateUnit j)
  have hpairs : ∀ i j, P i j := by
    apply assemble_coordinate_cases P (fun i => i ∈ unpairedIndices indices out.2.2) out.2.2 cover
    · intro i j h; dsimp [P] at *; rw [sourcePolar_units_are_columns] at h ⊢; exact (hs _ _).trans (h.trans (cs _ _))
    · intro i; dsimp [P]; rw [sourcePolar_units_are_columns, hl, ca]
    · intro i j hi hj; exact sourcePolar_residual_units p fuel indices J (by simpa [indices] using hbound) i j hi hj
    · intro i q hi hq; exact sourcePolar_residual_pair_units p fuel indices J ha hz hl hs (List.nodup_finRange n) i q hi hq
    · intro q hq; exact sourcePolar_recorded_pair_units p fuel indices J hl q hq
    · intro a b ha' hb' hne
      exact ⟨sourcePolar_cross_first_units p fuel indices J ha hz hl hs (List.nodup_finRange n) b a hb' ha' (Ne.symm hne),
        sourcePolar_cross_first_second_units p fuel indices J ha hz hl hs (List.nodup_finRange n) b a hb' ha' (Ne.symm hne),
        sourcePolar_cross_second_first_units p fuel indices J ha hz hl hs (List.nodup_finRange n) b a hb' ha' (Ne.symm hne),
        sourcePolar_cross_second_second_units p fuel indices J ha hz hl hs (List.nodup_finRange n) b a hb' ha' (Ne.symm hne)⟩
  exact hpairs



theorem sourcePolar_all_vectors {n : Nat} (p : PhaseANF n)
    (fuel : Nat) (J : BinaryMatrix n)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel) :
    let out := polarEliminate (phasePolar p) fuel (List.finRange n) J
    ∀ u v, phasePolar p (matrixApply out.1 u) (matrixApply out.1 v) =
      phasePolar (recordedPairPhase out.2.2) u v := by
  dsimp only
  let out := polarEliminate (phasePolar p) fuel (List.finRange n) J
  let B := fun u v => phasePolar p (matrixApply out.1 u) (matrixApply out.1 v)
  let C := phasePolar (recordedPairPhase out.2.2)
  obtain ⟨ts, _, _, hp, _, hl, hr⟩ := sourceQuadratic_hasPolar p hdegree
  obtain ⟨us, _, _, hq, _, cl, cr⟩ := sourceQuadratic_hasPolar (recordedPairPhase out.2.2) (recordedPairPhase_degree _)
  have mx : ∀ a b, matrixApply out.1 (binaryShift a b) = binaryShift (matrixApply out.1 a) (matrixApply out.1 b) := by
    intro a b; simpa [binaryShift, vectorXor] using matrixApply_xor out.1 b a
  have bl : ∀ a b z, B (binaryShift a b) z = Bool.xor (B a z) (B b z) := by
    intro a b z; dsimp [B]; rw [mx]; simp only [hp, hl]
  have br : ∀ z a b, B z (binaryShift a b) = Bool.xor (B z a) (B z b) := by
    intro z a b; dsimp [B]; rw [mx]; simp only [hp, hr]
  have ca : ∀ a b z, C (binaryShift a b) z = Bool.xor (C a z) (C b z) := by
    intro a b z; dsimp [C]; simp only [hq, cl]
  have cb : ∀ z a b, C z (binaryShift a b) = Bool.xor (C z a) (C z b) := by
    intro z a b; dsimp [C]; simp only [hq, cr]
  have bz : ∀ z, B (fun _ => false) z = false := by
    intro z; have h := bl (fun _ => false) (fun _ => false) z; simpa [binaryShift] using h
  have bzr : ∀ z, B z (fun _ => false) = false := by
    intro z; have h := br z (fun _ => false) (fun _ => false); simpa [binaryShift] using h
  have cz : ∀ z, C (fun _ => false) z = false := by
    intro z; have h := ca (fun _ => false) (fun _ => false) z; simpa [binaryShift] using h
  have czr : ∀ z, C z (fun _ => false) = false := by
    intro z; have h := cb z (fun _ => false) (fun _ => false); simpa [binaryShift] using h
  have hu : ∀ i j, B (coordinateUnit i) (coordinateUnit j) = C (coordinateUnit i) (coordinateUnit j) := by
    intro i j; dsimp [B, C]; rw [← sourcePolar_matrixChange]; exact sourcePolar_all_units p fuel J hdegree hbound i j
  exact fun u v => bilinear_equal_of_unit_pairs B C bl br bz bzr ca cb cz czr hu u v


end SectorSimulation