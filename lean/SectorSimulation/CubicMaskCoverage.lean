import SectorSimulation.CombinedPhaseNative
namespace SectorSimulation

def selectedTriple {n : Nat} (a b c : Fin n) : Fin 3 → Fin n :=
  fun i => if i = 0 then a else if i = 1 then b else c

theorem selectedTriple_values {n : Nat} (a b c : Fin n) :
    selectedTriple a b c 0 = a ∧ selectedTriple a b c 1 = b ∧ selectedTriple a b c 2 = c := by
  simp [selectedTriple]

theorem selectedVariables_nodup {n : Nat} (m : Monomial n) : (selectedVariables m).Nodup := by
  exact List.Nodup.sublist List.filter_sublist (List.nodup_finRange n)

theorem selectedTriple_injective {n : Nat} (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Function.Injective (selectedTriple a b c) := by
  intro i j h
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by have bound := i.isLt; omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by have bound := j.isLt; omega
  rcases hi with hi | hi | hi <;> rcases hj with hj | hj | hj <;> subst i <;> subst j <;>
    simp_all [selectedTriple, Ne.symm]

theorem cubicMask_supported_block {n : Nat} (anchor : Fin n) (m : Monomial n) (degree : monomialDegree m ≤ 3) :
    (∃ term : LowerPhaseTerm n, term.valid ∧ ∀ x, evalMonomial m x = evalMonomial (lowerPhaseMask term) x) ∨
    (∃ w : Fin 3 → Fin n, Function.Injective w ∧ ∀ x, evalMonomial m x = evalMonomial (tripleMask w) x) := by
  have nodup := selectedVariables_nodup m
  rcases cubicMask_selected_shape m degree with h0 | ⟨a,h1⟩ | ⟨a,b,h2⟩ | ⟨a,b,c,h3⟩
  · left; refine ⟨LowerPhaseTerm.constant anchor, trivial, ?_⟩
    intro x
    rw [evalMonomial_selected_nil m x h0]
    exact (evalMonomial_emptyMask x).symm
  · left; refine ⟨LowerPhaseTerm.linear a, trivial, ?_⟩
    intro x
    simpa [lowerPhaseMask, evalMonomial_singletonMask] using evalMonomial_selected_one m x a h1
  · have hab : a ≠ b := by simpa [h2] using nodup
    left; refine ⟨LowerPhaseTerm.quadratic a b, hab, ?_⟩
    intro x
    simpa [lowerPhaseMask, evalMonomial_pairMask] using evalMonomial_selected_two m x a b h2
  · have hs : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa [h3] using nodup
    right; refine ⟨selectedTriple a b c, selectedTriple_injective a b c hs.1.1 hs.1.2 hs.2, ?_⟩
    intro x
    simpa [tripleMask_eval, selectedTriple] using evalMonomial_selected_three m x a b c h3

theorem cubicPhase_supported_blocks {n : Nat} (anchor : Fin n) (phase : PhaseANF n)
    (degree : ∀ m ∈ phase, monomialDegree m ≤ 3) :
    ∃ lower : List (LowerPhaseTerm n), ∃ cubic : List (Fin 3 → Fin n),
      (∀ t ∈ lower, t.valid) ∧ (∀ w ∈ cubic, Function.Injective w) ∧
      ∀ x, evalPhase phase x = evalPhase (combinedPhaseANF lower cubic) x := by
  induction phase with
  | nil =>
    refine ⟨[], [], ?_, ?_, ?_⟩ <;> simp [combinedPhaseANF, lowerPhaseANF, cubicLayerANF, evalPhase]
  | cons m rest ih =>
    have hm : monomialDegree m ≤ 3 := degree m (by simp)
    have hd : ∀ t ∈ rest, monomialDegree t ≤ 3 := by intro t ht; exact degree t (by simp [ht])
    obtain ⟨lower, cubic, hl, hc, he⟩ := ih hd
    rcases cubicMask_supported_block anchor m hm with ⟨term, hv, hs⟩ | ⟨w, hw, hs⟩
    · refine ⟨term :: lower, cubic, ?_, hc, ?_⟩
      · intro t ht; simp only [List.mem_cons] at ht; rcases ht with rfl | ht; exact hv; exact hl t ht
      · intro x
        simp only [evalPhase_cons, he x, combinedPhaseANF, lowerPhaseANF, List.map_cons, evalPhase_cons, hs x]
        simp only [List.cons_append, evalPhase_cons]
    · refine ⟨lower, w :: cubic, hl, ?_, ?_⟩
      · intro z hz; simp only [List.mem_cons] at hz; rcases hz with rfl | hz; exact hw; exact hc z hz
      · intro x
        simp only [evalPhase_cons, he x, combinedPhaseANF, cubicLayerANF, List.map_cons,
          evalPhase_append, evalPhase_cons, hs x]
        cases evalMonomial (tripleMask w) x <;> cases evalPhase (lowerPhaseANF lower) x <;>
          cases evalPhase (List.map tripleMask cubic) x <;> decide

theorem cubicPhase_native_exists {n : Nat} (anchor : Fin n) (phase : PhaseANF n)
    (degree : ∀ m ∈ phase, monomialDegree m ≤ 3) (state : SharedDyadicState n) :
    ∃ records : List NativeGate, ∃ result, replayExactNative n records state = some result ∧
      ∀ x, sharedAmplitude result x = exactOfDyadic
        ⟨if evalPhase phase x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩ := by
  obtain ⟨lower, cubic, hl, hc, he⟩ := cubicPhase_supported_blocks anchor phase degree
  obtain ⟨result, hr, ha⟩ := combinedPhaseNative_correct lower cubic hl hc state
  refine ⟨combinedPhaseRecords lower cubic, result, hr, ?_⟩
  intro x
  rw [he x]
  exact ha x

end SectorSimulation
