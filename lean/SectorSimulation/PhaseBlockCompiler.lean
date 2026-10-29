import SectorSimulation.CubicMaskCoverage
namespace SectorSimulation

inductive PhaseBlock (n : Nat) where
  | lower (term : LowerPhaseTerm n)
  | cubic (a b c : Fin n)

def compilePhaseMask {n : Nat} (anchor : Fin n) (m : Monomial n) : Option (PhaseBlock n) :=
  match selectedVariables m with
  | [] => some (.lower (.constant anchor))
  | [a] => some (.lower (.linear a))
  | [a,b] => some (.lower (.quadratic a b))
  | [a,b,c] => some (.cubic a b c)
  | _ => none

def PhaseBlock.valid {n : Nat} : PhaseBlock n → Prop
  | .lower term => term.valid
  | .cubic a b c => a ≠ b ∧ a ≠ c ∧ b ≠ c

def PhaseBlock.mask {n : Nat} : PhaseBlock n → Monomial n
  | .lower term => lowerPhaseMask term
  | .cubic a b c => tripleMask (selectedTriple a b c)

theorem compilePhaseMask_correct {n : Nat} (anchor : Fin n) (m : Monomial n)
    (degree : monomialDegree m ≤ 3) :
    ∃ block, compilePhaseMask anchor m = some block ∧ block.valid ∧
      ∀ x, evalMonomial m x = evalMonomial block.mask x := by
  have nodup := selectedVariables_nodup m
  rcases cubicMask_selected_shape m degree with h0 | ⟨a,h1⟩ | ⟨a,b,h2⟩ | ⟨a,b,c,h3⟩
  · refine ⟨.lower (.constant anchor), ?_, trivial, ?_⟩
    · simp [compilePhaseMask, h0]
    · intro x; simpa [PhaseBlock.mask, lowerPhaseMask, evalMonomial_emptyMask] using evalMonomial_selected_nil m x h0
  · refine ⟨.lower (.linear a), ?_, trivial, ?_⟩
    · simp [compilePhaseMask, h1]
    · intro x; simpa [PhaseBlock.mask, lowerPhaseMask, evalMonomial_singletonMask] using evalMonomial_selected_one m x a h1
  · have hab : a ≠ b := by simpa [h2] using nodup
    refine ⟨.lower (.quadratic a b), ?_, hab, ?_⟩
    · simp [compilePhaseMask, h2]
    · intro x; simpa [PhaseBlock.mask, lowerPhaseMask, evalMonomial_pairMask] using evalMonomial_selected_two m x a b h2
  · have hs : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by simpa [h3] using nodup
    refine ⟨.cubic a b c, ?_, ⟨hs.1.1, hs.1.2, hs.2⟩, ?_⟩
    · simp [compilePhaseMask, h3]
    · intro x; simpa [PhaseBlock.mask, tripleMask_eval, selectedTriple] using evalMonomial_selected_three m x a b c h3

def compilePhaseBlocks {n : Nat} (anchor : Fin n) : PhaseANF n → Option (List (PhaseBlock n))
  | [] => some []
  | m :: rest => do
      let block ← compilePhaseMask anchor m
      let blocks ← compilePhaseBlocks anchor rest
      some (block :: blocks)

theorem compilePhaseBlocks_correct {n : Nat} (anchor : Fin n) (phase : PhaseANF n)
    (degree : ∀ m ∈ phase, monomialDegree m ≤ 3) :
    ∃ blocks, compilePhaseBlocks anchor phase = some blocks ∧
      (∀ block ∈ blocks, block.valid) ∧
      ∀ x, evalPhase phase x = evalPhase (blocks.map PhaseBlock.mask) x := by
  induction phase with
  | nil => refine ⟨[], rfl, ?_, ?_⟩ <;> simp [evalPhase]
  | cons m rest ih =>
    have hm : monomialDegree m ≤ 3 := degree m (by simp)
    have hd : ∀ t ∈ rest, monomialDegree t ≤ 3 := by intro t ht; exact degree t (by simp [ht])
    obtain ⟨block, hb, hv, he⟩ := compilePhaseMask_correct anchor m hm
    obtain ⟨blocks, hs, hvalid, heval⟩ := ih hd
    refine ⟨block :: blocks, ?_, ?_, ?_⟩
    · simp [compilePhaseBlocks, hb, hs]
    · intro b h; simp only [List.mem_cons] at h; rcases h with rfl | h; exact hv; exact hvalid b h
    · intro x; simp only [List.map_cons, evalPhase_cons, he x, heval x]

def PhaseBlock.records {n : Nat} : PhaseBlock n → List NativeGate
  | .lower term => lowerPhaseRecords term
  | .cubic a b c => threeWireCubicProgram.map (mappedNativeGate (selectedTriple a b c))

theorem phaseBlock_records_correct {n : Nat} (block : PhaseBlock n) (valid : block.valid)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n block.records state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (sharedMonomialSign block.mask state) x := by
  cases block with
  | lower term => exact nativeLowerPhaseTerm_correct term valid state
  | cubic a b c =>
    obtain ⟨hab, hac, hbc⟩ := valid
    obtain ⟨result, hr, he⟩ := mappedNativeCubic_correct (selectedTriple a b c)
      (selectedTriple_injective a b c hab hac hbc) state
    refine ⟨result, hr, ?_⟩
    intro x
    simpa [PhaseBlock.mask, sharedMonomialSign, sharedCubicSign, tripleMask_eval, selectedTriple] using he x

def phaseBlockRecords {n : Nat} (blocks : List (PhaseBlock n)) : List NativeGate :=
  blocks.flatMap PhaseBlock.records

def idealPhaseBlocks {n : Nat} : List (PhaseBlock n) → SharedDyadicState n → SharedDyadicState n
  | [], state => state
  | block :: rest, state => idealPhaseBlocks rest (sharedMonomialSign block.mask state)

theorem phaseBlockRecords_correct_from_equivalent {n : Nat} (blocks : List (PhaseBlock n))
    (valid : ∀ b ∈ blocks, b.valid) (u v : SharedDyadicState n)
    (equiv : ∀ x, sharedAmplitude u x = sharedAmplitude v x) :
    ∃ result, replayExactNative n (phaseBlockRecords blocks) u = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (idealPhaseBlocks blocks v) x := by
  induction blocks generalizing u v with
  | nil => exact ⟨u, rfl, equiv⟩
  | cons block rest ih =>
    have hb : block.valid := valid block (by simp)
    have hr : ∀ b ∈ rest, b.valid := by intro b h; exact valid b (by simp [h])
    obtain ⟨mid, hm, ha⟩ := phaseBlock_records_correct block hb u
    have he : ∀ x, sharedAmplitude mid x = sharedAmplitude (sharedMonomialSign block.mask v) x := by
      intro x; exact (ha x).trans (sharedMonomialSign_congr block.mask u v equiv x)
    obtain ⟨result, hresult, heq⟩ := ih hr mid (sharedMonomialSign block.mask v) he
    refine ⟨result, ?_, heq⟩
    simp only [phaseBlockRecords, List.flatMap_cons, replayExactNative_append, hm]
    exact hresult

theorem idealPhaseBlocks_phase {n : Nat} (blocks : List (PhaseBlock n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (idealPhaseBlocks blocks state).numerator x =
      if evalPhase (blocks.map PhaseBlock.mask) x then cycloNeg (state.numerator x) else state.numerator x := by
  induction blocks generalizing state with
  | nil => simp [idealPhaseBlocks, evalPhase]
  | cons block rest ih =>
    simp only [idealPhaseBlocks, ih, List.map_cons, evalPhase_cons, sharedMonomialSign]
    cases h : evalMonomial block.mask x <;>
      cases ht : evalPhase (List.map PhaseBlock.mask rest) x <;> simp [h, ht, cycloNeg]
    all_goals cases state.numerator x <;> simp [cycloNeg]

theorem idealPhaseBlocks_exponent {n : Nat} (blocks : List (PhaseBlock n))
    (state : SharedDyadicState n) : (idealPhaseBlocks blocks state).exponent = state.exponent := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih => simpa [idealPhaseBlocks, sharedMonomialSign] using ih (sharedMonomialSign block.mask state)

def compilePhaseRecords {n : Nat} (anchor : Fin n) (phase : PhaseANF n) : Option (List NativeGate) :=
  (compilePhaseBlocks anchor phase).map phaseBlockRecords

theorem compilePhaseRecords_correct {n : Nat} (anchor : Fin n) (phase : PhaseANF n)
    (degree : ∀ m ∈ phase, monomialDegree m ≤ 3) (state : SharedDyadicState n) :
    ∃ records result, compilePhaseRecords anchor phase = some records ∧
      replayExactNative n records state = some result ∧
      ∀ x, sharedAmplitude result x = exactOfDyadic
        ⟨if evalPhase phase x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩ := by
  obtain ⟨blocks, hc, hv, he⟩ := compilePhaseBlocks_correct anchor phase degree
  obtain ⟨result, hr, ha⟩ := phaseBlockRecords_correct_from_equivalent blocks hv state state (fun _ => rfl)
  refine ⟨phaseBlockRecords blocks, result, ?_, hr, ?_⟩
  · simp [compilePhaseRecords, hc]
  · intro x
    rw [ha x, he x]
    simp [sharedAmplitude, idealPhaseBlocks_phase, idealPhaseBlocks_exponent]

end SectorSimulation
