import SectorSimulation.SharedAdditionAmplitude
namespace SectorSimulation

def weightedBasis (state : SharedDyadicState 3) (k : Fin 8) : SharedDyadicState 3 :=
  sharedShift state.exponent (sharedScale (state.numerator (threeBitVector k)) (threeBitBasis k))

def threeBitDecomposition (state : SharedDyadicState 3) : SharedDyadicState 3 :=
  sharedAddSame (weightedBasis state 0) (sharedAddSame (weightedBasis state 1)
  (sharedAddSame (weightedBasis state 2) (sharedAddSame (weightedBasis state 3)
  (sharedAddSame (weightedBasis state 4) (sharedAddSame (weightedBasis state 5)
  (sharedAddSame (weightedBasis state 6) (weightedBasis state 7)))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem threeBitDecomposition_correct (state : SharedDyadicState 3) :
    threeBitDecomposition state = state := by
  cases state with | mk f e =>
    have hexp : 0 + e = e := Nat.zero_add e
    simp only [threeBitDecomposition, weightedBasis, sharedShift, sharedScale, sharedAddSame, threeBitBasis, hexp]
    congr 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2
    · have hx : x = threeBitVector 0 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 4 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 2 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 6 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 1 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 5 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 3 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]
    · have hx : x = threeBitVector 7 := by
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
          have bound := i.isLt
          omega
        rcases hi with hi | hi | hi <;> subst i <;> first | exact h0 | exact h1 | exact h2
      subst x
      simp (config := { decide := true }) [threeBitVector, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]

end SectorSimulation
