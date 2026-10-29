import SectorSimulation.DerivativeProduct

/-!
Explicit degree-at-most-three monomial difference identities over F2.
These identities are pointwise Boolean statements. Connecting them to the
list-of-masks ANF representation and proving the general degree bound remains
separate work.
-/

namespace SectorSimulation

/-- The derivative of a degree-two Boolean monomial has only degree-one
and constant terms in the original variables. -/
theorem quadratic_difference_expansion (a b ja jb : Bool) :
    Bool.xor (a && b) (Bool.xor a ja && Bool.xor b jb) =
      Bool.xor (Bool.xor (ja && b) (a && jb)) (ja && jb) := by
  cases a <;> cases b <;> cases ja <;> cases jb <;> rfl

/-- The derivative of a degree-three Boolean monomial has seven terms,
each with at most two of the original variables. -/
theorem cubic_difference_expansion (a b c ja jb jc : Bool) :
    Bool.xor (a && b && c)
        (Bool.xor a ja && Bool.xor b jb && Bool.xor c jc) =
      Bool.xor
        (Bool.xor
          (Bool.xor (ja && b && c) (a && jb && c))
          (Bool.xor (a && b && jc) (ja && jb && c)))
        (Bool.xor
          (Bool.xor (ja && b && jc) (a && jb && jc))
          (ja && jb && jc)) := by
  cases a <;> cases b <;> cases c <;>
    cases ja <;> cases jb <;> cases jc <;> rfl

end SectorSimulation
