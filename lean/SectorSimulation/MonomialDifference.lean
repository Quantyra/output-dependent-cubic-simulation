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

/-- The explicit quadratic-monomial expansion instantiated on binary vectors. -/
theorem quadraticVariable_derivative {ι : Type} (i k : ι) (v j : ι → Bool) :
    booleanDerivative (fun w => w i && w k) (binaryShift j) v =
      Bool.xor (Bool.xor (j i && v k) (v i && j k)) (j i && j k) := by
  exact quadratic_difference_expansion (v i) (v k) (j i) (j k)

/-- The explicit cubic-monomial expansion instantiated on binary vectors.
Repeated indices are allowed; no distinctness or oracle hypothesis is needed. -/
theorem cubicVariable_derivative {ι : Type} (i k l : ι) (v j : ι → Bool) :
    booleanDerivative (fun w => w i && w k && w l) (binaryShift j) v =
      Bool.xor
        (Bool.xor
          (Bool.xor (j i && v k && v l) (v i && j k && v l))
          (Bool.xor (v i && v k && j l) (j i && j k && v l)))
        (Bool.xor
          (Bool.xor (j i && v k && j l) (v i && j k && j l))
          (j i && j k && j l)) := by
  exact cubic_difference_expansion (v i) (v k) (v l) (j i) (j k) (j l)

end SectorSimulation
