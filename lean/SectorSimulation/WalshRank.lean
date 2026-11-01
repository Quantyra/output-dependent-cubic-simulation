import SectorSimulation.InterleavedCanonicalSum
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# The rank of the source polar form

The residual kernel is already proved equal to the image of the source quadratic polar form and
already proved in bijection with assignments on a block of twice the recorded polar-elimination
pair count. This module draws the counting consequence — the image has `2 ^ (2 * pairCount)`
elements — and then identifies the manuscript's rank `r` with `2 * pairCount` as a theorem about
the module-theoretic rank of the polar form over the two-element field.

The identification is the route recorded as option 1 in `SEMANTICS.md`: binary vectors are
transported to `Fin n → ZMod 2`, the polar form becomes a linear map, and Mathlib's finite-field
cardinality lemma for submodules converts the image cardinality into a `finrank`.
-/

namespace SectorSimulation

open Classical

/-! ## Transport between Boolean vectors and `ZMod 2` vectors -/

/-- The Boolean-to-`ZMod 2` coercion. -/
def boolToZ2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The `ZMod 2`-to-Boolean coercion, inverse to `boolToZ2`. -/
def z2ToBool (c : ZMod 2) : Bool := decide (c = 1)

theorem z2ToBool_boolToZ2 (b : Bool) : z2ToBool (boolToZ2 b) = b := by
  cases b <;> decide

theorem boolToZ2_z2ToBool (c : ZMod 2) : boolToZ2 (z2ToBool c) = c := by
  fin_cases c <;> decide

theorem boolToZ2_xor (a b : Bool) :
    boolToZ2 (Bool.xor a b) = boolToZ2 a + boolToZ2 b := by
  cases a <;> cases b <;> decide

theorem z2ToBool_add (a b : ZMod 2) :
    z2ToBool (a + b) = Bool.xor (z2ToBool a) (z2ToBool b) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Pointwise transport of a binary vector into `Fin n → ZMod 2`. -/
def toZ2Vec {n : Nat} (v : BinaryVector n) : Fin n → ZMod 2 := fun i => boolToZ2 (v i)

/-- Pointwise transport of a `Fin n → ZMod 2` vector into a binary vector. -/
def ofZ2Vec {n : Nat} (x : Fin n → ZMod 2) : BinaryVector n := fun i => z2ToBool (x i)

theorem ofZ2Vec_toZ2Vec {n : Nat} (v : BinaryVector n) : ofZ2Vec (toZ2Vec v) = v := by
  funext i
  exact z2ToBool_boolToZ2 (v i)

theorem toZ2Vec_ofZ2Vec {n : Nat} (x : Fin n → ZMod 2) : toZ2Vec (ofZ2Vec x) = x := by
  funext i
  exact boolToZ2_z2ToBool (x i)

theorem ofZ2Vec_add {n : Nat} (x y : Fin n → ZMod 2) :
    ofZ2Vec (x + y) = vectorXor (ofZ2Vec x) (ofZ2Vec y) := by
  funext i
  show z2ToBool ((x + y) i) = Bool.xor (z2ToBool (x i)) (z2ToBool (y i))
  rw [Pi.add_apply, z2ToBool_add]

theorem toZ2Vec_zero {n : Nat} : toZ2Vec (zeroVector : BinaryVector n) = 0 := by
  funext i
  show boolToZ2 false = (0 : Fin n → ZMod 2) i
  rw [Pi.zero_apply]
  rfl

theorem z2ToBool_zero : z2ToBool (0 : ZMod 2) = false := by decide

theorem ofZ2Vec_zero {n : Nat} : ofZ2Vec (0 : Fin n → ZMod 2) = zeroVector := by
  funext i
  show z2ToBool ((0 : Fin n → ZMod 2) i) = false
  rw [Pi.zero_apply, z2ToBool_zero]

/-! ## Polar-form additivity and the zero vector -/

/-- The pointwise XOR of binary vectors is the derivative shift with the arguments exchanged. -/
theorem vectorXor_eq_binaryShift {n : Nat} (u v : BinaryVector n) :
    vectorXor u v = binaryShift v u := by
  funext i
  simp [vectorXor, binaryShift]

/-- The source polar form is additive in its first argument for a degree-at-most-two phase. -/
theorem phasePolar_add_left {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) (u v w : BinaryVector n) :
    phasePolar p (vectorXor u v) w = Bool.xor (phasePolar p u w) (phasePolar p v w) := by
  obtain ⟨ts, _, _, hpolar, _, hadd, _⟩ := sourceQuadratic_hasPolar p hdegree
  rw [vectorXor_eq_binaryShift, hpolar, hpolar, hpolar, hadd v u w, Bool.xor_comm]

/-- The polar form of a degree-at-most-two phase vanishes on the zero vector. -/
theorem sourcePolarVector_zero {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) :
    sourcePolarVector p (zeroVector : BinaryVector n) = zeroVector := by
  obtain ⟨ts, _, _, hpolar, _, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hterm : ∀ (t : QuadraticTerm n) (v : BinaryVector n),
      termPolar t (zeroVector : BinaryVector n) v = false := by
    intro t v
    cases t with
    | constant => rfl
    | linear j => rfl
    | product a b => simp [termPolar, zeroVector]
  have hstep : ∀ (ts : List (QuadraticTerm n)) (v : BinaryVector n),
      termsPolar ts (zeroVector : BinaryVector n) v = false := by
    intro ts
    induction ts with
    | nil => intro v; rfl
    | cons t rest ih =>
        intro v
        show Bool.xor (termPolar t (zeroVector : BinaryVector n) v)
          (termsPolar rest (zeroVector : BinaryVector n) v) = false
        rw [hterm, ih]
        rfl
  funext i
  show phasePolar p (zeroVector : BinaryVector n) (coordinateUnit i) = false
  rw [hpolar]
  exact hstep ts (coordinateUnit i)

/-! ## The polar form as a linear map over the two-element field -/

/-- The source polar form, transported to `Fin n → ZMod 2`, as a linear map. -/
noncomputable def polarLinearMap {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun x := toZ2Vec (sourcePolarVector p (ofZ2Vec x))
  map_add' x y := by
    funext i
    show boolToZ2 (phasePolar p (ofZ2Vec (x + y)) (coordinateUnit i)) =
      boolToZ2 (phasePolar p (ofZ2Vec x) (coordinateUnit i)) +
        boolToZ2 (phasePolar p (ofZ2Vec y) (coordinateUnit i))
    rw [ofZ2Vec_add, phasePolar_add_left p hdegree]
    exact boolToZ2_xor _ _
  map_smul' c x := by
    fin_cases c
    · show toZ2Vec (sourcePolarVector p (ofZ2Vec ((0 : ZMod 2) • x))) =
        (0 : ZMod 2) • toZ2Vec (sourcePolarVector p (ofZ2Vec x))
      rw [zero_smul, zero_smul, ofZ2Vec_zero, sourcePolarVector_zero p hdegree, toZ2Vec_zero]
    · show toZ2Vec (sourcePolarVector p (ofZ2Vec ((1 : ZMod 2) • x))) =
        (1 : ZMod 2) • toZ2Vec (sourcePolarVector p (ofZ2Vec x))
      rw [one_smul, one_smul]

/-! ## The cardinality of the polar image -/

/-- The image of the source polar form has exactly `2 ^ (2 * pairCount)` elements, where
`pairCount` is the number of recorded polar-elimination pairs. -/
theorem sourcePolarImage_card_eq_two_pow {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Fintype.card (Set.range (sourcePolarVector p)) =
      2 ^ (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) := by
  classical
  have hset : Set.range (sourcePolarVector p) =
      {l : BinaryVector n |
        recordedResidualLinearPart
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
          hsize
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector} := by
    ext l
    rw [Set.mem_range]
    exact (residualKernel_eq_sourcePolarImage p fuel hdegree hbound hlen m hsize l).symm
  have hbij := residualKernel_pairedBlock_bijective p fuel hdegree hlen m hsize hb
  calc Fintype.card (Set.range (sourcePolarVector p))
      = Fintype.card {l : BinaryVector n |
          recordedResidualLinearPart
            (recordedCoordinateAt
              (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
            hsize
            (transposeBinaryMatrix
              (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector} :=
        Fintype.card_congr (Equiv.setCongr hset)
    _ = Fintype.card (Fin (2 *
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool) :=
        Fintype.card_congr (Equiv.ofBijective _ hbij)
    _ = 2 ^ (2 *
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) := by
        simp

/-- The range of the transported polar map has the cardinality of the polar image. -/
theorem polarLinearMap_range_card {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) :
    Fintype.card (LinearMap.range (polarLinearMap p hdegree)) =
      Fintype.card (Set.range (sourcePolarVector p)) := by
  classical
  let φ := polarLinearMap p hdegree
  have hφ : ∀ x : Fin n → ZMod 2, φ x = toZ2Vec (sourcePolarVector p (ofZ2Vec x)) := fun x => rfl
  have hrange : Set.range ⇑φ = toZ2Vec '' Set.range (sourcePolarVector p) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨sourcePolarVector p (ofZ2Vec x), ⟨ofZ2Vec x, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨x, hx⟩, rfl⟩
      refine ⟨toZ2Vec x, ?_⟩
      rw [hφ, ofZ2Vec_toZ2Vec, hx]
  have hinj : Function.Injective (toZ2Vec : BinaryVector n → Fin n → ZMod 2) := by
    intro a b hab
    have h := congrArg ofZ2Vec hab
    simpa [ofZ2Vec_toZ2Vec] using h
  calc Fintype.card (LinearMap.range φ)
      = Fintype.card (Set.range ⇑φ) := Fintype.card_congr (Equiv.setCongr (LinearMap.coe_range φ))
    _ = Fintype.card (toZ2Vec '' Set.range (sourcePolarVector p)) :=
        Fintype.card_congr (Equiv.setCongr hrange)
    _ = Fintype.card (Set.range (sourcePolarVector p)) := Set.card_image_of_injective _ hinj

/-- The manuscript's polar rank `r` is twice the recorded pair count, as a theorem about the
module-theoretic rank of the polar form over the two-element field. -/
theorem polarRank_eq_two_mul {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) =
      2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := Module.card_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.range (polarLinearMap p hdegree))
  have hz : Fintype.card (ZMod 2) = 2 := ZMod.card 2
  have hrange := polarLinearMap_range_card p hdegree
  have himg := sourcePolarImage_card_eq_two_pow p fuel hdegree hbound hlen m hsize hb
  have hpow : 2 ^ Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) =
      2 ^ (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) := by
    calc 2 ^ Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree))
        = Fintype.card (ZMod 2) ^
            Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) := by rw [hz]
      _ = Fintype.card (LinearMap.range (polarLinearMap p hdegree)) := hcard.symm
      _ = Fintype.card (Set.range (sourcePolarVector p)) := hrange
      _ = 2 ^ (2 * (polarEliminate (phasePolar p) fuel
            (List.finRange n) identityMatrix).2.2.length) := himg
  exact Nat.pow_right_injective (by norm_num) hpow

/-- Consequently the manuscript's polar rank is even, with half-rank the recorded pair count. -/
theorem polarRank_even {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    ∃ r : Nat,
      Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) = r + r := by
  refine ⟨(polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length, ?_⟩
  rw [polarRank_eq_two_mul p fuel hdegree hbound hlen m hsize hb]
  ring

end SectorSimulation
