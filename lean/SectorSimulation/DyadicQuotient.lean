import SectorSimulation.DyadicAddition
namespace SectorSimulation

def dyadicSetoid : Setoid DyadicCyclo where
  r := dyadicEquivalent
  iseqv := ⟨dyadicEquivalent_refl, (fun {_ _} h => dyadicEquivalent_symm _ _ h),
    (fun {_ _ _} h1 h2 => dyadicEquivalent_trans _ _ _ h1 h2)⟩

abbrev ExactAmplitude := Quotient dyadicSetoid

def exactOfDyadic (a : DyadicCyclo) : ExactAmplitude := Quotient.mk dyadicSetoid a

def exactAdd : ExactAmplitude → ExactAmplitude → ExactAmplitude :=
  Quotient.lift₂ (fun a b => exactOfDyadic (dyadicAdd a b))
    (fun a c b d h1 h2 => Quotient.sound (dyadicAdd_congr a b c d h1 h2))

def exactSub : ExactAmplitude → ExactAmplitude → ExactAmplitude :=
  Quotient.lift₂ (fun a b => exactOfDyadic (dyadicSubtract a b))
    (fun a c b d h1 h2 => Quotient.sound (dyadicSubtract_congr a b c d h1 h2))

def exactMul : ExactAmplitude → ExactAmplitude → ExactAmplitude :=
  Quotient.lift₂ (fun a b => exactOfDyadic (dyadicMultiply a b))
    (fun a c b d h1 h2 => Quotient.sound (dyadicMultiply_congr a b c d h1 h2))

def exactNeg : ExactAmplitude → ExactAmplitude :=
  Quotient.lift (fun a => exactOfDyadic (dyadicNeg a))
    (fun a b h => Quotient.sound (dyadicNeg_congr a b h))

def exactOne : ExactAmplitude := exactOfDyadic dyadicOne

def exactHadamardScale : ExactAmplitude := exactOfDyadic dyadicHadamardScale

theorem exact_add_representatives (a b : DyadicCyclo) :
    exactAdd (exactOfDyadic a) (exactOfDyadic b) = exactOfDyadic (dyadicAdd a b) := by rfl

theorem exact_mul_representatives (a b : DyadicCyclo) :
    exactMul (exactOfDyadic a) (exactOfDyadic b) = exactOfDyadic (dyadicMultiply a b) := by rfl

theorem exact_hadamard_scalar_normalization :
    exactAdd (exactMul exactHadamardScale exactHadamardScale)
      (exactMul exactHadamardScale exactHadamardScale) = exactOne := by
  apply Quotient.sound
  change dyadicEquivalent (dyadicAdd (dyadicMultiply dyadicHadamardScale dyadicHadamardScale)
    (dyadicMultiply dyadicHadamardScale dyadicHadamardScale)) dyadicOne
  unfold dyadicEquivalent
  decide

theorem exactAdd_comm (a b : ExactAmplitude) : exactAdd a b = exactAdd b a := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change exactOfDyadic (dyadicAdd a b) = exactOfDyadic (dyadicAdd b a)
      rw [dyadicAdd_comm]

theorem exactMul_comm (a b : ExactAmplitude) : exactMul a b = exactMul b a := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change exactOfDyadic (dyadicMultiply a b) = exactOfDyadic (dyadicMultiply b a)
      rw [dyadicMultiply_comm]

end SectorSimulation
