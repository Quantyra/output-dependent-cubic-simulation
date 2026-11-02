import SectorSimulation.WalshSectorFourier
import SectorSimulation.WalshSectorOrthogonal
import SectorSimulation.WalshSectorObservable

/-!
# The Fourier factor applied to a sector state: coset reindexing

`F_J` acting on a sector state sums over the character space, but the sector amplitude vanishes off its
coset, so the sum is really a sum over the coordinate space. This module makes that reindexing precise.

It **names the object** the matched-sector identity will have to evaluate; it evaluates nothing. In
particular the sum produced here still contains the phase of `f0`, so no Gauss-sum value, no `2^(r/2)`
scaling, no support on the neighbouring coset and no phase `e^(i theta_a)` is obtained. `F_J F_J`,
unitarity, `Z_e`, the offset `eta` and every overlap clause remain absent.

Route note, recorded because both reviews asked for it: the operator algebra of the observable is
carried out in the exact amplitude quotient (`characterFourier`, `sectorDiag`), while statements
requiring a modulus, conjugation or order are carried out in `ℂ` through `exactComplex`. This module is
on the quotient side.
-/

namespace SectorSimulation

open scoped BigOperators

/-- Remove the first occurrence of an element. Defined locally because the core `List.erase` needs a
`BEq` instance, which the vector type does not have. -/
def dropFirst {n : Nat} (ys : List (BinaryVector n)) (b : BinaryVector n) : List (BinaryVector n) :=
  match ys with
  | [] => []
  | c :: rest => if b = c then rest else c :: dropFirst rest b

theorem mem_dropFirst_subset {n : Nat} {ys : List (BinaryVector n)} {b b' : BinaryVector n}
    (h : b' ∈ dropFirst ys b) : b' ∈ ys := by
  induction ys with
  | nil => simp [dropFirst] at h
  | cons c rest ih =>
    by_cases hbc : b = c
    · rw [dropFirst, if_pos hbc] at h
      exact List.mem_cons.mpr (Or.inr h)
    · rw [dropFirst, if_neg hbc] at h
      rcases List.mem_cons.mp h with hh | hh
      · exact List.mem_cons.mpr (Or.inl hh)
      · exact List.mem_cons.mpr (Or.inr (ih hh))

theorem mem_dropFirst_of_ne {n : Nat} {ys : List (BinaryVector n)} {b b' : BinaryVector n}
    (hb' : b' ≠ b) (h : b' ∈ ys) : b' ∈ dropFirst ys b := by
  induction ys with
  | nil => simp at h
  | cons c rest ih =>
    by_cases hbc : b = c
    · subst hbc
      rw [dropFirst, if_pos rfl]
      rcases List.mem_cons.mp h with hh | hh
      · exact absurd hh hb'
      · exact hh
    · rw [dropFirst, if_neg hbc]
      rcases List.mem_cons.mp h with hh | hh
      · exact List.mem_cons.mpr (Or.inl hh)
      · exact List.mem_cons.mpr (Or.inr (ih hh))

theorem not_mem_dropFirst_self {n : Nat} : ∀ (ys : List (BinaryVector n)) (b : BinaryVector n),
    ys.Nodup → b ∉ dropFirst ys b
  | [], _, _ => by simp [dropFirst]
  | c :: rest, b, hnod => by
      by_cases hbc : b = c
      · rw [dropFirst, if_pos hbc, hbc]
        exact (List.nodup_cons.mp hnod).1
      · rw [dropFirst, if_neg hbc]
        intro hmem
        rcases List.mem_cons.mp hmem with hh | hh
        · exact hbc hh
        · exact not_mem_dropFirst_self rest b (List.nodup_cons.mp hnod).2 hh

theorem nodup_dropFirst {n : Nat} : ∀ (ys : List (BinaryVector n)) (b : BinaryVector n),
    ys.Nodup → (dropFirst ys b).Nodup
  | [], _, _ => by simp [dropFirst]
  | c :: rest, b, hnod => by
      have hrest := (List.nodup_cons.mp hnod).2
      by_cases hbc : b = c
      · rw [dropFirst, if_pos hbc]
        exact hrest
      · rw [dropFirst, if_neg hbc]
        exact List.nodup_cons.mpr ⟨fun hmem => (List.nodup_cons.mp hnod).1
          (mem_dropFirst_subset hmem), nodup_dropFirst rest b hrest⟩

/-- A list sum splits at any element that occurs in it. -/
theorem foldr_dropFirst {n : Nat} (ys : List (BinaryVector n)) (b : BinaryVector n)
    (g : BinaryVector n → ExactAmplitude) (hm : b ∈ ys) :
    ys.foldr (fun c acc => exactAdd (g c) acc) exactZero =
      exactAdd (g b) ((dropFirst ys b).foldr (fun c acc => exactAdd (g c) acc) exactZero) := by
  induction ys with
  | nil => simp at hm
  | cons c rest ih =>
    by_cases hbc : b = c
    · rw [dropFirst, if_pos hbc, List.foldr_cons, hbc]
    · rw [dropFirst, if_neg hbc]
      have hmem : b ∈ rest := by
        rcases List.mem_cons.mp hm with hh | hh
        · exact absurd hh hbc
        · exact hh
      rw [List.foldr_cons, List.foldr_cons, ih hmem, exactAdd_left_comm]

/-- A list sum all of whose terms vanish is zero. -/
theorem foldr_zero_of_all {n : Nat} (ys : List (BinaryVector n))
    (g : BinaryVector n → ExactAmplitude) (h : ∀ b ∈ ys, g b = exactZero) :
    ys.foldr (fun b acc => exactAdd (g b) acc) exactZero = exactZero := by
  induction ys with
  | nil => rfl
  | cons c rest ih =>
    rw [List.foldr_cons, h c (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb))), exactAdd_zero]

/-- Reindexing a list sum along an injection.

If `xs` is a nodup index list, `ys` is a nodup character list containing the whole image of `e`, and
`f` vanishes off that image, then summing `f` over `ys` equals summing `f ∘ e` over `xs`. This is the
"sum over the image" step in the exact amplitude quotient, where no additive instance is available and
sums are `List.foldr` over `binaryBasis`. -/
theorem foldr_reindex_of_injective {n : Nat} {α : Type} (xs : List α)
    (e : α → BinaryVector n) (ys : List (BinaryVector n))
    (f : BinaryVector n → ExactAmplitude)
    (hinj : ∀ a a', e a = e a' → a = a')
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (himg : ∀ a ∈ xs, e a ∈ ys)
    (hvan : ∀ b ∈ ys, (∀ a ∈ xs, e a ≠ b) → f b = exactZero) :
    ys.foldr (fun b acc => exactAdd (f b) acc) exactZero =
      xs.foldr (fun a acc => exactAdd (f (e a)) acc) exactZero := by
  induction xs generalizing ys with
  | nil =>
    rw [foldr_zero_of_all ys f (fun b hb =>
      hvan b hb (fun a ha => by simp at ha))]
    rfl
  | cons a rest ih =>
    obtain ⟨hanot, hrest⟩ := List.nodup_cons.mp hxs
    have hea : e a ∈ ys := himg a (List.mem_cons.mpr (Or.inl rfl))
    rw [foldr_dropFirst ys (e a) f hea, List.foldr_cons]
    have hstep := ih (dropFirst ys (e a)) hrest (nodup_dropFirst ys (e a) hys) ?_ ?_
    rw [hstep]
    · intro a' ha'
      have h1 : e a' ∈ ys := himg a' (List.mem_cons.mpr (Or.inr ha'))
      have h2 : e a' ≠ e a := by
        intro heq
        have hEq : a' = a := hinj a' a heq
        subst hEq
        exact hanot ha'
      exact mem_dropFirst_of_ne h2 h1
    · intro b hb hno
      have hbys : b ∈ ys := mem_dropFirst_subset hb
      exact hvan b hbys (fun a' ha' => by
        rcases List.mem_cons.mp ha' with hh | hh
        · rw [hh]
          exact fun heq => not_mem_dropFirst_self ys (e a) hys (heq ▸ hb)
        · exact hno a' hh)

/-- The Fourier factor applied to a sector state is a sum over the coset, indexed by the coordinate
space, with the paper's normalization factored out.

The sum is left unevaluated: it is the object the matched-sector identity must evaluate. -/
theorem characterFourier_sectorAmplitude {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) (l : BinaryVector n) :
    characterFourier J (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a) l =
      exactMul (iterateHadamardScale n exactOne)
        ((binaryBasis (2 * (polarEliminate (phasePolar q) fuel
            (List.finRange n) identityMatrix).2.2.length)).foldr
          (fun y acc => exactAdd
            (exactSigned
              (matrixPairingParity J l
                (sectorSupportPoint q fuel hdegree hlen m hsize hb a y))
              (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y)) acc) exactZero) := by
  classical
  unfold characterFourier
  refine congrArg (exactMul (iterateHadamardScale n exactOne)) ?_
  have hreindex := foldr_reindex_of_injective
    (binaryBasis (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length))
    (fun y => sectorSupportPoint q fuel hdegree hlen m hsize hb a y)
    (binaryBasis n)
    (fun b => exactSigned (matrixPairingParity J l b)
      (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a b))
    (fun a' a'' heq => sectorSupportPoint_injective_at_label q fuel hdegree hlen m hsize hb a heq)
    (binaryBasis_nodup _)
    (binaryBasis_nodup n)
    (fun y _ => binaryBasis_complete (sectorSupportPoint q fuel hdegree hlen m hsize hb a y))
    (fun b _ hno => by
      have hnot : ¬ ∃ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool),
          sectorSupportPoint q fuel hdegree hlen m hsize hb a y = b := by
        rintro ⟨y, hy⟩
        exact (hno y (binaryBasis_complete y)) hy
      show exactSigned (matrixPairingParity J l b)
        (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a b) = exactZero
      rw [sectorAmplitude_eq_zero_of_not_support q f0 J beta fuel hdegree hlen m hsize hb a b hnot,
        exactSigned_zero])
  rw [hreindex]
  simp only [sectorAmplitude_support]

end SectorSimulation
