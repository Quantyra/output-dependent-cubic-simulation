import SectorSimulation.CanonicalPairVectors
import SectorSimulation.CanonicalCoordinateLayout
namespace SectorSimulation

def canonicalAssignment {k m : Nat} (x : BinaryVector ((k+k)+m)) :
    List Bool × List (Bool × Bool) :=
  (vectorAssignment (canonicalRadical x), vectorPairAssignment (canonicalLeft x) (canonicalRight x))

theorem canonicalAssignment_join {k m : Nat} (u v : BinaryVector k) (w : BinaryVector m) :
    canonicalAssignment (canonicalJoin u v w) = (vectorAssignment w, vectorPairAssignment u v) := by
  simp [canonicalAssignment, canonicalLeft_join, canonicalRight_join, canonicalRadical_join]

theorem canonicalAssignment_injective (k m : Nat) : Function.Injective (@canonicalAssignment k m) := by
  intro x y h
  have hr := congrArg Prod.fst h
  have hp := congrArg Prod.snd h
  have huv := vectorPairAssignment_injective _ _ _ _ hp
  have hw := vectorAssignment_injective m hr
  calc
    x = canonicalJoin (canonicalLeft x) (canonicalRight x) (canonicalRadical x) := (canonicalJoin_split x).symm
    _ = canonicalJoin (canonicalLeft y) (canonicalRight y) (canonicalRadical y) := by rw [huv.1, huv.2, hw]
    _ = y := canonicalJoin_split y

theorem canonicalAssignment_surjective {k m : Nat} (ps : List (Bool × Bool)) (rs : List Bool)
    (hp : ps ∈ pairAssignments k) (hr : rs ∈ radicalAssignments m) :
    ∃ x : BinaryVector ((k+k)+m), canonicalAssignment x = (rs,ps) := by
  obtain ⟨u,v,huv,_⟩ := pairAssignment_has_unique_vectors k ps hp
  obtain ⟨w,hw,_⟩ := radicalAssignment_has_unique_vector m rs hr
  refine ⟨canonicalJoin u v w, ?_⟩
  rw [canonicalAssignment_join, hw, huv]

def canonicalPhaseOnVector {k m : Nat} (pairs : List (Bool × Bool)) (radicals : List Bool)
    (c : Bool) (x : BinaryVector ((k+k)+m)) : Bool :=
  pairPhaseEval pairs (canonicalAssignment x).2
    (radicalPhaseEval radicals (canonicalAssignment x).1 c)

theorem canonicalPhaseOnVector_join {k m : Nat} (pairs : List (Bool × Bool))
    (radicals : List Bool) (c : Bool) (u v : BinaryVector k) (w : BinaryVector m) :
    canonicalPhaseOnVector pairs radicals c (canonicalJoin u v w) =
      pairPhaseEval pairs (vectorPairAssignment u v) (radicalPhaseEval radicals (vectorAssignment w) c) := by
  simp [canonicalPhaseOnVector, canonicalAssignment_join]


def listCartesian {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x,y)))

theorem listCartesian_nodup {α β : Type} (xs : List α) (ys : List β)
    (hx : xs.Nodup) (hy : ys.Nodup) : (listCartesian xs ys).Nodup := by
  induction xs with
  | nil => simp [listCartesian]
  | cons x rest ih =>
    have hh := List.nodup_cons.mp hx
    have hn : (ys.map (fun y => (x,y))).Nodup :=
      List.Pairwise.map _ (fun _ _ h e => h (congrArg Prod.snd e)) hy
    simp only [listCartesian, List.flatMap_cons]
    apply List.nodup_append.mpr
    refine ⟨hn, ih hh.2, ?_⟩
    intro p hp q hq he
    obtain ⟨y,hy',rfl⟩ := List.mem_map.mp hp
    obtain ⟨x',hx',hq'⟩ := List.mem_flatMap.mp hq
    obtain ⟨y',hy'',rfl⟩ := List.mem_map.mp hq'
    have eq : x = x' := congrArg Prod.fst he
    subst x'
    exact hh.1 hx'


theorem canonicalAssignment_mem {k m : Nat} (x : BinaryVector ((k+k)+m)) :
    canonicalAssignment x ∈ listCartesian (radicalAssignments m) (pairAssignments k) := by
  apply List.mem_flatMap.mpr
  refine ⟨vectorAssignment (canonicalRadical x), vectorAssignment_mem _, ?_⟩
  exact List.mem_map.mpr ⟨vectorPairAssignment (canonicalLeft x) (canonicalRight x),
    vectorPairAssignment_mem _ _, rfl⟩

theorem canonicalAssignment_perm (k m : Nat) :
    ((binaryBasis ((k+k)+m)).map canonicalAssignment).Perm
      (listCartesian (radicalAssignments m) (pairAssignments k)) := by
  have hnd : ((binaryBasis ((k+k)+m)).map canonicalAssignment).Nodup :=
    List.Pairwise.map _ (fun _ _ h he => h (canonicalAssignment_injective k m he)) (binaryBasis_nodup _)
  have hpd := listCartesian_nodup (radicalAssignments m) (pairAssignments k)
    (radicalAssignments_nodup m) (pairAssignments_nodup k)
  have hm : ∀ z, z ∈ ((binaryBasis ((k+k)+m)).map canonicalAssignment) ↔
      z ∈ listCartesian (radicalAssignments m) (pairAssignments k) := by
    intro z
    constructor
    · intro hz
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz
      exact canonicalAssignment_mem x
    · intro hz
      obtain ⟨rs, hrs, hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨ps, hps, he⟩ := List.mem_map.mp hz
      have hx := canonicalAssignment_surjective ps rs hps hrs
      obtain ⟨x, hx⟩ := hx
      apply List.mem_map.mpr
      exact ⟨x, binaryBasis_complete x, hx.trans he⟩
  apply List.perm_iff_count.mpr
  intro z
  rw [hnd.count, hpd.count]
  simp [hm z]


theorem integerSum_perm {α : Type} (xs ys : List α) (h : xs.Perm ys) (f : α → Int) :
    (xs.map f).sum = (ys.map f).sum := by
  induction h with
  | nil => rfl
  | cons a h ih => simp [ih]
  | swap a b xs => simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

theorem integerSum_cartesian {α β : Type} (xs : List α) (ys : List β) (f : α × β → Int) :
    ((listCartesian xs ys).map f).sum =
      (xs.map (fun x => (ys.map (fun y => f (x,y))).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [listCartesian, List.map_flatMap, List.map_map, Function.comp_def] at ih ⊢
    exact ih

def canonicalVectorWalshSum {k m : Nat} (pairs : List (Bool × Bool)) (radicals : List Bool) (c : Bool) : Int :=
  ((binaryBasis ((k+k)+m)).map (fun x => integerWalshSign (canonicalPhaseOnVector pairs radicals c x))).sum

theorem canonicalVectorWalshSum_eq {k m : Nat} (pairs : List (Bool × Bool)) (radicals : List Bool)
    (c : Bool) (hp : pairs.length = k) (hr : radicals.length = m) :
    canonicalVectorWalshSum (k := k) (m := m) pairs radicals c = explicitCanonicalSum pairs radicals c := by
  have h := integerSum_perm _ _ (canonicalAssignment_perm k m)
    (fun z => integerWalshSign (pairPhaseEval pairs z.2 (radicalPhaseEval radicals z.1 c)))
  rw [integerSum_cartesian] at h
  simpa [canonicalVectorWalshSum, canonicalPhaseOnVector, explicitCanonicalSum, explicitPairSum,
    List.map_map, Function.comp_def, hp, hr] using h

theorem canonicalVectorWalshSum_closed {k m : Nat} (pairs : List (Bool × Bool)) (radicals : List Bool)
    (c : Bool) (hp : pairs.length = k) (hr : radicals.length = m) :
    canonicalVectorWalshSum (k := k) (m := m) pairs radicals c =
      if radicals.any id then 0 else (2 : Int)^(m+k) *
        integerWalshSign (Bool.xor c (hyperbolicSignature pairs)) := by
  rw [canonicalVectorWalshSum_eq pairs radicals c hp hr, explicitCanonicalSum_closed, hp, hr]

end SectorSimulation
