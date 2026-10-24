import ExtensionStatement

namespace LitOnlySigma

instance typeA_decidable (x : Configuration 7) : Decidable (TypeA x) := by
  unfold TypeA antipodalPair
  infer_instance
instance typeB_decidable (x : Configuration 7) : Decidable (TypeB x) := by
  unfold TypeB
  infer_instance
instance typeC_decidable (x : Configuration 7) : Decidable (TypeC x) := by
  unfold TypeC
  infer_instance

/-- Counts in the ten distinct states; membership equivalence below makes these exact. -/
theorem type_counts :
    (Finset.univ.filter fun i : Fin 10 => TypeA (decode (closedCodes i))).card = 3 ∧
    (Finset.univ.filter fun i : Fin 10 => TypeB (decode (closedCodes i))).card = 1 ∧
    (Finset.univ.filter fun i : Fin 10 => TypeC (decode (closedCodes i))).card = 6 ∧
    Function.Injective (fun i : Fin 10 => decode (closedCodes i)) ∧
    (∀ i : Fin 10, ¬ (TypeA (decode (closedCodes i)) ∧ TypeB (decode (closedCodes i))) ∧
      ¬ (TypeA (decode (closedCodes i)) ∧ TypeC (decode (closedCodes i))) ∧
      ¬ (TypeB (decode (closedCodes i)) ∧ TypeC (decode (closedCodes i)))) := by
  unfold Function.Injective
  decide

theorem type_weights : ∀ i : Fin 10,
    (TypeA (decode (closedCodes i)) → lightNumber (decode (closedCodes i)) = 4) ∧
    (TypeB (decode (closedCodes i)) → lightNumber (decode (closedCodes i)) = 6) ∧
    (TypeC (decode (closedCodes i)) → lightNumber (decode (closedCodes i)) = 4) := by decide

/-- Rotation/reflection of the outer cycle; the hub is fixed. -/
def cycleSymmetry (k : Fin 6) (reflect : Bool) (v : Fin 7) : Fin 7 :=
  if v.val < 6 then
    ⟨(k.val + if reflect then 6 - v.val else v.val) % 6,
      Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩
  else 6

def transform (k : Fin 6) (reflect : Bool) (x : Configuration 7) : Configuration 7 :=
  fun v => x (cycleSymmetry k reflect v)

/-- Five representatives for a state together with a permitted played vertex. -/
def representativeCode : Fin 5 → ℕ := ![27, 63, 71, 71, 71]
def representativeMove : Fin 5 → Fin 7 := ![0, 0, 0, 1, 6]

theorem symmetry_graph : ∀ k reflect u v,
    graph (cycleSymmetry k reflect u) (cycleSymmetry k reflect v) = graph u v := by
  decide

theorem symmetry_bijective : ∀ k reflect, Function.Bijective (cycleSymmetry k reflect) := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide

theorem transform_regular (k : Fin 6) (reflect : Bool) (x : Configuration 7) (v : Fin 7) :
    regularMove graph (transform k reflect x) v =
      transform k reflect (regularMove graph x (cycleSymmetry k reflect v)) := by
  funext w
  simp only [regularMove, transform, symmetry_graph]

theorem transform_litOnly (k : Fin 6) (reflect : Bool) (x : Configuration 7) (v : Fin 7) :
    litOnlyMove graph (transform k reflect x) v =
      transform k reflect (litOnlyMove graph x (cycleSymmetry k reflect v)) := by
  cases h : x (cycleSymmetry k reflect v)
  · simp [litOnlyMove, transform, h]
  · simpa only [litOnlyMove, transform, h, Bool.true_eq_false, reduceIte] using
      transform_regular k reflect x v

theorem certificate_type_membership : ∀ i : Fin 10, ThreeTypes (decode (closedCodes i)) := by
  unfold ThreeTypes TypeA TypeB TypeC antipodalPair
  decide

/-- Every proposed type equals one of the ten configurations (function extensionality). -/
theorem types_in_certificate {x : Configuration 7} (h : ThreeTypes x) : InCertificate x := by
  have bool_ext : ∀ a b : Bool, (a = true ↔ b = true) → a = b := by decide
  rcases h with ⟨o, ho⟩ | hb | ⟨s, hs⟩
  · have : ∀ o : Fin 3, ∃ i : Fin 10, ∀ v,
        decode (closedCodes i) v = true ↔
          ∃ j : Fin 3, j ≠ o ∧ antipodalPair j v := by
      unfold antipodalPair
      decide
    obtain ⟨i, hi⟩ := this o
    exact ⟨i, funext fun v => bool_ext _ _ ((ho v).trans (hi v).symm)⟩
  · exact ⟨3, funext fun v => bool_ext _ _ ((hb v).trans
      ((by decide : ∀ v : Fin 7, decode (closedCodes 3) v = true ↔ v.val < 6) v).symm)⟩
  · have : ∀ s : Fin 6, ∃ i : Fin 10, ∀ v,
        decode (closedCodes i) v = true ↔
          v = 6 ∨ ∃ j : Fin 3, v.val = (s.val + j.val) % 6 := by decide
    obtain ⟨i, hi⟩ := this s
    exact ⟨i, funext fun v => bool_ext _ _ ((hs v).trans (hi v).symm)⟩

theorem certificate_iff_types (x : Configuration 7) : InCertificate x ↔ ThreeTypes x := by
  constructor
  · rintro ⟨i, rfl⟩
    exact certificate_type_membership i
  · exact types_in_certificate

/-- Exhaustive cover of all legal moves, not an assumption about their orbits. -/
theorem five_representatives_cover : ∀ i : Fin 10, ∀ v : Fin 7,
    decode (closedCodes i) v = true →
    ∃ k : Fin 6, ∃ reflect : Bool, ∃ r : Fin 5,
      decode (closedCodes i) = transform k reflect (decode (representativeCode r)) ∧
      cycleSymmetry k reflect v = representativeMove r := by decide

/-- Removing the first representative leaves a gap in the legal-move cover. -/
theorem rejects_missing_representative : ¬ (∀ i : Fin 10, ∀ v : Fin 7,
    decode (closedCodes i) v = true →
    ∃ k : Fin 6, ∃ reflect : Bool, ∃ r : Fin 5, r ≠ 0 ∧
      decode (closedCodes i) = transform k reflect (decode (representativeCode r)) ∧
      cycleSymmetry k reflect v = representativeMove r) := by decide

theorem representative_successors : ∀ r : Fin 5,
    litOnlyMove graph (decode (representativeCode r)) (representativeMove r) =
      decode ((![71, 99, 27, 63, 120] : Fin 5 → ℕ) r) := by decide

theorem transformed_successor_in_certificate : ∀ k reflect r,
    InCertificate (transform k reflect
      (decode ((![71, 99, 27, 63, 120] : Fin 5 → ℕ) r))) := by
  unfold InCertificate
  decide

theorem types_closed {x : Configuration 7} (h : ThreeTypes x) (v : Fin 7) :
    ThreeTypes (litOnlyMove graph x v) := by
  apply (certificate_iff_types _).mp
  obtain ⟨i, rfl⟩ := types_in_certificate h
  cases hv : decode (closedCodes i) v with
  | false => simpa [litOnlyMove, hv] using (show InCertificate (decode (closedCodes i)) from ⟨i, rfl⟩)
  | true =>
    obtain ⟨k, reflect, r, hx, hmove⟩ := five_representatives_cover i v hv
    rw [hx, transform_litOnly, hmove, representative_successors]
    exact transformed_successor_in_certificate k reflect r

/-- Explicit finite paths show the set is the orbit, not merely a closed superset. -/
def orbitPath : Fin 10 → List (Fin 7) :=
  ![[], [1, 5], [0, 2], [0, 1], [0], [0, 1, 2],
    [4], [1], [0, 1, 5], [3]]

def playList (x : Configuration 7) (vs : List (Fin 7)) : Configuration 7 :=
  vs.foldl (litOnlyMove graph) x

/-- True exactly when each listed play is at a light that is currently on. -/
def orbitPathLegal (x : Configuration 7) : List (Fin 7) → Bool
  | [] => true
  | v :: vs => x v && orbitPathLegal (litOnlyMove graph x v) vs

theorem orbit_paths_legal : ∀ i : Fin 10, orbitPathLegal start (orbitPath i) = true := by
  decide

theorem orbit_paths_correct : ∀ i : Fin 10,
    playList start (orbitPath i) = decode (closedCodes i) := by decide

theorem playList_reachable (x : Configuration 7) (vs : List (Fin 7)) :
    Reachable (litOnlyMove graph) x (playList x vs) := by
  induction vs generalizing x with
  | nil => exact .refl
  | cons v vs ih =>
    exact (Relation.ReflTransGen.single ⟨v, rfl⟩).trans (ih (litOnlyMove graph x v))

theorem orbit_iff_types (x : Configuration 7) :
    Reachable (litOnlyMove graph) start x ↔ ThreeTypes x := by
  constructor
  · exact fun h => (certificate_iff_types x).mp (reachable_in_certificate h)
  · intro h
    obtain ⟨i, rfl⟩ := types_in_certificate h
    rw [← orbit_paths_correct i]
    exact playList_reachable _ _

theorem three_type_description : ThreeTypeStatement := by
  exact ⟨certificate_iff_types, orbit_iff_types, fun _ v h => types_closed h v,
    by unfold TypeA antipodalPair; decide, start_weight, regular_path⟩

end LitOnlySigma
