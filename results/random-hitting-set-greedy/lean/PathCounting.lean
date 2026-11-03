import DeterministicExchange

/-! Counting the seven-row paths: each bad middle has exactly eight ordered
representations. -/
set_option maxHeartbeats 2000000
namespace ADG
open Finset
attribute [local instance] Classical.propDecidable

def pathEquivalent {m : ℕ} (t u : PathTuple m) : Prop :=
  pathMiddle t = pathMiddle u ∧
  ((pathLeft t = pathLeft u ∧ pathRight t = pathRight u) ∨
   (pathLeft t = pathRight u ∧ pathRight t = pathLeft u))

instance {m : ℕ} (t u : PathTuple m) : Decidable (pathEquivalent t u) := by
  unfold pathEquivalent
  infer_instance

lemma path_left_middle {m : ℕ} (t : PathTuple m) :
    pathLeft t ∩ pathMiddle t = {t 2} := by
  have h : ({0,1,2} ∩ {2,3,4} : Finset (Fin 7)) = {2} := by decide
  have hi := congrArg (fun s : Finset (Fin 7) => s.image t) h
  simpa only [image_inter _ _ t.injective, image_insert, image_singleton,
    pathLeft, pathMiddle] using hi

lemma path_right_middle {m : ℕ} (t : PathTuple m) :
    pathRight t ∩ pathMiddle t = {t 4} := by
  have h : ({4,5,6} ∩ {2,3,4} : Finset (Fin 7)) = {4} := by decide
  have hi := congrArg (fun s : Finset (Fin 7) => s.image t) h
  simpa only [image_inter _ _ t.injective, image_insert, image_singleton,
    pathRight, pathMiddle] using hi

lemma path_left_sdiff {m : ℕ} (t : PathTuple m) :
    pathLeft t \ pathMiddle t = {t 0,t 1} := by
  have h : ({0,1,2} \ {2,3,4} : Finset (Fin 7)) = {0,1} := by decide
  have hi := congrArg (fun s : Finset (Fin 7) => s.image t) h
  simpa only [image_sdiff _ _ t.injective, image_insert, image_singleton,
    pathLeft, pathMiddle] using hi

lemma path_right_sdiff {m : ℕ} (t : PathTuple m) :
    pathRight t \ pathMiddle t = {t 5,t 6} := by
  have h : ({4,5,6} \ {2,3,4} : Finset (Fin 7)) = {5,6} := by decide
  have hi := congrArg (fun s : Finset (Fin 7) => s.image t) h
  simpa only [image_sdiff _ _ t.injective, image_insert, image_singleton,
    pathRight, pathMiddle] using hi

lemma pair_eq_pair {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) (h : ({a,b} : Finset α) = {c,d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha' : a ∈ ({c,d} : Finset α) := h ▸ (by simp : a ∈ ({a,b} : Finset α))
  have hb' : b ∈ ({c,d} : Finset α) := h ▸ (by simp : b ∈ ({a,b} : Finset α))
  have ha : a = c ∨ a = d := by simpa using ha'
  have hb : b = c ∨ b = d := by simpa using hb'
  aesop

lemma oriented_coords {m : ℕ} {t u : PathTuple m}
    (hL : pathLeft t = pathLeft u) (hM : pathMiddle t = pathMiddle u)
    (hR : pathRight t = pathRight u) :
    u 2 = t 2 ∧ u 3 = t 3 ∧ u 4 = t 4 ∧
    ((u 0 = t 0 ∧ u 1 = t 1) ∨ (u 0 = t 1 ∧ u 1 = t 0)) ∧
    ((u 5 = t 5 ∧ u 6 = t 6) ∨ (u 5 = t 6 ∧ u 6 = t 5)) := by
  have h2 : u 2 = t 2 := by
    apply Eq.symm
    apply singleton_inj.mp
    rw [← path_left_middle t, ← path_left_middle u, hL, hM]
  have h4 : u 4 = t 4 := by
    apply Eq.symm
    apply singleton_inj.mp
    rw [← path_right_middle t, ← path_right_middle u, hR, hM]
  have h3 : u 3 = t 3 := by
    have hx : u 3 ∈ pathMiddle t := hM ▸ (by simp [pathMiddle])
    have hn2 : u 3 ≠ t 2 := by rw [← h2]; exact u.injective.ne (by decide)
    have hn4 : u 3 ≠ t 4 := by rw [← h4]; exact u.injective.ne (by decide)
    simp only [pathMiddle, mem_insert, mem_singleton] at hx
    aesop
  have h01 : ({u 0,u 1} : Finset (Fin m)) = {t 0,t 1} := by
    rw [← path_left_sdiff u, ← path_left_sdiff t, hL, hM]
  have h56 : ({u 5,u 6} : Finset (Fin m)) = {t 5,t 6} := by
    rw [← path_right_sdiff u, ← path_right_sdiff t, hR, hM]
  exact ⟨h2,h3,h4,pair_eq_pair (u.injective.ne (by decide))
    (t.injective.ne (by decide)) h01,pair_eq_pair (u.injective.ne (by decide))
    (t.injective.ne (by decide)) h56⟩

def pathPermutation (v : Bool × Bool × Bool) : Equiv.Perm (Fin 7) :=
  ((if v.1 then Equiv.swap 0 1 else Equiv.refl _).trans
    (if v.2.1 then Equiv.swap 5 6 else Equiv.refl _)).trans
    (if v.2.2 then Fin.revPerm else Equiv.refl _)

def pathVariant {m : ℕ} (t : PathTuple m) (v : Bool × Bool × Bool) : PathTuple m :=
  (pathPermutation v).toEmbedding.trans t

lemma pathVariant_equivalent {m : ℕ} (t : PathTuple m) (v : Bool × Bool × Bool) :
    pathEquivalent t (pathVariant t v) := by
  have hp : ∀ v : Bool × Bool × Bool,
      ({2,3,4} : Finset (Fin 7)).image (pathPermutation v) = {2,3,4} ∧
      ((({0,1,2} : Finset (Fin 7)).image (pathPermutation v) = {0,1,2} ∧
        ({4,5,6} : Finset (Fin 7)).image (pathPermutation v) = {4,5,6}) ∨
       (({0,1,2} : Finset (Fin 7)).image (pathPermutation v) = {4,5,6} ∧
        ({4,5,6} : Finset (Fin 7)).image (pathPermutation v) = {0,1,2})) := by decide
  obtain ⟨hM,hP⟩ := hp v
  constructor
  · have h := congrArg (fun s : Finset (Fin 7) => s.image t) hM.symm
    simpa [image_image,pathMiddle,pathVariant] using h
  · rcases hP with ⟨hL,hR⟩ | ⟨hL,hR⟩
    · left
      constructor
      · have h := congrArg (fun s : Finset (Fin 7) => s.image t) hL.symm
        simpa [image_image,pathLeft,pathVariant] using h
      · have h := congrArg (fun s : Finset (Fin 7) => s.image t) hR.symm
        simpa [image_image,pathRight,pathVariant] using h
    · right
      constructor
      · have h := congrArg (fun s : Finset (Fin 7) => s.image t) hR.symm
        simpa [image_image,pathLeft,pathRight,pathVariant] using h
      · have h := congrArg (fun s : Finset (Fin 7) => s.image t) hL.symm
        simpa [image_image,pathLeft,pathRight,pathVariant] using h

lemma pathVariant_injective {m : ℕ} (t : PathTuple m) :
    Function.Injective (pathVariant t) := by
  intro a b h
  have hp : pathPermutation a = pathPermutation b := by
    apply Equiv.ext
    intro i
    exact t.injective (congrArg (fun e : PathTuple m => e i) h)
  have hinj : Function.Injective pathPermutation := by decide
  exact hinj hp

lemma oriented_variant {m : ℕ} {t u : PathTuple m}
    (hL : pathLeft t = pathLeft u) (hM : pathMiddle t = pathMiddle u)
    (hR : pathRight t = pathRight u) :
    ∃ a b : Bool, u = pathVariant t (a,b,false) := by
  obtain ⟨h2,h3,h4,h01,h56⟩ := oriented_coords hL hM hR
  rcases h01 with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;>
    rcases h56 with ⟨h5,h6⟩ | ⟨h5,h6⟩
  · refine ⟨false,false,?_⟩
    apply Function.Embedding.ext
    intro i; fin_cases i <;> assumption
  · refine ⟨false,true,?_⟩
    apply Function.Embedding.ext
    intro i; fin_cases i <;> assumption
  · refine ⟨true,false,?_⟩
    apply Function.Embedding.ext
    intro i; fin_cases i <;> assumption
  · refine ⟨true,true,?_⟩
    apply Function.Embedding.ext
    intro i; fin_cases i <;> assumption

lemma equivalent_is_variant {m : ℕ} {t u : PathTuple m}
    (h : pathEquivalent t u) : ∃ v, u = pathVariant t v := by
  obtain ⟨hM,hP⟩ := h
  rcases hP with ⟨hL,hR⟩ | ⟨hL,hR⟩
  · obtain ⟨a,b,h⟩ := oriented_variant hL hM hR
    exact ⟨(a,b,false),h⟩
  · let r := pathVariant t (false,false,true)
    have hrL : pathLeft r = pathRight t := by
      have hp : ({0,1,2} : Finset (Fin 7)).image
          (pathPermutation (false,false,true)) = {4,5,6} := by decide
      have he := congrArg (fun s : Finset (Fin 7) => s.image t) hp
      simpa [r,pathVariant,pathLeft,pathRight,image_image] using he
    have hrM : pathMiddle r = pathMiddle t := (pathVariant_equivalent t _).1.symm
    have hrR : pathRight r = pathLeft t := by
      have hp : ({4,5,6} : Finset (Fin 7)).image
          (pathPermutation (false,false,true)) = {0,1,2} := by decide
      have he := congrArg (fun s : Finset (Fin 7) => s.image t) hp
      simpa [r,pathVariant,pathLeft,pathRight,image_image] using he
    obtain ⟨a,b,hu⟩ := oriented_variant (hrL.trans hR) (hrM.trans hM) (hrR.trans hL)
    refine ⟨(a,b,true),hu.trans ?_⟩
    apply Function.Embedding.ext
    intro i
    apply congrArg t
    have he : ∀ (a b : Bool) (i : Fin 7),
        pathPermutation (false,false,true) (pathPermutation (a,b,false) i) =
          pathPermutation (a,b,true) i := by decide
    exact he a b i

lemma equivalent_path_count {m : ℕ} (t : PathTuple m) :
    (univ.filter (fun u : PathTuple m => pathEquivalent t u)).card = 8 := by
  classical
  have hs : univ.filter (fun u : PathTuple m => pathEquivalent t u) =
      univ.image (pathVariant t) := by
    ext u
    simp only [mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro h
      obtain ⟨v,rfl⟩ := equivalent_is_variant h
      exact ⟨v,rfl⟩
    · rintro ⟨v,rfl⟩
      exact pathVariant_equivalent t v
  rw [hs,card_image_of_injective _ (pathVariant_injective t)]
  decide

lemma same_middle_equivalent {m n : ℕ} (A : Matrix m n)
    (t u : PathTuple m) (l j r l' r' : Fin n)
    (ht : pathOccursAt A t l j r) (hu : pathOccursAt A u l' j r') :
    pathEquivalent t u := by
  have hm : pathMiddle t = pathMiddle u := ht.2.2.2.2.1.symm.trans hu.2.2.2.2.1
  have hlTouch : ¬Disjoint (A l') (pathRows t) := by
    intro hd
    apply (disjoint_left.mp hd) (a := u 2)
    · rw [hu.2.2.2.1]; simp [pathLeft]
    · apply pathMiddle_subset_rows t
      rw [hm]; simp [pathMiddle]
  have hrTouch : ¬Disjoint (A r') (pathRows t) := by
    intro hd
    apply (disjoint_left.mp hd) (a := u 4)
    · rw [hu.2.2.2.2.2.1]; simp [pathRight]
    · apply pathMiddle_subset_rows t
      rw [hm]; simp [pathMiddle]
  have hlChoice := pathOccursAt_isolation A t l j r ht l'
    (by rw [hu.2.2.2.1]; exact pathLeft_card u) hlTouch
  have hrChoice := pathOccursAt_isolation A t l j r ht r'
    (by rw [hu.2.2.2.2.2.1]; exact pathRight_card u) hrTouch
  have hl : l' = l ∨ l' = r := by
    rcases hlChoice with h|h|h
    · exact False.elim (ne_of_gt hu.1 h)
    · exact Or.inl h
    · exact Or.inr h
  have hr : r' = l ∨ r' = r := by
    rcases hrChoice with h|h|h
    · exact False.elim (ne_of_gt hu.2.1 h)
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨hm, ?_⟩
  rcases hl with hl|hl <;> rcases hr with hr|hr
  · exact False.elim (hu.2.2.1 (hl.trans hr.symm))
  · left; constructor
    · exact ht.2.2.2.1.symm.trans (hl ▸ hu.2.2.2.1)
    · exact ht.2.2.2.2.2.1.symm.trans (hr ▸ hu.2.2.2.2.2.1)
  · right; constructor
    · exact ht.2.2.2.1.symm.trans (hr ▸ hu.2.2.2.2.2.1)
    · exact ht.2.2.2.2.2.1.symm.trans (hl ▸ hu.2.2.2.1)
  · exact False.elim (hu.2.2.1 (hl.trans hr.symm))

lemma equivalent_rows {m : ℕ} {t u : PathTuple m} (h : pathEquivalent t u) :
    pathRows t = pathRows u := by
  rw [pathRows_eq_union,pathRows_eq_union,h.1]
  rcases h.2 with h|h
  · rw [h.1,h.2]
  · rw [h.1,h.2]; ext i; simp; tauto

lemma equivalent_occursAt {m n : ℕ} (A : Matrix m n) (t u : PathTuple m)
    (he : pathEquivalent t u) (l j r : Fin n) (ht : pathOccursAt A t l j r) :
    ∃ l' r', pathOccursAt A u l' j r' := by
  have hF : pathForbidden t = pathForbidden u := by
    unfold pathForbidden; rw [equivalent_rows he]
  rcases he.2 with h|h
  · refine ⟨l,r,ht.1,ht.2.1,ht.2.2.1,?_,?_,?_,?_⟩
    · exact ht.2.2.2.1.trans h.1
    · exact ht.2.2.2.2.1.trans he.1
    · exact ht.2.2.2.2.2.1.trans h.2
    · intro c hl hj hr; rw [← hF]; exact ht.2.2.2.2.2.2 c hl hj hr
  · refine ⟨r,l,ht.2.1,ht.1,ht.2.2.1.symm,?_,?_,?_,?_⟩
    · exact ht.2.2.2.2.2.1.trans h.2
    · exact ht.2.2.2.2.1.trans he.1
    · exact ht.2.2.2.1.trans h.1
    · intro c hr hj hl; rw [← hF]; exact ht.2.2.2.2.2.2 c hl hj hr

lemma middle_unique {m n : ℕ} (A : Matrix m n) (t : PathTuple m)
    (l j r l' j' r' : Fin n) (h : pathOccursAt A t l j r)
    (h' : pathOccursAt A t l' j' r') : j = j' := by
  have ht : ¬Disjoint (A j') (pathRows t) := by
    intro hd
    apply (disjoint_left.mp hd) (a := t 2)
    · rw [h'.2.2.2.2.1]; simp [pathMiddle]
    · simp [pathRows]
  rcases pathOccursAt_isolation A t l j r h j'
    (by rw [h'.2.2.2.2.1]; exact pathMiddle_card t) ht with hj|hl|hr
  · exact hj.symm
  · have he : pathLeft t = pathMiddle t := h.2.2.2.1.symm.trans (hl ▸ h'.2.2.2.2.1)
    have hmem : t 0 ∈ pathMiddle t := he ▸ (by simp [pathLeft])
    simpa [pathMiddle,t.injective.eq_iff] using hmem
  · have he : pathRight t = pathMiddle t := h.2.2.2.2.2.1.symm.trans (hr ▸ h'.2.2.2.2.1)
    have hmem : t 6 ∈ pathMiddle t := he ▸ (by simp [pathRight])
    simpa [pathMiddle,t.injective.eq_iff] using hmem

def middleOccurs {m n : ℕ} (A : Matrix m n) (t : PathTuple m) (j : Fin n) : Prop :=
  ∃ l r, pathOccursAt A t l j r

lemma pathOccurs_iff_middle {m n : ℕ} (A : Matrix m n) (t : PathTuple m) :
    pathOccurs A t ↔ ∃ j, middleOccurs A t j := by
  unfold pathOccurs exactlyOnceMiddleFirst middleOccurs pathOccursAt
  constructor
  · rintro ⟨l,j,r,h⟩; exact ⟨j,l,r,h⟩
  · rintro ⟨j,l,r,h⟩; exact ⟨l,j,r,h⟩

lemma middleOccurs_unique {m n : ℕ} (A : Matrix m n) (t : PathTuple m)
    {j j' : Fin n} (h : middleOccurs A t j) (h' : middleOccurs A t j') : j = j' := by
  obtain ⟨l,r,h⟩ := h
  obtain ⟨l',r',h'⟩ := h'
  exact middle_unique A t l j r l' j' r' h h'

lemma middle_fiber_card {m n : ℕ} (A : Matrix m n) (j : Fin n) :
    (univ.filter (fun t : PathTuple m => middleOccurs A t j)).card =
      if j ∈ badMiddles A then 8 else 0 := by
  classical
  by_cases hj : j ∈ badMiddles A
  · rw [if_pos hj]
    obtain ⟨t,l,r,ht⟩ := (mem_filter.mp hj).2
    have he : univ.filter (fun u : PathTuple m => middleOccurs A u j) =
        univ.filter (fun u => pathEquivalent t u) := by
      ext u
      simp only [mem_filter,mem_univ,true_and]
      constructor
      · rintro ⟨l',r',hu⟩
        exact same_middle_equivalent A t u l j r l' r' ht hu
      · intro hu
        exact equivalent_occursAt A t u hu l j r ht
    rw [he]; exact equivalent_path_count t
  · rw [if_neg hj]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro t ht
    obtain ⟨l,r,ht⟩ := (mem_filter.mp ht).2
    exact hj (mem_filter.mpr ⟨mem_univ _, t,l,r,ht⟩)

lemma tuple_middle_fiber_card {m n : ℕ} (A : Matrix m n) (t : PathTuple m) :
    (univ.filter (fun j : Fin n => middleOccurs A t j)).card =
      if pathOccurs A t then 1 else 0 := by
  classical
  by_cases ht : pathOccurs A t
  · rw [if_pos ht]
    obtain ⟨j,hj⟩ := (pathOccurs_iff_middle A t).mp ht
    have he : univ.filter (fun j' => middleOccurs A t j') = {j} := by
      ext j'
      simp only [mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro h; exact middleOccurs_unique A t h hj
      · rintro rfl; exact hj
    rw [he]; simp
  · rw [if_neg ht]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro j hj
    exact ht ((pathOccurs_iff_middle A t).mpr ⟨j,(mem_filter.mp hj).2⟩)

/-- Exact eightfold multiplicity for actual isolated-path occurrences. -/
theorem orderedPathCount_eq_eight_B {m n : ℕ} (A : Matrix m n) :
    orderedPathCount A = 8 * B A := by
  classical
  have hs : (∑ t : PathTuple m, (univ.filter (fun j : Fin n => middleOccurs A t j)).card) =
      ∑ j : Fin n, (univ.filter (fun t : PathTuple m => middleOccurs A t j)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    exact sum_comm
  rw [show orderedPathCount A = ∑ t : PathTuple m, if pathOccurs A t then 1 else 0 by
    simp only [orderedPathCount,card_eq_sum_ones,sum_filter]]
  simp_rw [← tuple_middle_fiber_card A]
  rw [hs]
  simp_rw [middle_fiber_card A]
  simp only [B,badMiddles,card_eq_sum_ones,sum_filter,mul_sum]
  apply sum_congr rfl
  intro j hj
  simp only [mem_filter,mem_univ,true_and]
  split_ifs <;> norm_num

end ADG
