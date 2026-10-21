import R3P10.Defs

/-! # Edges, edge indices, colour vectors and the generator action -/

namespace R3P10

variable {n : ℕ}

theorem mem_edges {a b : ℕ} : (a, b) ∈ edges n ↔ a < b ∧ b < n := by
  simp only [edges, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    split_ifs at h with hij
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · rintro ⟨hab, hb⟩
    exact ⟨a, by omega, b, hb, by simp [hab]⟩

theorem nodup_edges : (edges n).Nodup := by
  unfold edges
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · refine List.Nodup.filterMap ?_ List.nodup_range
    intro a b c ha hb
    split_ifs at ha hb <;> simp only [Option.mem_def, Option.some.injEq, reduceCtorEq] at ha hb
    rw [← hb] at ha; exact (Prod.mk.injEq _ _ _ _ ▸ ha).2
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
    intro a b _ _ hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    simp only [List.mem_filterMap, List.mem_range] at hx hy
    obtain ⟨j, _, hj⟩ := hx
    obtain ⟨j', _, hj'⟩ := hy
    split_ifs at hj hj'
    simp only [Option.some.injEq] at hj hj'
    rw [← hj'] at hj; exact hab (Prod.mk.inj hj).1

theorem eidx_comm (u v : ℕ) : eidx n u v = eidx n v u := by
  simp [eidx, min_comm, max_comm]

theorem eidx_lt {u v : ℕ} (huv : u ≠ v) (hu : u < n) (hv : v < n) :
    eidx n u v < (edges n).length := by
  unfold eidx
  rw [List.idxOf_lt_length_iff, mem_edges]
  omega

theorem getElem_eidx {u v : ℕ} (huv : u ≠ v) (hu : u < n) (hv : v < n) :
    (edges n)[eidx n u v]'(eidx_lt huv hu hv) = (min u v, max u v) :=
  List.getElem_idxOf _

theorem getD_eidx {u v : ℕ} (huv : u ≠ v) (hu : u < n) (hv : v < n) :
    (edges n).getD (eidx n u v) (0, 0) = (min u v, max u v) := by
  rw [List.getD_eq_getElem _ _ (eidx_lt huv hu hv), getElem_eidx huv hu hv]

theorem edge_spec {k : ℕ} (hk : k < (edges n).length) :
    ((edges n).getD k (0, 0)).1 < ((edges n).getD k (0, 0)).2 ∧
      ((edges n).getD k (0, 0)).2 < n := by
  rw [List.getD_eq_getElem _ _ hk]
  exact mem_edges.1 (List.getElem_mem hk)

theorem eidx_getD {k : ℕ} (hk : k < (edges n).length) :
    eidx n ((edges n).getD k (0, 0)).1 ((edges n).getD k (0, 0)).2 = k := by
  have h := edge_spec hk
  rw [List.getD_eq_getElem _ _ hk] at h ⊢
  unfold eidx
  rw [min_eq_left h.1.le, max_eq_right h.1.le]
  exact nodup_edges.idxOf_getElem k hk

/-! ## Colours of pairs and of edge positions -/

/-- The colour of pair `{a, b}` (0 when out of range). -/
def colOf (X : Col n) (a b : ℕ) : Fin 3 :=
  if h : a < n ∧ b < n then X s(⟨a, h.1⟩, ⟨b, h.2⟩) else 0

/-- The colour of edge number `k`. -/
def vec (X : Col n) (k : ℕ) : Fin 3 :=
  colOf X ((edges n).getD k (0, 0)).1 ((edges n).getD k (0, 0)).2

theorem colOf_comm (X : Col n) (a b : ℕ) : colOf X a b = colOf X b a := by
  unfold colOf
  by_cases h : a < n ∧ b < n
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩, Sym2.eq_swap]
  · rw [dif_neg h, dif_neg (by tauto)]

theorem vec_eidx (X : Col n) {u v : ℕ} (huv : u ≠ v) (hu : u < n) (hv : v < n) :
    vec X (eidx n u v) = colOf X u v := by
  unfold vec
  rw [getD_eidx huv hu hv]
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, colOf_comm]

/-! ## The generator action -/

/-- `(act g X) {π a, π b} = σ (X {a, b})`. -/
def act (g : Gen n) (X : Col n) : Col n := fun z => g.col (X (Sym2.map g.perm.symm z))

theorem permN_lt (π : Equiv.Perm (Fin n)) {a : ℕ} (ha : a < n) : permN π a < n := by
  simp [permN, ha]

theorem permN_inj (π : Equiv.Perm (Fin n)) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : permN π a = permN π b) : a = b := by
  simp only [permN, ha, hb, dif_pos] at h
  have := π.injective (Fin.ext h)
  simpa using this

theorem colOf_act (g : Gen n) (X : Col n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    colOf (act g X) a b = g.col (colOf X (permN g.perm.symm a) (permN g.perm.symm b)) := by
  simp [colOf, act, ha, hb, permN]

theorem src_lt (g : Gen n) {k : ℕ} (hk : k < (edges n).length) : src g k < (edges n).length := by
  have h := edge_spec hk
  unfold src
  exact eidx_lt (fun e => by have := permN_inj _ (by omega) h.2 e; omega)
    (permN_lt _ (by omega)) (permN_lt _ h.2)

theorem vec_act (g : Gen n) (X : Col n) {k : ℕ} (hk : k < (edges n).length) :
    vec (act g X) k = g.col (vec X (src g k)) := by
  have h := edge_spec hk
  unfold src
  rw [vec_eidx X (fun e => by have := permN_inj _ (by omega) h.2 e; omega)
    (permN_lt _ (by omega)) (permN_lt _ h.2)]
  exact colOf_act g X (by omega) h.2

theorem vec_act_of_skip (g : Gen n) (X : Col n) {k : ℕ} (hk : k < (edges n).length)
    (hs : skip g k = true) : vec (act g X) k = vec X k := by
  simp only [skip, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at hs
  rw [vec_act g X hk, hs.1]
  exact hs.2 _

end R3P10
