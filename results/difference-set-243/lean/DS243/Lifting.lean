import DS243.Singleton
import DS243.Counting

/-!
# Lifting: a normalized fixed set is a leaf of the frozen search tree

`leaf c w` is the 121-element candidate of `campaign.cpp` for case `c` (row `c` of the pinned
`cases.txt`) and the 24 ternary digits `w`. It is the frozen singleton set together with, for
each of the 24 nonspecial cells in the search order (coefficient-6 cells by increasing cell
index, then coefficient-3 cells by increasing cell index), the option chosen by its digit:
for a coefficient-3 cell the digit names the one 61-orbit taken, and for a coefficient-6 cell the
one 61-orbit omitted, the three orbits of a cell being ordered by least encoded element
(`81x + 9y + z`).
-/

namespace DS243

open Finset

/-- Encoding `81x + 9y + z` of `campaign.cpp`. -/
def encG (p : G) : ℕ := 81 * p.1.val + 9 * p.2.1.val + p.2.2.val

/-- Decoding of `encG`. -/
def decG (e : ℕ) : G := (((e / 81 : ℕ) : ZMod 3), ((e / 9 % 9 : ℕ) : ZMod 9), ((e % 9 : ℕ) : ZMod 9))

/-- Cell index `9x + 3(y mod 3) + (z mod 3)` of an encoded element. -/
def cellIdx (e : ℕ) : ℕ := 9 * (e / 81) + 3 * (e / 9 % 3) + e % 3

/-- The eight frozen quotient images (`cases.txt`, weights dropped), indexed by cell. -/
def caseRows : List (List ℕ) :=
  [[4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 6, 6, 3, 6, 6, 3, 6, 6, 3, 3, 3, 3, 6, 3, 3, 6],
   [4, 6, 3, 6, 6, 3, 3, 6, 3, 3, 6, 6, 6, 3, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 6, 6],
   [4, 3, 6, 6, 6, 6, 3, 3, 3, 3, 6, 6, 6, 6, 3, 6, 6, 3, 6, 3, 3, 3, 6, 3, 3, 6, 3],
   [4, 3, 6, 6, 3, 6, 3, 3, 6, 3, 6, 6, 6, 3, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 6, 6],
   [4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 3, 6, 3, 3, 6, 3, 3, 6, 6, 3, 3, 6, 6, 3, 6, 6],
   [4, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 6, 6, 3, 3, 6, 3, 3, 6, 3, 6, 3, 6, 6, 3, 6, 6],
   [4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 6, 3, 6, 6, 6, 6, 3, 6, 3, 3, 3, 6, 3, 6, 3, 3],
   [4, 6, 3, 6, 3, 6, 3, 3, 6, 3, 6, 6, 3, 3, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 6, 3, 6]]

/-- Coefficient of case `c` at cell `q`. -/
def caseCoef (c q : ℕ) : ℕ := (caseRows.getD c []).getD q 0

/-- The 61-orbit of an encoded element, as encoded elements. -/
def orbitE (e : ℕ) : List ℕ := [e, encG ((61 : ℕ) • decG e), encG ((3721 : ℕ) • decG e)]

/-- The three 61-orbits of a nonspecial cell, as their least elements, increasing. -/
def bucket (j : ℕ) : List ℕ :=
  (List.range 243).filter fun e => cellIdx e == j && (orbitE e).all (e ≤ ·)

/-- The 24 nonspecial cells of case `c` in search order. -/
def positions (c : ℕ) : List ℕ :=
  ((List.range 27).filter fun j => j % 9 != 0 && caseCoef c j == 6) ++
  ((List.range 27).filter fun j => j % 9 != 0 && caseCoef c j == 3)

/-- Least elements of the orbits chosen by digit `a` at search position `pos`. -/
def optionLeaders (c pos a : ℕ) : List ℕ :=
  let j := (positions c).getD pos 0
  let b := bucket j
  if caseCoef c j == 3 then [b.getD a 0]
  else (List.range 3).filter (· != a) |>.map fun i => b.getD i 0

/-- The leaf of case `c` with digits `w`. -/
def leaf (c : ℕ) (w : Fin 24 → Fin 3) : Finset G :=
  MaskSet ∪ (((List.finRange 24).flatMap fun pos =>
    (optionLeaders c pos.val (w pos).val).flatMap orbitE).map decG).toFinset

/-- Cell counts of the frozen case `c`, as a function of the cell. -/
def caseCount (c : ℕ) (q : ZMod 3 × ZMod 3 × ZMod 3) : ℕ :=
  caseCoef c (9 * q.1.val + 3 * q.2.1.val + q.2.2.val)

/-! ### Helper facts for `exists_leaf` -/

/-- Multiplication by `61` on `G`, in closed form. -/
def m61 (x : G) : G := (x.1, 7 * x.2.1, 7 * x.2.2)

/-- Multiplication by `3721 = 61²` on `G`, in closed form. -/
def m3721 (x : G) : G := (x.1, 4 * x.2.1, 4 * x.2.2)

lemma smul61 (x : G) : (61 : ℕ) • x = m61 x := by
  obtain ⟨a, b, c⟩ := x
  have h3 : ((61 : ℕ) : ZMod 3) = 1 := by decide
  have h9 : ((61 : ℕ) : ZMod 9) = 7 := by decide
  rw [Prod.smul_mk, Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, h3, h9, one_mul]
  rfl

lemma smul3721 (x : G) : (3721 : ℕ) • x = m3721 x := by
  obtain ⟨a, b, c⟩ := x
  have h3 : ((3721 : ℕ) : ZMod 3) = 1 := by decide
  have h9 : ((3721 : ℕ) : ZMod 9) = 4 := by decide
  rw [Prod.smul_mk, Prod.smul_mk, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, h3, h9, one_mul]
  rfl

/-- `x` lies in the 61-orbit `{y, 61 y, 3721 y}` of `y`. -/
def inOrb (x y : G) : Prop := x = y ∨ x = m61 y ∨ x = m3721 y

instance (x y : G) : Decidable (inOrb x y) :=
  inferInstanceAs (Decidable (x = y ∨ x = m61 y ∨ x = m3721 y))

/-- The orbit of `y` as a finset. -/
def orbF (y : G) : Finset G := {y, m61 y, m3721 y}

/-- The values of `bucket` (checked in `bucket_eq`). -/
def bucketTab : List (List ℕ) :=
  [[0, 3, 6, 27, 30, 33, 54, 57, 60], [1, 28, 55], [2, 29, 56], [9, 12, 15], [10, 13, 16],
   [11, 14, 17], [18, 21, 24], [19, 22, 25], [20, 23, 26],
   [81, 84, 87, 108, 111, 114, 135, 138, 141], [82, 109, 136], [83, 110, 137], [90, 93, 96],
   [91, 94, 97], [92, 95, 98], [99, 102, 105], [100, 103, 106], [101, 104, 107],
   [162, 165, 168, 189, 192, 195, 216, 219, 222], [163, 190, 217], [164, 191, 218],
   [171, 174, 177], [172, 175, 178], [173, 176, 179], [180, 183, 186], [181, 184, 187],
   [182, 185, 188]]

/-- The leader of orbit `i` of cell `j`, as an element of `G`. -/
def bL (j i : ℕ) : G := decG ((bucketTab.getD j []).getD i 0)

/-- The cell with index `j`. -/
def qOf (j : ℕ) : ZMod 3 × ZMod 3 × ZMod 3 := (((j / 9 : ℕ) : ZMod 3), ((j / 3 % 3 : ℕ) : ZMod 3),
  ((j % 3 : ℕ) : ZMod 3))

lemma orbitE_eq (e : ℕ) : orbitE e = [e, encG (m61 (decG e)), encG (m3721 (decG e))] := by
  rw [orbitE, smul61, smul3721]

lemma bucket_eq : ∀ j, j < 27 → bucket j = bucketTab.getD j [] := by
  have h : ∀ j, j < 27 → (List.range 243).filter (fun e => cellIdx e == j &&
      [e, encG (m61 (decG e)), encG (m3721 (decG e))].all (e ≤ ·)) = bucketTab.getD j [] := by
    decide +kernel
  intro j hj
  rw [← h j hj, bucket]
  simp only [orbitE_eq]

lemma decG_encG : ∀ x : G, decG (encG x) = x := by decide +kernel

lemma qOf_idx : ∀ j, j < 27 → 9 * (qOf j).1.val + 3 * (qOf j).2.1.val + (qOf j).2.2.val = j := by
  decide +kernel

lemma cell_fact : ∀ x : G, cellIdx (encG x) < 27 ∧ cell x = qOf (cellIdx (encG x)) := by
  decide +kernel

lemma H_fact : ∀ x : G, (3 • x = 0 ↔ cellIdx (encG x) % 9 = 0) := by
  decide +kernel

lemma m_fact : ∀ y : G, cellIdx (encG (m61 y)) = cellIdx (encG y) ∧
    cellIdx (encG (m3721 y)) = cellIdx (encG y) ∧ m3721 y = m61 (m61 y) ∧ m61 (m61 (m61 y)) = y := by
  decide +kernel

lemma cover_fact : ∀ x : G, cellIdx (encG x) % 9 ≠ 0 →
    (inOrb x (bL (cellIdx (encG x)) 0) ∨ inOrb x (bL (cellIdx (encG x)) 1) ∨
      inOrb x (bL (cellIdx (encG x)) 2)) := by
  decide +kernel

lemma leader_fact : ∀ j, j < 27 → j % 9 ≠ 0 → ∀ i : Fin 3, cellIdx (encG (bL j i)) = j := by
  decide +kernel

lemma leader_disj : ∀ j, j < 27 → j % 9 ≠ 0 → ∀ i i' : Fin 3, inOrb (bL j i) (bL j i') → i = i' := by
  decide +kernel

lemma card_fact : ∀ j, j < 27 → j % 9 ≠ 0 → ∀ b0 b1 b2 : Bool,
    ((if b0 then orbF (bL j 0) else ∅) ∪ (if b1 then orbF (bL j 1) else ∅) ∪
      (if b2 then orbF (bL j 2) else ∅)).card = 3 * (b0.toNat + b1.toNat + b2.toNat) := by
  decide +kernel

lemma pos_fact : ∀ c, c < 8 → (positions c).Nodup ∧ (positions c).length = 24 ∧
    (∀ j, j < 27 → j % 9 ≠ 0 → j ∈ positions c) ∧
    ∀ p : Fin 24, (positions c).getD p 0 < 27 ∧ (positions c).getD p 0 % 9 ≠ 0 ∧
      (caseCoef c ((positions c).getD p 0) = 3 ∨ caseCoef c ((positions c).getD p 0) = 6) := by
  decide +kernel

lemma m3721_eq (y : G) : m3721 y = m61 (m61 y) := (m_fact y).2.2.1

lemma m61_cube (y : G) : m61 (m61 (m61 y)) = y := (m_fact y).2.2.2

lemma inOrb_symm {x y : G} (h : inOrb x y) : inOrb y x := by
  rcases h with rfl | rfl | rfl
  · left; rfl
  · right; right; rw [m3721_eq, m61_cube]
  · right; left; rw [m3721_eq, m61_cube]

lemma inOrb_trans {x y z : G} (h1 : inOrb x y) (h2 : inOrb y z) : inOrb x z := by
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
    simp [inOrb, m3721_eq, m61_cube]

lemma cellIdx_inOrb {x y : G} (h : inOrb x y) : cellIdx (encG x) = cellIdx (encG y) := by
  rcases h with rfl | rfl | rfl
  · rfl
  · exact (m_fact y).1
  · exact (m_fact y).2.1

lemma mem_iff_of_inOrb {D : Finset G} (hF : Fixed D) {x y : G} (h : inOrb x y) :
    x ∈ D ↔ y ∈ D := by
  have hF' : ∀ z ∈ D, m61 z ∈ D := fun z hz => smul61 z ▸ hF z hz
  have h61 : ∀ z, m61 z ∈ D ↔ z ∈ D := fun z =>
    ⟨fun hz => by have := hF' _ (hF' _ hz); rwa [m61_cube] at this, hF' z⟩
  rcases h with rfl | rfl | rfl
  · rfl
  · exact h61 y
  · rw [m3721_eq, h61, h61]

lemma mem_orbF {x y : G} : x ∈ orbF y ↔ inOrb x y := by
  simp [orbF, inOrb]

lemma mem_ite_empty {x : G} {P : Prop} [Decidable P] {s : Finset G} :
    x ∈ (if P then s else ∅) ↔ P ∧ x ∈ s := by
  split_ifs with h <;> simp [h]

lemma cell_iff {j : ℕ} (hj : j < 27) (hj9 : j % 9 ≠ 0) (x : G) :
    cell x = qOf j ↔ inOrb x (bL j 0) ∨ inOrb x (bL j 1) ∨ inOrb x (bL j 2) := by
  obtain ⟨hlt, hc⟩ := cell_fact x
  constructor
  · intro h
    have e : cellIdx (encG x) = j := by
      rw [← qOf_idx _ hlt, ← qOf_idx _ hj, ← hc, h]
    have := cover_fact x (by rw [e]; exact hj9)
    rwa [e] at this
  · intro h
    have e : cellIdx (encG x) = j := by
      rcases h with h | h | h
      · rw [cellIdx_inOrb h]; exact leader_fact j hj hj9 0
      · rw [cellIdx_inOrb h]; exact leader_fact j hj hj9 1
      · rw [cellIdx_inOrb h]; exact leader_fact j hj hj9 2
    rw [hc, e]

lemma cellCount_eq {D : Finset G} (hF : Fixed D) {j : ℕ} (hj : j < 27) (hj9 : j % 9 ≠ 0) :
    cellCount D (qOf j) = 3 * ((decide (bL j 0 ∈ D)).toNat + (decide (bL j 1 ∈ D)).toNat +
      (decide (bL j 2 ∈ D)).toNat) := by
  rw [← card_fact j hj hj9]
  unfold cellCount
  congr 1
  ext x
  simp only [mem_filter, mem_union, decide_eq_true_eq, mem_ite_empty, mem_orbF, cell_iff hj hj9]
  constructor
  · rintro ⟨hx, h | h | h⟩
    · exact Or.inl (Or.inl ⟨(mem_iff_of_inOrb hF h).1 hx, h⟩)
    · exact Or.inl (Or.inr ⟨(mem_iff_of_inOrb hF h).1 hx, h⟩)
    · exact Or.inr ⟨(mem_iff_of_inOrb hF h).1 hx, h⟩
  · rintro ((⟨hy, h⟩ | ⟨hy, h⟩) | ⟨hy, h⟩)
    · exact ⟨(mem_iff_of_inOrb hF h).2 hy, Or.inl h⟩
    · exact ⟨(mem_iff_of_inOrb hF h).2 hy, Or.inr (Or.inl h)⟩
    · exact ⟨(mem_iff_of_inOrb hF h).2 hy, Or.inr (Or.inr h)⟩

/-- Selection rule of `optionLeaders`: digit `a` takes orbit `i` (coefficient 3) or omits it. -/
def sel (c p : ℕ) (a i : Fin 3) : Prop :=
  if caseCoef c ((positions c).getD p 0) = 3 then i = a else i ≠ a

lemma pick (P : Fin 3 → Prop) [DecidablePred P] (k : ℕ) (hk : k = 3 ∨ k = 6)
    (h : 3 * ((decide (P 0)).toNat + (decide (P 1)).toNat + (decide (P 2)).toNat) = k) :
    ∃ a : Fin 3, ∀ i, P i ↔ (if k = 3 then i = a else i ≠ a) := by
  have hall : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hk with rfl | rfl <;> by_cases h0 : P 0 <;> by_cases h1 : P 1 <;> by_cases h2 : P 2 <;>
    simp [h0, h1, h2] at h ⊢ <;>
    first
    | (refine ⟨0, fun i => ?_⟩; rcases hall i with rfl | rfl | rfl <;> simp [h0, h1, h2]; done)
    | (refine ⟨1, fun i => ?_⟩; rcases hall i with rfl | rfl | rfl <;> simp [h0, h1, h2]; done)
    | (refine ⟨2, fun i => ?_⟩; rcases hall i with rfl | rfl | rfl <;> simp [h0, h1, h2]; done)

lemma mem_optionLeaders (c p : ℕ) (a : Fin 3) (l : ℕ) :
    l ∈ optionLeaders c p a ↔
      ∃ i : Fin 3, sel c p a i ∧ l = (bucket ((positions c).getD p 0)).getD i 0 := by
  unfold optionLeaders sel
  by_cases h : caseCoef c ((positions c).getD p 0) = 3
  · simp only [h, beq_self_eq_true, if_true, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨a, rfl, rfl⟩
    · rintro ⟨i, rfl, rfl⟩; rfl
  · simp only [h, beq_iff_eq, if_false, List.mem_map, List.mem_filter, List.mem_range,
      bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨n, ⟨hn, hna⟩, rfl⟩
      exact ⟨⟨n, hn⟩, fun e => hna (by rw [← e]), rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, ⟨i.2, fun e => hi (Fin.ext e)⟩, rfl⟩

lemma mem_orbitE {l : ℕ} {x : G} : (∃ e ∈ orbitE l, decG e = x) ↔ inOrb x (decG l) := by
  rw [orbitE_eq]
  constructor
  · rintro ⟨e, he, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp [inOrb, decG_encG]
  · rintro (rfl | rfl | rfl)
    · exact ⟨l, by simp, rfl⟩
    · exact ⟨_, by simp, decG_encG _⟩
    · exact ⟨_, by simp, decG_encG _⟩

lemma mem_leaf (c : ℕ) (w : Fin 24 → Fin 3) (x : G) :
    x ∈ leaf c w ↔ x ∈ MaskSet ∨ ∃ p : Fin 24, ∃ i : Fin 3,
      sel c p (w p) i ∧ inOrb x (decG ((bucket ((positions c).getD p 0)).getD i 0)) := by
  unfold leaf
  rw [Finset.mem_union, List.mem_toFinset, List.mem_map]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨p, -, he⟩ := List.mem_flatMap.1 he
    obtain ⟨l, hl, he⟩ := List.mem_flatMap.1 he
    obtain ⟨i, hsel, rfl⟩ := (mem_optionLeaders _ _ _ _).1 hl
    exact ⟨p, i, hsel, mem_orbitE.1 ⟨e, he, rfl⟩⟩
  · rintro ⟨p, i, hsel, ho⟩
    obtain ⟨e, he, rfl⟩ := mem_orbitE.2 ho
    exact ⟨e, List.mem_flatMap.2 ⟨p, List.mem_finRange p, List.mem_flatMap.2
      ⟨_, (mem_optionLeaders _ _ _ _).2 ⟨i, hsel, rfl⟩, he⟩⟩, rfl⟩

lemma bucket_bL {j : ℕ} (hj : j < 27) (i : ℕ) : decG ((bucket j).getD i 0) = bL j i := by
  rw [bucket_eq j hj, bL]

lemma not_mem_H_iff {x : G} : x ∉ H ↔ cellIdx (encG x) % 9 ≠ 0 := by
  rw [mem_H, H_fact]

/-- A fixed set meeting `H` in `MaskSet` with the cell counts of case `c` is a leaf of case `c`. -/
theorem exists_leaf {D : Finset G} (hF : Fixed D) (hS : D.filter (· ∈ H) = MaskSet)
    {c : ℕ} (hc : c < 8) (hcells : ∀ q, cellCount D q = caseCount c q) :
    ∃ w : Fin 24 → Fin 3, D = leaf c w := by
  obtain ⟨hnd, hlen, hmem, hpos⟩ := pos_fact c hc
  have key : ∀ p : Fin 24, ∃ a : Fin 3, ∀ i : Fin 3,
      (bL ((positions c).getD p 0) i ∈ D ↔ sel c p a i) := by
    intro p
    obtain ⟨h27, h9, hco⟩ := hpos p
    have hcnt := cellCount_eq hF h27 h9
    rw [hcells, caseCount, qOf_idx _ h27] at hcnt
    exact pick (fun i => bL ((positions c).getD p 0) i ∈ D) _ hco hcnt.symm
  choose w hw using key
  refine ⟨w, ?_⟩
  ext x
  rw [mem_leaf]
  by_cases hx : x ∈ H
  · have hxD : x ∈ D ↔ x ∈ MaskSet := by rw [← hS, mem_filter]; tauto
    rw [hxD]
    constructor
    · exact Or.inl
    · rintro (h | ⟨p, i, -, ho⟩)
      · exact h
      · exfalso
        rw [bucket_bL (hpos p).1] at ho
        have e := cellIdx_inOrb ho
        rw [leader_fact _ (hpos p).1 (hpos p).2.1 i] at e
        exact not_mem_H_iff.2 (by rw [e]; exact (hpos p).2.1) hx
  · have hxM : x ∉ MaskSet := fun h => hx (MaskSet_sub_H h)
    have h9 := not_mem_H_iff.1 hx
    obtain ⟨hlt, -⟩ := cell_fact x
    obtain ⟨n, hn, hget⟩ := List.getElem_of_mem (hmem _ hlt h9)
    set p : Fin 24 := ⟨n, hlen ▸ hn⟩ with hp
    have hpj : (positions c).getD p 0 = cellIdx (encG x) := by
      rw [hp, List.getD_eq_getElem _ _ hn, hget]
    -- the orbit of `x` among the three of its cell
    have hcov : ∃ i : Fin 3, inOrb x (bL ((positions c).getD p 0) i) := by
      rw [hpj]
      rcases cover_fact x h9 with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    obtain ⟨i, ho⟩ := hcov
    rw [mem_iff_of_inOrb hF ho, hw p i]
    constructor
    · intro hs
      exact Or.inr ⟨p, i, hs, by rw [bucket_bL (hpos p).1]; exact ho⟩
    · rintro (h | ⟨p', i', hs, ho'⟩)
      · exact absurd h hxM
      · rw [bucket_bL (hpos p').1] at ho'
        have e1 := cellIdx_inOrb ho
        have e2 := cellIdx_inOrb ho'
        rw [leader_fact _ (hpos p).1 (hpos p).2.1 i] at e1
        rw [leader_fact _ (hpos p').1 (hpos p').2.1 i'] at e2
        have hpp : p' = p := by
          have h' : (positions c).getD p' 0 = (positions c).getD p 0 := e2.symm.trans e1
          rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact p'.2),
            List.getD_eq_getElem _ _ (by rw [hlen]; exact p.2)] at h'
          exact Fin.ext ((hnd.getElem_inj_iff).1 h')
        subst hpp
        have hii : i' = i := leader_disj _ (hpos p).1 (hpos p).2.1 i' i
          (inOrb_trans (inOrb_symm ho') ho)
        subst hii
        exact hs

end DS243
