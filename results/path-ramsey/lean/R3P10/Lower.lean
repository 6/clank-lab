import R3P10.Defs

/-! # A 3-colouring of the edges of K_17 with no monochromatic P_10

The witness is the classical colouring `checks/lower_bound.py` writes (and
`data/k17-coloring.txt` holds): a blow-up of `K_4` with parts A = {0..4},
B = {5..8}, C = {9..12}, D = {13..16}. Colour 0 is used inside A ∪ B and inside
C ∪ D, colour 1 between A and C and between B and D, and colour 2 between A
and D and between B and C. The colouring is written out below edge by edge;
`Checks.lean` compares it with `data/k17-coloring.txt`.

The proof is by a certificate that the kernel checks with `decide +kernel`
(kernel reduction; no native evaluation, so no `Lean.ofReduceBool` axiom):
for each colour, a labelling of the vertices that is constant across every
edge of that colour and whose classes have at most 9 vertices. A path in one
colour stays inside one class, so it has at most 9 vertices
(`noMono_of_labels`, proved for every `n` and `m`).
-/

namespace R3P10

/-! ## A sufficient certificate for "no monochromatic `P_m`" -/

/-- If, for each colour `c`, the labelling `lab c` is constant across every
`c`-coloured edge and each of its classes has fewer than `m` vertices, then
`X` has no monochromatic path on `m` vertices. -/
theorem noMono_of_labels {n m : ℕ} (hm : 0 < m) (X : Col n) (lab : Fin 3 → Fin n → ℕ)
    (hclosed : ∀ (c : Fin 3) (u v : Fin n), X s(u, v) = c → lab c u = lab c v)
    (hsmall : ∀ (c : Fin 3) (v : Fin n),
      (Finset.univ.filter fun w => lab c w = lab c v).card < m) :
    ¬ HasMonoPath n m X := by
  rintro ⟨c, p, hinj, hp⟩
  have key : ∀ (i : ℕ) (h : i < m), lab c (p ⟨i, h⟩) = lab c (p ⟨0, hm⟩) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih => intro h; rw [← ih (by omega)]; exact (hclosed c _ _ (hp i h)).symm
  have hle : (Finset.univ : Finset (Fin m)).card ≤
      (Finset.univ.filter fun w => lab c w = lab c (p ⟨0, hm⟩)).card :=
    Finset.card_le_card_of_injOn p
      (fun i _ => by simpa using key i.val i.isLt) (fun i _ j _ hij => hinj hij)
  have := hsmall c (p ⟨0, hm⟩)
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-! ## The witness -/

/-- The colours of the edges `(i, j)`, `i < j < 17`: row `i` lists `j = i+1, ..., 16`
(the order and values of `data/k17-coloring.txt`). -/
def k17Rows : List (List (Fin 3)) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 0
   [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 1
   [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 2
   [0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 3
   [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2],  -- row 4
   [0, 0, 0, 2, 2, 2, 2, 1, 1, 1, 1],  -- row 5
   [0, 0, 2, 2, 2, 2, 1, 1, 1, 1],  -- row 6
   [0, 2, 2, 2, 2, 1, 1, 1, 1],  -- row 7
   [2, 2, 2, 2, 1, 1, 1, 1],  -- row 8
   [0, 0, 0, 0, 0, 0, 0],  -- row 9
   [0, 0, 0, 0, 0, 0],  -- row 10
   [0, 0, 0, 0, 0],  -- row 11
   [0, 0, 0, 0],  -- row 12
   [0, 0, 0],  -- row 13
   [0, 0],  -- row 14
   [0]]  -- row 15

/-- The colour of the pair `{a, b}` read from `k17Rows` (0 on the diagonal, which
no path uses). -/
def k17Fn (a b : Fin 17) : Fin 3 :=
  if a.val < b.val then (k17Rows.getD a.val []).getD (b.val - a.val - 1) 0
  else if b.val < a.val then (k17Rows.getD b.val []).getD (a.val - b.val - 1) 0
  else 0

theorem k17Fn_symm (a b : Fin 17) : k17Fn a b = k17Fn b a := by
  unfold k17Fn
  by_cases h1 : a.val < b.val
  · rw [if_pos h1, if_neg (by omega), if_pos h1]
  · by_cases h2 : b.val < a.val
    · rw [if_neg h1, if_pos h2, if_pos h2]
    · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]

/-- The colouring of `K_17`. -/
def k17Col : Col 17 := Sym2.lift ⟨k17Fn, k17Fn_symm⟩

/-- The certificate: for colour `c`, vertex `v` gets label `(k17Labels.getD c []).getD v 0`.
Colour 0: A ∪ B / C ∪ D; colour 1: A ∪ C / B ∪ D; colour 2: A ∪ D / B ∪ C. -/
def k17Labels : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0]]

def k17Lab (c : Fin 3) (v : Fin 17) : ℕ := (k17Labels.getD c.val []).getD v.val 0

/-- Every edge of colour `c` joins two vertices with the same `c`-label (kernel-checked). -/
theorem k17_closed : ∀ (c : Fin 3) (u v : Fin 17), k17Fn u v = c → k17Lab c u = k17Lab c v := by
  decide +kernel

/-- Every label class has at most 9 vertices (kernel-checked). -/
theorem k17_small : ∀ (c : Fin 3) (v : Fin 17),
    (Finset.univ.filter fun w => k17Lab c w = k17Lab c v).card < 10 := by
  decide +kernel

/-- **Lower bound.** The colouring `k17Col` of the edges of `K_17` has no
monochromatic path on 10 vertices, so `R(P_10, P_10, P_10) > 17`. The finite
checks (`k17_closed`, `k17_small`) are decided by `decide +kernel`, i.e. by
the Lean kernel's own reduction; no native evaluation is used. -/
theorem K17_no_mono_P10 : ¬ HasMonoPath 17 10 k17Col :=
  noMono_of_labels (by norm_num) k17Col k17Lab (fun c u v h => k17_closed c u v h) k17_small

/-- The lower bound in the form of the main theorem's statement. -/
theorem K17_exists_no_mono_P10 :
    ∃ X : Sym2 (Fin 17) → Fin 3, ¬ ∃ (c : Fin 3) (p : Fin 10 → Fin 17), Function.Injective p ∧
      ∀ (i : ℕ) (h : i + 1 < 10), X s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c :=
  ⟨k17Col, K17_no_mono_P10⟩

end R3P10
