import DS243.Multiplier
import DS243.SingletonClass
import DS243.Quotient
import DS243.Pruning
import DS243.ReceiptData

/-!
# No (243,121,60) difference set in C3 × C9 × C9, assuming the search receipts

`reduction`: every (243,121,60) difference set in `G` yields one in the frozen search tree,
namely `leaf c w` for a case `c < 8` and digits `w`. The steps are the multiplier theorem and fixed
translate, the singleton classification, the quotient-image normalization and the lifting.

The search covers the IDs `case * 3^12 + p` for big-endian twelve-digit ternary prefixes `p`,
split into 1038 ranges `[4096 r, min (4096 (r + 1)) 4251528)`. `RangeClear r` is what the
receipt of range `r` asserts: no leaf below any ID of the range is a difference set.
`no_difference_set` derives the claim from the 1038 receipts, each named by the SHA-256 of its
canonical final rows in the frozen `data/ranges.json`.
-/

namespace DS243

open Finset

/-- Big-endian digit `pos < 12` of the depth-12 prefix of a search ID. -/
def prefixDigit (id pos : ℕ) : ℕ := id % 531441 / 3 ^ (11 - pos) % 3

/-- The 24 digits of the leaf below search ID `id` with tail digits `tail`. -/
def idDigits (id : ℕ) (tail : Fin 12 → Fin 3) : Fin 24 → Fin 3 := fun pos =>
  if h : pos.val < 12 then ⟨prefixDigit id pos.val, Nat.mod_lt _ (by norm_num)⟩
  else tail ⟨pos.val - 12, by omega⟩

/-- The assertion of the receipt of range `r`: no leaf below any of its IDs is a difference set. -/
def RangeClear (r : ℕ) : Prop :=
  ∀ id, 4096 * r ≤ id → id < min (4096 * (r + 1)) 4251528 →
    ∀ tail : Fin 12 → Fin 3, ¬ IsDiffSet (leaf (id / 531441) (idDigits id tail))

/-- The receipt of range `r`, whose canonical final rows have SHA-256 `sha256`. -/
structure Receipt (r : ℕ) (sha256 : String) : Prop where
  clear : RangeClear r

/-- Little-endian base-3 value of a digit list. -/
def val3 : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 3 * val3 ds

lemma val3_lt : ∀ ds : List ℕ, (∀ d ∈ ds, d < 3) → val3 ds < 3 ^ ds.length
  | [], _ => by simp [val3]
  | d :: ds, h => by
    have hd := h d (by simp)
    have := val3_lt ds (fun x hx => h x (by simp [hx]))
    simp only [val3, List.length_cons, pow_succ]
    omega

lemma val3_digit : ∀ (ds : List ℕ), (∀ d ∈ ds, d < 3) → ∀ i, val3 ds / 3 ^ i % 3 = ds.getD i 0
  | [], _, i => by simp [val3]
  | d :: ds, h, 0 => by
    have hd := h d (by simp)
    simp [val3]; omega
  | d :: ds, h, i + 1 => by
    have hd := h d (by simp)
    have ih := val3_digit ds (fun x hx => h x (by simp [hx])) i
    have e : val3 (d :: ds) / 3 = val3 ds := by simp only [val3]; omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, e]
    simpa using ih

lemma image_word_append (w v : Word) (X : Finset G) :
    (X.image v.legal.toFun).image w.legal.toFun = X.image (w ++ v).legal.toFun := by
  rw [image_image]; congr 1; funext x; simp [Word.legal_toFun, Word.eval_append]

/-- **Normal form.** Every difference set is, after a translation and a legal map (an additive
automorphism followed by a translation in `H`, given as a word), exactly a leaf of the frozen tree:
the frozen singleton set plus 24 orbit choices of one of the 8 frozen cases. -/
theorem normal_form {D : Finset G} (hD : IsDiffSet D) :
    ∃ u : G, ∃ w : Word, ∃ c, c < 8 ∧ ∃ digits : Fin 24 → Fin 3,
      (D.image (· - u)).image w.legal.toFun = leaf c digits := by
  obtain ⟨u, hfix⟩ := exists_fixed_translate hD
  have hD0 := isDiffSet_translate hD u
  obtain ⟨w1, hS1⟩ := exists_word_mask (card_S hD0 hfix) (cond_S hD0 hfix)
  have hD1 := w1.legal.isDiffSet_image hD0
  have hF1 := w1.legal.fixed_image hfix
  obtain ⟨w2, c, hc, hS2, hcells⟩ := quotient_normal hD1 hF1 hS1
  have hF2 := w2.legal.fixed_image hF1
  obtain ⟨digits, hdig⟩ := exists_leaf hF2 hS2 hc hcells
  refine ⟨u, w2 ++ w1, c, hc, digits, ?_⟩
  rw [← hdig, image_word_append]

/-- The 1038 ranges partition the search IDs `[0, 4251528)`. -/
theorem ranges_partition (id : ℕ) (hid : id < 4251528) :
    ∃! r, r < 1038 ∧ 4096 * r ≤ id ∧ id < min (4096 * (r + 1)) 4251528 := by
  refine ⟨id / 4096, ⟨by omega, by omega, by rw [lt_min_iff]; omega⟩, ?_⟩
  rintro r ⟨-, h1, h2⟩
  rw [lt_min_iff] at h2
  omega

/-- Every leaf lies below a search ID of some range: case `c` and the first twelve digits give the
ID `c · 3^12 + (big-endian prefix)`, and the last twelve digits are the tail. -/
theorem leaf_has_id {c : ℕ} (hc : c < 8) (digits : Fin 24 → Fin 3) :
    ∃ r, r < 1038 ∧ ∃ id, 4096 * r ≤ id ∧ id < min (4096 * (r + 1)) 4251528 ∧
      ∃ tail : Fin 12 → Fin 3, id / 531441 = c ∧ idDigits id tail = digits := by
  obtain ⟨L, hL⟩ : ∃ L : List ℕ,
      L = (List.range 12).map fun i => (digits ⟨11 - i, by omega⟩).val := ⟨_, rfl⟩
  have hL3 : ∀ d ∈ L, d < 3 := by
    intro d hd
    rw [hL, List.mem_map] at hd
    obtain ⟨i, -, rfl⟩ := hd
    exact (digits _).isLt
  have hlen : L.length = 12 := by rw [hL]; simp
  have hlt : val3 L < 531441 := by
    have := val3_lt L hL3; rw [hlen] at this; simpa using this
  obtain ⟨v, hv⟩ : ∃ v, v = val3 L := ⟨_, rfl⟩
  rw [← hv] at hlt
  obtain ⟨id, hid⟩ : ∃ id, id = c * 531441 + v := ⟨_, rfl⟩
  have hmod : id % 531441 = v := by omega
  have key : ∀ k (hk : k < 12), v / 3 ^ (11 - k) % 3 = (digits ⟨k, by omega⟩).val := by
    intro k hk
    rw [hv, val3_digit L hL3, hL, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    exact congrArg (fun j => (digits j).val) (Fin.ext (by simp only; omega))
  refine ⟨id / 4096, by omega, id, by omega, by rw [lt_min_iff]; constructor <;> omega,
    fun t => digits ⟨t.val + 12, by omega⟩, by omega, ?_⟩
  funext pos
  by_cases hp : pos.val < 12
  · apply Fin.ext
    simp only [idDigits, hp, dite_true, prefixDigit, hmod]
    rw [key pos.val hp]
  · simp only [idDigits, hp, dite_false]
    exact congrArg digits (Fin.ext (by simp only; omega))

/-- **Coverage.** Every (243,121,60) difference set in `G` is, up to a translation and a legal
map, exactly the leaf below some search ID of one of the 1038 ranges. This is the decomposition
both lifting kernels share; it is proved here with no hypothesis about the search. -/
theorem coverage {D : Finset G} (hD : IsDiffSet D) :
    ∃ u : G, ∃ w : Word, ∃ r, r < 1038 ∧ ∃ id, 4096 * r ≤ id ∧
      id < min (4096 * (r + 1)) 4251528 ∧ ∃ tail : Fin 12 → Fin 3,
        (D.image (· - u)).image w.legal.toFun = leaf (id / 531441) (idDigits id tail) := by
  obtain ⟨u, w, c, hc, digits, hleaf⟩ := normal_form hD
  obtain ⟨r, hr, id, h1, h2, tail, hcase, hdig⟩ := leaf_has_id hc digits
  exact ⟨u, w, r, hr, id, h1, h2, tail, by rw [hcase, hdig, hleaf]⟩

/-- The covering leaf is itself a difference set. -/
theorem reduction {D : Finset G} (hD : IsDiffSet D) :
    ∃ c, c < 8 ∧ ∃ w : Fin 24 → Fin 3, IsDiffSet (leaf c w) := by
  obtain ⟨u, w, c, hc, digits, hleaf⟩ := normal_form hD
  exact ⟨c, hc, digits, hleaf ▸ w.legal.isDiffSet_image (isDiffSet_translate hD u)⟩

/-- **Main theorem.** Given the 1038 range receipts, each named by the SHA-256 of its canonical
final rows, there is no (243,121,60) difference set in `C3 × C9 × C9`. -/
theorem no_difference_set
    (receipts : ∀ r, r < 1038 → Receipt r (receiptDigest.getD r "")) :
    ¬ ∃ D : Finset G, IsDiffSet D := by
  rintro ⟨D, hD⟩
  obtain ⟨u, w, r, hr, id, h1, h2, tail, hleaf⟩ := coverage hD
  exact (receipts r hr).clear id h1 h2 tail
    (hleaf ▸ w.legal.isDiffSet_image (isDiffSet_translate hD u))

end DS243
