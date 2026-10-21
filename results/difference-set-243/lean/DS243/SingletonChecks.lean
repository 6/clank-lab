import DS243.Singleton

/-! Kernel checks of the singleton classification, with finite witnesses checked here.
Each check is split into small declarations (the kernel's caches are per declaration). -/

namespace DS243

/-- Property checked by K1 for a layer-0 mask `m`. -/
def K1prop (m : ℕ) : Prop := img9 (T0 m) 0 m ∈ reps ∧ ∀ j, j < 9 → pullIdx (T0 m) j < 9

instance (m : ℕ) : Decidable (K1prop m) := by unfold K1prop; infer_instance

/-- Property checked by K2 for a layer-1 mask `c`. -/
def K2prop (c : ℕ) : Prop := img9 (T1 c) 9 c ∈ canon ∧
    ∀ j, j < 9 → pullIdx (T1 c) j = j ∧ 9 ≤ pullIdx (T1 c) (9 + j) ∧ pullIdx (T1 c) (9 + j) < 18

instance (c : ℕ) : Decidable (K2prop c) := by unfold K2prop; infer_instance

/-- Number of set bits among the first nine. -/
def popc9 (n : ℕ) : ℕ := ((List.range 9).filter fun i => n.testBit i).length

/-- The 9-bit masks with `k` set bits. -/
def byPop (k : ℕ) : List ℕ := (List.range 512).filter fun n => popc9 n == k

/-- Property checked by K3 for a layer-0 representative `r` and a layer-1 representative `c`:
every completion by a layer-2 mask to 13 points that satisfies the mod-3 condition is a survivor. -/
def K3rc (r c : ℕ) : Prop := popc9 r + popc9 c ≤ 13 → ∀ n ∈ byPop (13 - popc9 r - popc9 c),
    condMask (r + 512 * c + 262144 * n) = true → r + 512 * c + 262144 * n ∈ survivors.map Prod.fst

instance (r c : ℕ) : Decidable (K3rc r c) := by unfold K3rc; infer_instance

/-- Cover of `[0, 512)` by eight chunks of 64. -/
lemma chunk_cover (P : ℕ → Prop) (h : ∀ k, k < 8 → ∀ i, i < 64 → P (64 * k + i)) :
    ∀ m, m < 512 → P m := by
  intro m hm
  have := h (m / 64) (by omega) (m % 64) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

set_option maxRecDepth 100000

theorem K1_0 : ∀ i, i < 64 → K1prop (0 + i) := by decide +kernel

theorem K1_1 : ∀ i, i < 64 → K1prop (64 + i) := by decide +kernel

theorem K1_2 : ∀ i, i < 64 → K1prop (128 + i) := by decide +kernel

theorem K1_3 : ∀ i, i < 64 → K1prop (192 + i) := by decide +kernel

theorem K1_4 : ∀ i, i < 64 → K1prop (256 + i) := by decide +kernel

theorem K1_5 : ∀ i, i < 64 → K1prop (320 + i) := by decide +kernel

theorem K1_6 : ∀ i, i < 64 → K1prop (384 + i) := by decide +kernel

theorem K1_7 : ∀ i, i < 64 → K1prop (448 + i) := by decide +kernel

theorem K1 : ∀ m, m < 512 → K1prop m := by
  apply chunk_cover
  intro k hk
  interval_cases k
  · simpa using K1_0
  · simpa using K1_1
  · simpa using K1_2
  · simpa using K1_3
  · simpa using K1_4
  · simpa using K1_5
  · simpa using K1_6
  · simpa using K1_7

theorem K2_0 : ∀ i, i < 64 → K2prop (0 + i) := by decide +kernel

theorem K2_1 : ∀ i, i < 64 → K2prop (64 + i) := by decide +kernel

theorem K2_2 : ∀ i, i < 64 → K2prop (128 + i) := by decide +kernel

theorem K2_3 : ∀ i, i < 64 → K2prop (192 + i) := by decide +kernel

theorem K2_4 : ∀ i, i < 64 → K2prop (256 + i) := by decide +kernel

theorem K2_5 : ∀ i, i < 64 → K2prop (320 + i) := by decide +kernel

theorem K2_6 : ∀ i, i < 64 → K2prop (384 + i) := by decide +kernel

theorem K2_7 : ∀ i, i < 64 → K2prop (448 + i) := by decide +kernel

theorem K2 : ∀ m, m < 512 → K2prop m := by
  apply chunk_cover
  intro k hk
  interval_cases k
  · simpa using K2_0
  · simpa using K2_1
  · simpa using K2_2
  · simpa using K2_3
  · simpa using K2_4
  · simpa using K2_5
  · simpa using K2_6
  · simpa using K2_7

/-- Layer-1 representatives, chunk 0. -/
def canonC0 : List ℕ := [0, 1, 3, 7, 9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 28, 29]

/-- Layer-1 representatives, chunk 1. -/
def canonC1 : List ℕ := [30, 31, 57, 59, 63, 73, 74, 75, 76, 77, 78, 79, 83, 84, 85, 86]

/-- Layer-1 representatives, chunk 2. -/
def canonC2 : List ℕ := [87, 90, 91, 93, 94, 95, 98, 99, 102, 103, 107, 109, 110, 111, 115, 117]

/-- Layer-1 representatives, chunk 3. -/
def canonC3 : List ℕ := [118, 119, 123, 125, 126, 127, 219, 221, 222, 223, 238, 239, 245, 247, 255, 511]

lemma canon_eq : canon = canonC0 ++ (canonC1 ++ (canonC2 ++ (canonC3))) := rfl

theorem K3_0_0 : ∀ c ∈ canonC0, K3rc 0 c := by decide +kernel

theorem K3_0_1 : ∀ c ∈ canonC1, K3rc 0 c := by decide +kernel

theorem K3_0_2 : ∀ c ∈ canonC2, K3rc 0 c := by decide +kernel

theorem K3_0_3 : ∀ c ∈ canonC3, K3rc 0 c := by decide +kernel

theorem K3r_0 : ∀ c ∈ canon, K3rc 0 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_0_0 c h
  · exact K3_0_1 c h
  · exact K3_0_2 c h
  · exact K3_0_3 c h

theorem K3_1_0 : ∀ c ∈ canonC0, K3rc 1 c := by decide +kernel

theorem K3_1_1 : ∀ c ∈ canonC1, K3rc 1 c := by decide +kernel

theorem K3_1_2 : ∀ c ∈ canonC2, K3rc 1 c := by decide +kernel

theorem K3_1_3 : ∀ c ∈ canonC3, K3rc 1 c := by decide +kernel

theorem K3r_1 : ∀ c ∈ canon, K3rc 1 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_1_0 c h
  · exact K3_1_1 c h
  · exact K3_1_2 c h
  · exact K3_1_3 c h

theorem K3_3_0 : ∀ c ∈ canonC0, K3rc 3 c := by decide +kernel

theorem K3_3_1 : ∀ c ∈ canonC1, K3rc 3 c := by decide +kernel

theorem K3_3_2 : ∀ c ∈ canonC2, K3rc 3 c := by decide +kernel

theorem K3_3_3 : ∀ c ∈ canonC3, K3rc 3 c := by decide +kernel

theorem K3r_3 : ∀ c ∈ canon, K3rc 3 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_3_0 c h
  · exact K3_3_1 c h
  · exact K3_3_2 c h
  · exact K3_3_3 c h

theorem K3_7_0 : ∀ c ∈ canonC0, K3rc 7 c := by decide +kernel

theorem K3_7_1 : ∀ c ∈ canonC1, K3rc 7 c := by decide +kernel

theorem K3_7_2 : ∀ c ∈ canonC2, K3rc 7 c := by decide +kernel

theorem K3_7_3 : ∀ c ∈ canonC3, K3rc 7 c := by decide +kernel

theorem K3r_7 : ∀ c ∈ canon, K3rc 7 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_7_0 c h
  · exact K3_7_1 c h
  · exact K3_7_2 c h
  · exact K3_7_3 c h

theorem K3_11_0 : ∀ c ∈ canonC0, K3rc 11 c := by decide +kernel

theorem K3_11_1 : ∀ c ∈ canonC1, K3rc 11 c := by decide +kernel

theorem K3_11_2 : ∀ c ∈ canonC2, K3rc 11 c := by decide +kernel

theorem K3_11_3 : ∀ c ∈ canonC3, K3rc 11 c := by decide +kernel

theorem K3r_11 : ∀ c ∈ canon, K3rc 11 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_11_0 c h
  · exact K3_11_1 c h
  · exact K3_11_2 c h
  · exact K3_11_3 c h

theorem K3_15_0 : ∀ c ∈ canonC0, K3rc 15 c := by decide +kernel

theorem K3_15_1 : ∀ c ∈ canonC1, K3rc 15 c := by decide +kernel

theorem K3_15_2 : ∀ c ∈ canonC2, K3rc 15 c := by decide +kernel

theorem K3_15_3 : ∀ c ∈ canonC3, K3rc 15 c := by decide +kernel

theorem K3r_15 : ∀ c ∈ canon, K3rc 15 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_15_0 c h
  · exact K3_15_1 c h
  · exact K3_15_2 c h
  · exact K3_15_3 c h

theorem K3_27_0 : ∀ c ∈ canonC0, K3rc 27 c := by decide +kernel

theorem K3_27_1 : ∀ c ∈ canonC1, K3rc 27 c := by decide +kernel

theorem K3_27_2 : ∀ c ∈ canonC2, K3rc 27 c := by decide +kernel

theorem K3_27_3 : ∀ c ∈ canonC3, K3rc 27 c := by decide +kernel

theorem K3r_27 : ∀ c ∈ canon, K3rc 27 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_27_0 c h
  · exact K3_27_1 c h
  · exact K3_27_2 c h
  · exact K3_27_3 c h

theorem K3_31_0 : ∀ c ∈ canonC0, K3rc 31 c := by decide +kernel

theorem K3_31_1 : ∀ c ∈ canonC1, K3rc 31 c := by decide +kernel

theorem K3_31_2 : ∀ c ∈ canonC2, K3rc 31 c := by decide +kernel

theorem K3_31_3 : ∀ c ∈ canonC3, K3rc 31 c := by decide +kernel

theorem K3r_31 : ∀ c ∈ canon, K3rc 31 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_31_0 c h
  · exact K3_31_1 c h
  · exact K3_31_2 c h
  · exact K3_31_3 c h

theorem K3_63_0 : ∀ c ∈ canonC0, K3rc 63 c := by decide +kernel

theorem K3_63_1 : ∀ c ∈ canonC1, K3rc 63 c := by decide +kernel

theorem K3_63_2 : ∀ c ∈ canonC2, K3rc 63 c := by decide +kernel

theorem K3_63_3 : ∀ c ∈ canonC3, K3rc 63 c := by decide +kernel

theorem K3r_63 : ∀ c ∈ canon, K3rc 63 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_63_0 c h
  · exact K3_63_1 c h
  · exact K3_63_2 c h
  · exact K3_63_3 c h

theorem K3_79_0 : ∀ c ∈ canonC0, K3rc 79 c := by decide +kernel

theorem K3_79_1 : ∀ c ∈ canonC1, K3rc 79 c := by decide +kernel

theorem K3_79_2 : ∀ c ∈ canonC2, K3rc 79 c := by decide +kernel

theorem K3_79_3 : ∀ c ∈ canonC3, K3rc 79 c := by decide +kernel

theorem K3r_79 : ∀ c ∈ canon, K3rc 79 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_79_0 c h
  · exact K3_79_1 c h
  · exact K3_79_2 c h
  · exact K3_79_3 c h

theorem K3_95_0 : ∀ c ∈ canonC0, K3rc 95 c := by decide +kernel

theorem K3_95_1 : ∀ c ∈ canonC1, K3rc 95 c := by decide +kernel

theorem K3_95_2 : ∀ c ∈ canonC2, K3rc 95 c := by decide +kernel

theorem K3_95_3 : ∀ c ∈ canonC3, K3rc 95 c := by decide +kernel

theorem K3r_95 : ∀ c ∈ canon, K3rc 95 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_95_0 c h
  · exact K3_95_1 c h
  · exact K3_95_2 c h
  · exact K3_95_3 c h

theorem K3_127_0 : ∀ c ∈ canonC0, K3rc 127 c := by decide +kernel

theorem K3_127_1 : ∀ c ∈ canonC1, K3rc 127 c := by decide +kernel

theorem K3_127_2 : ∀ c ∈ canonC2, K3rc 127 c := by decide +kernel

theorem K3_127_3 : ∀ c ∈ canonC3, K3rc 127 c := by decide +kernel

theorem K3r_127 : ∀ c ∈ canon, K3rc 127 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_127_0 c h
  · exact K3_127_1 c h
  · exact K3_127_2 c h
  · exact K3_127_3 c h

theorem K3_255_0 : ∀ c ∈ canonC0, K3rc 255 c := by decide +kernel

theorem K3_255_1 : ∀ c ∈ canonC1, K3rc 255 c := by decide +kernel

theorem K3_255_2 : ∀ c ∈ canonC2, K3rc 255 c := by decide +kernel

theorem K3_255_3 : ∀ c ∈ canonC3, K3rc 255 c := by decide +kernel

theorem K3r_255 : ∀ c ∈ canon, K3rc 255 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_255_0 c h
  · exact K3_255_1 c h
  · exact K3_255_2 c h
  · exact K3_255_3 c h

theorem K3_511_0 : ∀ c ∈ canonC0, K3rc 511 c := by decide +kernel

theorem K3_511_1 : ∀ c ∈ canonC1, K3rc 511 c := by decide +kernel

theorem K3_511_2 : ∀ c ∈ canonC2, K3rc 511 c := by decide +kernel

theorem K3_511_3 : ∀ c ∈ canonC3, K3rc 511 c := by decide +kernel

theorem K3r_511 : ∀ c ∈ canon, K3rc 511 c := by
  intro c hc
  rw [canon_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with h|h|h|h
  · exact K3_511_0 c h
  · exact K3_511_1 c h
  · exact K3_511_2 c h
  · exact K3_511_3 c h

/-- K3: every admissible 13-element mask with representative layers 0 and 1 is a survivor. -/
theorem K3 : ∀ r ∈ reps, ∀ c ∈ canon, K3rc r c := by
  intro r hr
  simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact K3r_0
  · exact K3r_1
  · exact K3r_3
  · exact K3r_7
  · exact K3r_11
  · exact K3r_15
  · exact K3r_27
  · exact K3r_31
  · exact K3r_63
  · exact K3r_79
  · exact K3r_95
  · exact K3r_127
  · exact K3r_255
  · exact K3r_511

/-- K4: every survivor's word maps it to the frozen mask. -/
theorem K4 : ∀ p ∈ survivors, ∀ j, j < 27 → MASK.testBit j = p.1.testBit (pullIdx p.2 j) := by
  decide +kernel

end DS243
