import Endpoint

namespace NoncrossingSCD

universe u

/-- Covers in a product change exactly one factor by a cover. -/
def ProductCover {α β : Type u} (cα : α → α → Prop) (cβ : β → β → Prop)
    (x y : α × β) : Prop :=
  (cα x.1 y.1 ∧ x.2 = y.2) ∨ (x.1 = y.1 ∧ cβ x.2 y.2)

/-- The local grid chain containing (i,j) has index min(i,b-j). -/
def gridLabel (b i j : Nat) := min i (b-j)
def gridX (b k t : Nat) := k + (t-(b-k))
def gridY (b k t : Nat) := min t (b-k)

theorem grid_facts (a b k t : Nat) (ka : k ≤ a) (kb : k ≤ b)
    (ht : t ≤ a+b-2*k) :
    gridX b k t ≤ a ∧ gridY b k t ≤ b ∧
    gridLabel b (gridX b k t) (gridY b k t) = k ∧
    gridX b k t + gridY b k t = k+t := by
  unfold gridX gridY gridLabel
  omega

theorem grid_recover (a b i j : Nat) (hi : i ≤ a) (hj : j ≤ b) :
    let k := gridLabel b i j
    k ≤ a ∧ k ≤ b ∧ k ≤ i+j ∧ i+j-k ≤ a+b-2*k ∧
    gridX b k (i+j-k) = i ∧ gridY b k (i+j-k) = j := by
  unfold gridX gridY gridLabel
  omega

theorem grid_step (a b k t : Nat) (_ka : k ≤ a) (kb : k ≤ b)
    (_ht : t+1 ≤ a+b-2*k) :
    (gridX b k (t+1) = gridX b k t + 1 ∧ gridY b k (t+1) = gridY b k t) ∨
    (gridX b k (t+1) = gridX b k t ∧ gridY b k (t+1) = gridY b k t + 1) := by
  unfold gridX gridY
  omega

structure ProductLabel {α β : Type u} {cα cβ rα rβ n m}
    (P : SCD α cα rα n) (Q : SCD β cβ rβ m) where
  p : P.Label
  q : Q.Label
  k : Nat
  kp : k ≤ P.top p - P.bottom p
  kq : k ≤ Q.top q - Q.bottom q

section
variable {α β : Type u} {cα : α → α → Prop} {cβ : β → β → Prop}
  {rα : α → Nat} {rβ : β → Nat} {n m : Nat}
  (P : SCD α cα rα n) (Q : SCD β cβ rβ m)

def prodBottom (a : ProductLabel P Q) := P.bottom a.p + Q.bottom a.q + a.k
def prodTop (a : ProductLabel P Q) := P.top a.p + Q.top a.q - a.k

def prodLabel (x : α × β) : ProductLabel P Q :=
  let i := rα x.1 - P.bottom (P.label x.1)
  let j := rβ x.2 - Q.bottom (Q.label x.2)
  let b := Q.top (Q.label x.2) - Q.bottom (Q.label x.2)
  { p := P.label x.1, q := Q.label x.2, k := gridLabel b i j
    kp := by have := P.bounds x.1; unfold gridLabel; omega
    kq := by have := Q.bounds x.2; unfold gridLabel; omega }

def prodPoint (a : ProductLabel P Q) (r : Nat)
    (lo : prodBottom P Q a ≤ r) (hi : r ≤ prodTop P Q a) : α × β :=
  let t := r - prodBottom P Q a
  let b := Q.top a.q - Q.bottom a.q
  let i := gridX b a.k t
  let j := gridY b a.k t
  have facts := grid_facts (P.top a.p-P.bottom a.p) b a.k t a.kp a.kq (by
    have := P.nonempty a.p; have := Q.nonempty a.q
    have := a.kp; have := a.kq
    unfold t prodBottom prodTop at *; omega)
  (P.point a.p (P.bottom a.p+i) (by omega) (by have := P.nonempty a.p; omega),
   Q.point a.q (Q.bottom a.q+j) (by omega) (by have := Q.nonempty a.q; omega))

theorem prodPoint_rank (a : ProductLabel P Q) (r : Nat) (lo hi) :
    rα (prodPoint P Q a r lo hi).1 + rβ (prodPoint P Q a r lo hi).2 = r := by
  have hP := P.nonempty a.p; have hQ := Q.nonempty a.q
  have hkP := a.kp; have hkQ := a.kq
  have h := grid_facts (P.top a.p-P.bottom a.p) (Q.top a.q-Q.bottom a.q)
    a.k (r-prodBottom P Q a) hkP hkQ (by unfold prodBottom prodTop at *; omega)
  simp only [prodPoint, P.point_rank, Q.point_rank]
  unfold prodBottom at *; omega

theorem prodPoint_label (a : ProductLabel P Q) (r : Nat) (lo hi) :
    prodLabel P Q (prodPoint P Q a r lo hi) = a := by
  have hP := P.nonempty a.p; have hQ := Q.nonempty a.q
  have hkP := a.kp; have hkQ := a.kq
  have h := grid_facts (P.top a.p-P.bottom a.p) (Q.top a.q-Q.bottom a.q)
    a.k (r-prodBottom P Q a) hkP hkQ (by unfold prodBottom prodTop at *; omega)
  simp only [prodLabel, prodPoint, P.point_label, Q.point_label,
    P.point_rank, Q.point_rank, Nat.add_sub_cancel_left]
  cases a
  simp_all only []

theorem prodBounds (x : α × β) :
    prodBottom P Q (prodLabel P Q x) ≤ rα x.1+rβ x.2 ∧
    rα x.1+rβ x.2 ≤ prodTop P Q (prodLabel P Q x) := by
  have hp := P.bounds x.1; have hq := Q.bounds x.2
  unfold prodBottom prodTop prodLabel gridLabel
  dsimp
  omega

theorem prodRecover (x : α × β) :
    prodPoint P Q (prodLabel P Q x) (rα x.1+rβ x.2)
      (prodBounds P Q x).1 (prodBounds P Q x).2 = x := by
  have hp := P.bounds x.1; have hq := Q.bounds x.2
  have h := grid_recover (P.top (P.label x.1)-P.bottom (P.label x.1))
    (Q.top (Q.label x.2)-Q.bottom (Q.label x.2))
    (rα x.1-P.bottom (P.label x.1)) (rβ x.2-Q.bottom (Q.label x.2))
    (by omega) (by omega)
  dsimp only at h
  have ti : rα x.1+rβ x.2-prodBottom P Q (prodLabel P Q x) =
      (rα x.1-P.bottom (P.label x.1))+(rβ x.2-Q.bottom (Q.label x.2))-
      gridLabel (Q.top (Q.label x.2)-Q.bottom (Q.label x.2))
        (rα x.1-P.bottom (P.label x.1)) (rβ x.2-Q.bottom (Q.label x.2)) := by
    unfold prodBottom prodLabel; dsimp; omega
  apply Prod.ext
  · simp only [prodPoint, ti]
    simp only [prodLabel, h.2.2.2.2.1]
    have e : P.bottom (P.label x.1)+(rα x.1-P.bottom (P.label x.1)) = rα x.1 := by omega
    simpa only [e] using P.recover x.1
  · simp only [prodPoint, ti]
    simp only [prodLabel, h.2.2.2.2.2]
    have e : Q.bottom (Q.label x.2)+(rβ x.2-Q.bottom (Q.label x.2)) = rβ x.2 := by omega
    simpa only [e] using Q.recover x.2


theorem prodSaturated (a : ProductLabel P Q) (r : Nat)
    (lo : prodBottom P Q a ≤ r) (hi : r+1 ≤ prodTop P Q a) :
    ProductCover cα cβ
      (prodPoint P Q a r lo (by omega))
      (prodPoint P Q a (r+1) (by omega) hi) := by
  have hp := P.nonempty a.p; have hq := Q.nonempty a.q
  have kp := a.kp; have kq := a.kq
  have ht : r-prodBottom P Q a+1 ≤
      (P.top a.p-P.bottom a.p)+(Q.top a.q-Q.bottom a.q)-2*a.k := by
    unfold prodBottom prodTop at *; omega
  have tt : r+1-prodBottom P Q a = r-prodBottom P Q a+1 := by omega
  have hf := grid_facts (P.top a.p-P.bottom a.p) (Q.top a.q-Q.bottom a.q)
    a.k (r-prodBottom P Q a+1) kp kq ht
  have hs := grid_step (P.top a.p-P.bottom a.p) (Q.top a.q-Q.bottom a.q)
    a.k (r-prodBottom P Q a) kp kq ht
  rcases hs with hs | hs
  · left
    constructor
    · have pc := P.saturated a.p
        (P.bottom a.p + gridX (Q.top a.q-Q.bottom a.q) a.k (r-prodBottom P Q a))
        (by omega) (by omega)
      simpa only [prodPoint, tt, hs.1, Nat.add_assoc] using pc
    · simp only [prodPoint, tt, hs.2]
  · right
    constructor
    · simp only [prodPoint, tt, hs.1]
    · have qc := Q.saturated a.q
        (Q.bottom a.q + gridY (Q.top a.q-Q.bottom a.q) a.k (r-prodBottom P Q a))
        (by omega) (by omega)
      simpa only [prodPoint, tt, hs.2, Nat.add_assoc] using qc

/-- An actual construction: no classification or reflection-group hypotheses. -/
def productSCD : SCD (α × β) (ProductCover cα cβ)
    (fun x => rα x.1+rβ x.2) (n+m) where
  Label := ProductLabel P Q
  label := prodLabel P Q
  bottom := prodBottom P Q
  top := prodTop P Q
  nonempty a := by
    have := P.nonempty a.p; have := Q.nonempty a.q
    have := a.kp; have := a.kq
    unfold prodBottom prodTop; omega
  symmetric a := by
    have := P.symmetric a.p; have := Q.symmetric a.q
    have := a.kp; have := a.kq
    unfold prodBottom prodTop; omega
  point := prodPoint P Q
  point_label := prodPoint_label P Q
  point_rank := prodPoint_rank P Q
  bounds := prodBounds P Q
  recover := prodRecover P Q
  saturated := prodSaturated P Q

end

/-- ProductCover is the genuine cover relation for a product of partial orders. -/
theorem productCover_is_cover {α β : Type u}
    (leα : α → α → Prop) (leβ : β → β → Prop)
    (reflα : ∀ a, leα a a) (reflβ : ∀ b, leβ b b)
    (antisymmα : ∀ a b, leα a b → leα b a → a=b)
    (antisymmβ : ∀ a b, leβ a b → leβ b a → a=b)
    (x y : α × β) :
    ProductCover (Cover leα) (Cover leβ) x y ↔
    Cover (fun a b : α × β => leα a.1 b.1 ∧ leβ a.2 b.2) x y := by
  constructor
  · intro h
    rcases h with ⟨hc, he⟩ | ⟨he, hc⟩
    · refine ⟨⟨hc.1, ?_⟩, ?_, ?_⟩
      · rw [he]; exact reflβ y.2
      · intro e; exact hc.2.1 (congrArg Prod.fst e)
      · intro z hx hz
        have hz2 : z.2=x.2 := antisymmβ _ _ (by simpa only [he] using hz.2) hx.2
        rcases hc.2.2 z.1 hx.1 hz.1 with h | h
        · exact Or.inl (Prod.ext h hz2)
        · exact Or.inr (Prod.ext h (hz2.trans he))
    · refine ⟨⟨?_, hc.1⟩, ?_, ?_⟩
      · rw [he]; exact reflα y.1
      · intro e; exact hc.2.1 (congrArg Prod.snd e)
      · intro z hx hz
        have hz1 : z.1=x.1 := antisymmα _ _ (by simpa only [he] using hz.1) hx.1
        rcases hc.2.2 z.2 hx.2 hz.2 with h | h
        · exact Or.inl (Prod.ext hz1 h)
        · exact Or.inr (Prod.ext (hz1.trans he) h)
  · intro h
    have mid := h.2.2 (y.1,x.2) ⟨h.1.1, reflβ _⟩ ⟨reflα _, h.1.2⟩
    rcases mid with mid | mid
    · right
      have he : x.1=y.1 := (congrArg Prod.fst mid).symm
      refine ⟨he, h.1.2, ?_, ?_⟩
      · intro e; exact h.2.1 (Prod.ext he e)
      · intro z hx hz
        have q := h.2.2 (x.1,z) ⟨reflα _, hx⟩ ⟨h.1.1,hz⟩
        exact q.elim (fun e => Or.inl (congrArg Prod.snd e))
          (fun e => Or.inr (congrArg Prod.snd e))
    · left
      have he := congrArg (fun z : α × β => z.2) mid
      change x.2 = y.2 at he
      refine ⟨⟨h.1.1, ?_, ?_⟩, he⟩
      · intro e; exact h.2.1 (Prod.ext e he)
      · intro z hx hz
        have q := h.2.2 (z,x.2) ⟨hx,reflβ _⟩ ⟨hz,h.1.2⟩
        exact q.elim (fun e => Or.inl (congrArg Prod.fst e))
          (fun e => Or.inr (congrArg Prod.fst e))

end NoncrossingSCD
