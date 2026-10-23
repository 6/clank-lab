import Product

namespace NoncrossingSCD
universe u

/-- Transport the actual partition, with every inverse and preservation law explicit. -/
def transportSCD {α β : Type u} {cα : α → α → Prop} {cβ : β → β → Prop}
    {rα : α → Nat} {rβ : β → Nat} {n : Nat}
    (P : SCD α cα rα n) (f : α → β) (g : β → α)
    (gf : ∀ x, g (f x) = x) (fg : ∀ x, f (g x) = x)
    (hr : ∀ x, rβ (f x) = rα x)
    (hc : ∀ x y, cα x y → cβ (f x) (f y)) : SCD β cβ rβ n where
  Label := P.Label
  label x := P.label (g x)
  bottom := P.bottom
  top := P.top
  nonempty := P.nonempty
  symmetric := P.symmetric
  point a i lo hi := f (P.point a i lo hi)
  point_label := by intro a i lo hi; simp only [gf, P.point_label]
  point_rank := by intro a i lo hi; simp only [hr, P.point_rank]
  bounds := by
    intro x
    have h := P.bounds (g x)
    have e : rβ x = rα (g x) := by simpa only [fg] using hr (g x)
    simpa only [e] using h
  recover := by
    intro x
    have e : rβ x = rα (g x) := by simpa only [fg] using hr (g x)
    simp only [e, P.recover, fg]
  saturated := by intro a i lo hi; exact hc _ _ (P.saturated a i lo hi)

/-- Covers transport through an order isomorphism; no rankedness assumption. -/
theorem cover_map {α β : Type u} {leα : α → α → Prop} {leβ : β → β → Prop}
    (f : α → β) (g : β → α) (gf : ∀ x, g (f x)=x) (fg : ∀ y, f (g y)=y)
    (hl : ∀ x y, leβ (f x) (f y) ↔ leα x y)
    (x y : α) (h : Cover leα x y) : Cover leβ (f x) (f y) := by
  refine ⟨(hl x y).2 h.1, ?_, ?_⟩
  · intro e
    have q := congrArg g e
    simp only [gf] at q
    exact h.2.1 q
  · intro z hx hz
    have hx' : leα x (g z) := (hl x (g z)).1 (by simpa only [fg] using hx)
    have hz' : leα (g z) y := (hl (g z) y).1 (by simpa only [fg] using hz)
    rcases h.2.2 (g z) hx' hz' with h | h
    · left; simpa only [fg] using congrArg f h
    · right; simpa only [fg] using congrArg f h

/-- Exact reflection words; the index is the number of reflection factors. -/
inductive HasWord {W : Type u} (mul : W → W → W) (one : W) (T : W → Prop) :
    W → Nat → Prop where
  | nil : HasWord mul one T one 0
  | cons (t w : W) (k : Nat) : T t → HasWord mul one T w k →
      HasWord mul one T (mul t w) (k+1)

structure LengthSpec {W : Type u} (mul : W → W → W) (one : W)
    (T : W → Prop) (len : W → Nat) : Prop where
  realized : ∀ w, HasWord mul one T w (len w)
  minimal : ∀ w k, HasWord mul one T w k → len w ≤ k

theorem word_map {W V : Type u} {mul : W → W → W} {mul' : V → V → V}
    {one : W} {one' : V} {T : W → Prop} {T' : V → Prop}
    (f : W → V) (h1 : f one=one') (hm : ∀ x y, f (mul x y)=mul' (f x) (f y))
    (hT : ∀ t, T t → T' (f t)) (w : W) (k : Nat) (h : HasWord mul one T w k) :
    HasWord mul' one' T' (f w) k := by
  induction h with
  | nil => simpa only [h1] using (HasWord.nil : HasWord mul' one' T' one' 0)
  | cons t w k ht hw ih =>
    simpa only [hm] using HasWord.cons (f t) (f w) k (hT t ht) ih

/-- Reflection-preserving isomorphisms preserve minimal reflection length. -/
theorem reflectionLength_map {W V : Type u}
    {mul : W → W → W} {mul' : V → V → V} {one : W} {one' : V}
    {T : W → Prop} {T' : V → Prop} {len : W → Nat} {len' : V → Nat}
    (L : LengthSpec mul one T len) (L' : LengthSpec mul' one' T' len')
    (f : W → V) (g : V → W) (gf : ∀ x, g (f x)=x)
    (f1 : f one=one') (g1 : g one'=one)
    (fm : ∀ x y, f (mul x y)=mul' (f x) (f y))
    (gm : ∀ x y, g (mul' x y)=mul (g x) (g y))
    (fT : ∀ t, T t → T' (f t)) (gT : ∀ t, T' t → T (g t)) (w : W) :
    len' (f w)=len w := by
  apply Nat.le_antisymm
  · exact L'.minimal _ _ (word_map f f1 fm fT _ _ (L.realized w))
  · have h := L.minimal _ _ (word_map g g1 gm gT _ _ (L'.realized (f w)))
    simpa only [gf] using h

theorem absoluteLE_map {W V : Type u} (D : IntervalData W) (E : IntervalData V)
    (f : W → V) (hm : ∀ x y, f (D.mul x y)=E.mul (f x) (f y))
    (hi : ∀ x, f (D.inv x)=E.inv (f x))
    (hl : ∀ x, E.reflectionLength (f x)=D.reflectionLength x) (x y : W) :
    AbsoluteLE E (f x) (f y) ↔ AbsoluteLE D x y := by
  unfold AbsoluteLE
  rw [←hi, ←hm, hl, hl, hl]

/-- Restriction of a length-preserving group isomorphism to its NC intervals. -/
def intervalMap {W V : Type u} (D : IntervalData W) (E : IntervalData V)
    (f : W → V) (hm : ∀ x y, f (D.mul x y)=E.mul (f x) (f y))
    (hi : ∀ x, f (D.inv x)=E.inv (f x))
    (hl : ∀ x, E.reflectionLength (f x)=D.reflectionLength x) (c : W) :
    Interval D c → Interval E (f c) :=
  fun x => ⟨f x.val, (absoluteLE_map D E f hm hi hl x.val c).2 x.property⟩

/-- The reflections of a direct product act in exactly one coordinate. -/
def ProductReflections {W V : Type u} (T : W → Prop) (U : V → Prop)
    (one : W) (one' : V) (w : W × V) : Prop :=
  (T w.1 ∧ w.2=one') ∨ (w.1=one ∧ U w.2)

theorem product_word_split {W V : Type u}
    (mul : W → W → W) (mul' : V → V → V) (one : W) (one' : V)
    (T : W → Prop) (U : V → Prop)
    (h1 : ∀ x, mul one x=x) (h2 : ∀ y, mul' one' y=y)
    (w : W × V) (k : Nat)
    (h : HasWord (fun a b : W × V => (mul a.1 b.1,mul' a.2 b.2))
      (one,one') (ProductReflections T U one one') w k) :
    ∃ i j, i+j=k ∧ HasWord mul one T w.1 i ∧ HasWord mul' one' U w.2 j := by
  induction h with
  | nil => exact ⟨0,0,rfl,HasWord.nil,HasWord.nil⟩
  | cons t w k ht hw ih =>
    obtain ⟨i,j,eq,wi,wj⟩ := ih
    rcases ht with ⟨ht,he⟩ | ⟨he,ht⟩
    · refine ⟨i+1,j,by omega,HasWord.cons t.1 w.1 i ht wi,?_⟩
      simpa only [he,h2] using wj
    · refine ⟨i,j+1,by omega,?_,HasWord.cons t.2 w.2 j ht wj⟩
      simpa only [he,h1] using wi

theorem product_word_join {W V : Type u}
    (mul : W → W → W) (mul' : V → V → V) (one : W) (one' : V)
    (T : W → Prop) (U : V → Prop)
    (h1 : ∀ x, mul one x=x) (h2 : ∀ y, mul' one' y=y)
    (x : W) (y : V) (i j : Nat)
    (hx : HasWord mul one T x i) (hy : HasWord mul' one' U y j) :
    HasWord (fun a b : W × V => (mul a.1 b.1,mul' a.2 b.2))
      (one,one') (ProductReflections T U one one') (x,y) (i+j) := by
  induction hx with
  | nil =>
    simp only [Nat.zero_add]
    induction hy with
    | nil => exact HasWord.nil
    | cons t w k ht hw ih =>
      have h := HasWord.cons (one,t) (one,w) k (Or.inr ⟨rfl,ht⟩) ih
      simpa only [h1] using h
  | cons t w k ht hw ih =>
    have h := HasWord.cons (t,one') (w,y) (k+j) (Or.inl ⟨ht,rfl⟩) ih
    simpa only [h2,Nat.add_right_comm] using h

/-- The sum of the factor lengths satisfies the exact minimum-word definition. -/
theorem product_length_spec {W V : Type u}
    (mul : W → W → W) (mul' : V → V → V) (one : W) (one' : V)
    (T : W → Prop) (U : V → Prop) (len : W → Nat) (len' : V → Nat)
    (h1 : ∀ x, mul one x=x) (h2 : ∀ y, mul' one' y=y)
    (L : LengthSpec mul one T len) (L' : LengthSpec mul' one' U len') :
    LengthSpec (fun a b : W × V => (mul a.1 b.1,mul' a.2 b.2))
      (one,one') (ProductReflections T U one one') (fun w => len w.1+len' w.2) where
  realized w := product_word_join mul mul' one one' T U h1 h2 _ _ _ _
    (L.realized w.1) (L'.realized w.2)
  minimal w k h := by
    obtain ⟨i,j,eq,hi,hj⟩ := product_word_split mul mul' one one' T U h1 h2 w k h
    have := L.minimal _ _ hi
    have := L'.minimal _ _ hj
    omega

/-- Length additivity makes the product interval equality a scalar fact. -/
theorem product_interval_membership (a a' b b' n m : Nat)
    (ha : n ≤ a+a') (hb : m ≤ b+b') :
    a+b+(a'+b')=n+m ↔ a+a'=n ∧ b+b'=m := by omega

/-- The one-element empty product, with its genuine cover relation. -/
def zeroSCD : SCD PUnit (Cover (fun _ _ => True)) (fun _ => 0) 0 where
  Label := PUnit
  label _ := PUnit.unit
  bottom _ := 0
  top _ := 0
  nonempty _ := Nat.le_refl 0
  symmetric _ := rfl
  point _ _ _ _ := PUnit.unit
  point_label := by intros; rfl
  point_rank := by intros; omega
  bounds _ := ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  recover := by intro x; cases x; rfl
  saturated := by intros; omega

/-- The rank-one interval is the two-element chain. -/
def oneSCD : SCD (Fin 2) (fun x y => x.val+1=y.val) Fin.val 1 where
  Label := PUnit
  label _ := PUnit.unit
  bottom _ := 0
  top _ := 1
  nonempty _ := by decide
  symmetric _ := rfl
  point _ i _ hi := ⟨i, by omega⟩
  point_label := by intros; rfl
  point_rank := by intros; rfl
  bounds x := ⟨Nat.zero_le _, by have := x.isLt; omega⟩
  recover := by intros; rfl
  saturated := by intros; rfl

/-- Product theorem stated using actual order-theoretic covers. -/
def productPosetSCD {α β : Type u}
    (leα : α → α → Prop) (leβ : β → β → Prop)
    (reflα : ∀ a, leα a a) (reflβ : ∀ b, leβ b b)
    (antisymmα : ∀ a b, leα a b → leα b a → a=b)
    (antisymmβ : ∀ a b, leβ a b → leβ b a → a=b)
    {rα : α → Nat} {rβ : β → Nat} {n m : Nat}
    (P : SCD α (Cover leα) rα n) (Q : SCD β (Cover leβ) rβ m) :
    SCD (α × β) (Cover (fun a b => leα a.1 b.1 ∧ leβ a.2 b.2))
      (fun a => rα a.1+rβ a.2) (n+m) :=
  transportSCD (productSCD P Q) id id (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun x y h =>
      (productCover_is_cover leα leβ reflα reflβ antisymmα antisymmβ x y).1 h)

/-- Full SCD transfer to any other Coxeter interval once the reflection
isomorphism supplied by the cited theorem is provided. -/
def intervalSCD_map {W : Type u} (D : IntervalData W)
    (f g : W → W) (gf : ∀ x, g (f x)=x) (fg : ∀ x, f (g x)=x)
    (hm : ∀ x y, f (D.mul x y)=D.mul (f x) (f y))
    (hi : ∀ x, f (D.inv x)=D.inv (f x))
    (hl : ∀ x, D.reflectionLength (f x)=D.reflectionLength x) (c : W)
    (P : SCD (Interval D c) (Cover (fun x y => AbsoluteLE D x.val y.val))
      (fun x => D.reflectionLength x.val) D.essentialRank) :
    SCD (Interval D (f c)) (Cover (fun x y => AbsoluteLE D x.val y.val))
      (fun x => D.reflectionLength x.val) D.essentialRank := by
  let F := intervalMap D D f hm hi hl c
  let G : Interval D (f c) → Interval D c := fun x =>
    ⟨g x.val, (absoluteLE_map D D f hm hi hl (g x.val) c).1
      (by simpa only [fg] using x.property)⟩
  have hGF : ∀ x, G (F x)=x := by
    intro x; apply Subtype.ext; exact gf x.val
  have hFG : ∀ x, F (G x)=x := by
    intro x; apply Subtype.ext; exact fg x.val
  exact transportSCD P F G hGF hFG (fun x => hl x.val)
    (fun x y h => cover_map F G hGF hFG
      (fun a b => absoluteLE_map D D f hm hi hl a.val b.val) x y h)

end NoncrossingSCD
