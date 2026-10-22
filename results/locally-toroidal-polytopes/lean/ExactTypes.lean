import Main
import Statement
import StatementToroid
import StatementGroupForm
import StatementPolytope
import StatementTorus
import P16c.Fields

/-! Exact types of the theorem interfaces. Each example checks the entire
quantified statement, including hypotheses, local groups and universality. -/

universe v

namespace P16c

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u),
    (∀ i, Main.r s u i ^ 2 = 1) ∧
    orderOf (Main.r s u 0 * Main.r s u 1) = 4 ∧ orderOf (Main.r s u 1 * Main.r s u 2) = 4 ∧
    orderOf (Main.r s u 2 * Main.r s u 3) = 4 ∧
    (∀ i j : Fin 4, i.val + 2 ≤ j.val → Main.r s u i * Main.r s u j = Main.r s u j * Main.r s u i) ∧
    (∀ I J : Finset (Fin 4),
      Subgroup.closure (Main.r s u '' ↑I) ⊓ Subgroup.closure (Main.r s u '' ↑J) =
        Subgroup.closure (Main.r s u '' ↑(I ∩ J))) ∧
    (∃ e : Main.TorusGroup s ≃* Subgroup.closure {Main.r s u 0, Main.r s u 1, Main.r s u 2},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : Main.Γ s u) = Main.r s u i.castSucc) ∧
    Nat.card (Subgroup.closure {Main.r s u 0, Main.r s u 1, Main.r s u 2}) = 8 * s ^ 2 ∧
    (∃ e : Main.TorusGroup u ≃* Subgroup.closure {Main.r s u 1, Main.r s u 2, Main.r s u 3},
      ∀ i : Fin 3, (e (PresentedGroup.of i) : Main.Γ s u) = Main.r s u i.succ) ∧
    Nat.card (Subgroup.closure {Main.r s u 1, Main.r s u 2, Main.r s u 3}) = 8 * u ^ 2 :=
  @P16c.Main.p16c

example : ∀ {K : Type*} [Field K] [CharP K 2] (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u),
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    (∀ i, g i ^ 2 = 1) ∧ orderOf (g 0 * g 1) = 4 ∧
      orderOf (g 1 * g 2) = 4 ∧ orderOf (g 2 * g 3) = 4 ∧
      (g 0 * g 2) ^ 2 = 1 ∧ (g 0 * g 3) ^ 2 = 1 ∧ (g 1 * g 3) ^ 2 = 1 ∧
      orderOf (g 0 * g 1 * g 2 * g 1) = s ∧ orderOf (g 1 * g 2 * g 3 * g 2) = u ∧
      Nat.card (Subgroup.closure {g 0, g 1, g 2}) = 8 * s ^ 2 ∧
      Nat.card (Subgroup.closure {g 1, g 2, g 3}) = 8 * u ^ 2 ∧
      Subgroup.closure {g 0, g 1, g 2} ⊓ Subgroup.closure {g 1, g 2, g 3} =
        Subgroup.closure {g 1, g 2} :=
  @P16c.p16c_core

example : ∀ (s : ℕ) (hs : 0 < s),
    Finite (Toroid.G s) ∧ Nat.card (Toroid.G s) ≤ 8 * s ^ 2 :=
  @P16c.toroid_group_bound

example : ∀ {K : Type*} [Field K] [CharP K 2]
    (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u),
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    (∃ φ : Toroid.G s →* (Matrix (Fin 4) (Fin 4) K)ˣ,
      (∀ i : Fin 3, φ (Toroid.r s i) = g i.castSucc) ∧ Function.Injective φ ∧
        φ.range = Subgroup.closure {g 0, g 1, g 2}) ∧
    (∃ ψ : Toroid.G u →* (Matrix (Fin 4) (Fin 4) K)ˣ,
      (∀ i : Fin 3, ψ (Toroid.r u i) = g i.succ) ∧ Function.Injective ψ ∧
        ψ.range = Subgroup.closure {g 1, g 2, g 3}) :=
  @P16c.p16c_toroid

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u),
    ∃ (k : ℕ) (l m : GaloisField 2 k)
      (hl : orderOf l = s) (hm : orderOf m = u),
      CoreConclusion (generators (aParam l m) (bParam l m)
        (parameters s u hs3 hu3 hsu l m hl hm).2.2.1) s u :=
  @P16c.p16c_all

example : ∀ {K : Type*} [Field K] [CharP K 2]
    (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u)
    (l m : K) (hl : orderOf l = s) (hm : orderOf m = u),
    let g := generators (aParam l m) (bParam l m)
      (parameters s u hs3 hu3 hsu l m hl hm).2.2.1
    IsStringCGroup g :=
  @P16c.p16c_matrix_stringC

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u),
    Nat.card (Subgroup.closure {Universal.r s u 0, Universal.r s u 1,
      Universal.r s u 2}) = 8 * s ^ 2 ∧
    Nat.card (Subgroup.closure {Universal.r s u 1, Universal.r s u 2,
      Universal.r s u 3}) = 8 * u ^ 2 ∧
    (∃ e : Toroid.G s ≃* Subgroup.closure {Universal.r s u 0,
        Universal.r s u 1, Universal.r s u 2},
      ∀ i : Fin 3, (e (Toroid.r s i) : Gamma s u) = Universal.r s u i.castSucc) ∧
    (∃ e : Toroid.G u ≃* Subgroup.closure {Universal.r s u 1,
        Universal.r s u 2, Universal.r s u 3},
      ∀ i : Fin 3, (e (Toroid.r u i) : Gamma s u) = Universal.r s u i.succ) :=
  @P16c.p16c_universal_locals

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u)
    (hs3 : 3 ≤ s) (hu3 : 3 ≤ u) (hsu : s ≠ u),
    IsStringCGroup (fun i : Fin 4 => (PresentedGroup.of i : Gamma s u)) ∧
    Nat.card (Subgroup.closure {Universal.r s u 0, Universal.r s u 1,
      Universal.r s u 2}) = 8 * s ^ 2 ∧
    Nat.card (Subgroup.closure {Universal.r s u 1, Universal.r s u 2,
      Universal.r s u 3}) = 8 * u ^ 2 ∧
    (∃ e : Toroid.G s ≃* Subgroup.closure {Universal.r s u 0,
        Universal.r s u 1, Universal.r s u 2},
      ∀ i : Fin 3, (e (Toroid.r s i) : Gamma s u) = Universal.r s u i.castSucc) ∧
    (∃ e : Toroid.G u ≃* Subgroup.closure {Universal.r s u 1,
        Universal.r s u 2, Universal.r s u 3},
      ∀ i : Fin 3, (e (Toroid.r u i) : Gamma s u) = Universal.r s u i.succ) :=
  @P16c.p16c_universal_stringC

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u),
    (IsPolytope (ToroidalMap s hs hs3) 3 (toroidC s hs hs3).rank ∧
      IsRegular (ToroidalMap s hs hs3)) ∧
    (IsPolytope (ToroidalMap u hu hu3) 3 (toroidC u hu hu3).rank ∧
      IsRegular (ToroidalMap u hu hu3)) ∧
    (IsPolytope (gammaC s u hs hu hs3 hu3 hsu).Face 4 (gammaC s u hs hu hs3 hu3 hsu).rank ∧
      IsRegular (gammaC s u hs hu hs3 hu3 hsu).Face ∧
      (∀ F, (gammaC s u hs hu hs3 hu3 hsu).rank F = 3 →
        Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3)) ∧
      (∀ v, (gammaC s u hs hu hs3 hu3 hsu).rank v = 0 →
        Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3)) ∧
      ∃ e : Gamma s u ≃* ((gammaC s u hs hu hs3 hu3 hsu).Face ≃o
          (gammaC s u hs hu hs3 hu3 hsu).Face),
        ∀ (g : Gamma s u) (hg : g ∈ (gammaC s u hs hu hs3 hu3 hsu).group),
          e g = (gammaC s u hs hu hs3 hu3 hsu).act ⟨g, hg⟩) ∧
    ∀ (Q : Type v) [PartialOrder Q] (rank : Q → ℤ), IsPolytope Q 4 rank → IsRegular Q →
      (∀ F : Q, rank F = 3 → Nonempty (Set.Iic F ≃o ToroidalMap s hs hs3)) →
      (∀ v : Q, rank v = 0 → Nonempty (Set.Ici v ≃o ToroidalMap u hu hu3)) →
      ∃ π : Gamma s u →* (Q ≃o Q), Function.Surjective π ∧
        (∃ Φ : Flag Q, ∀ i : Fin 4, ∀ F ∈ Φ, (π (Universal.r s u i) F = F ↔ rank F ≠ i)) ∧
        ∃ c : (gammaC s u hs hu hs3 hu3 hsu).Face → Q,
          IsCovering (gammaC s u hs hu hs3 hu3 hsu).rank rank c :=
  @P16c.p16c_polytope

example : ∀ (s : ℕ),
    torusFaces s = (fun F => torusProj s '' F) '' planeFaces :=
  @P16c.torus_faces_from_plane

example : ∀ (s : ℕ) (hs3 : 3 ≤ s) (F G : Set (ℤ × ℤ))
    (hF : F ∈ planeFaces) (hG : G ∈ planeFaces),
    (torusProj s '' F ⊆ torusProj s '' G ↔
      ∃ t : ℤ × ℤ, (s : ℤ) ∣ t.1 ∧ (s : ℤ) ∣ t.2 ∧ (· + t) '' F ⊆ G) ∧
    (torusProj s '' F = torusProj s '' G ↔
      ∃ t : ℤ × ℤ, (s : ℤ) ∣ t.1 ∧ (s : ℤ) ∣ t.2 ∧ (· + t) '' F = G) :=
  @P16c.torus_faces_are_orbits

example : ∀ (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s),
    ∃ e : TorusMap s ≃o ToroidalMap s hs hs3,
      ∀ F, (toroidC s hs hs3).rank (e F) = torusRank s F :=
  @P16c.torus_identification

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s)
    (hu3 : 3 ≤ u) (hsu : s ≠ u),
    (IsPolytope (TorusMap s) 3 (torusRank s) ∧ IsRegular (TorusMap s)) ∧
    (IsPolytope (TorusMap u) 3 (torusRank u) ∧ IsRegular (TorusMap u)) ∧
    (IsPolytope (gammaC s u hs hu hs3 hu3 hsu).Face 4 (gammaC s u hs hu hs3 hu3 hsu).rank ∧
      IsRegular (gammaC s u hs hu hs3 hu3 hsu).Face ∧
      (∀ F, (gammaC s u hs hu hs3 hu3 hsu).rank F = 3 →
        Nonempty (Set.Iic F ≃o TorusMap s)) ∧
      (∀ v, (gammaC s u hs hu hs3 hu3 hsu).rank v = 0 →
        Nonempty (Set.Ici v ≃o TorusMap u)) ∧
      ∃ e : Gamma s u ≃* ((gammaC s u hs hu hs3 hu3 hsu).Face ≃o
          (gammaC s u hs hu hs3 hu3 hsu).Face),
        ∀ (g : Gamma s u) (hg : g ∈ (gammaC s u hs hu hs3 hu3 hsu).group),
          e g = (gammaC s u hs hu hs3 hu3 hsu).act ⟨g, hg⟩) ∧
    ∀ (Q : Type v) [PartialOrder Q] (rank : Q → ℤ), IsPolytope Q 4 rank → IsRegular Q →
      (∀ F : Q, rank F = 3 → Nonempty (Set.Iic F ≃o TorusMap s)) →
      (∀ v : Q, rank v = 0 → Nonempty (Set.Ici v ≃o TorusMap u)) →
      ∃ π : Gamma s u →* (Q ≃o Q), Function.Surjective π ∧
        (∃ Φ : Flag Q, ∀ i : Fin 4, ∀ F ∈ Φ, (π (Universal.r s u i) F = F ↔ rank F ≠ i)) ∧
        ∃ c : (gammaC s u hs hu hs3 hu3 hsu).Face → Q,
          IsCovering (gammaC s u hs hu hs3 hu3 hsu).rank rank c :=
  @P16c.p16c_polytope_geometric

example : ∀ (s u : ℕ) (hs : Odd s) (hu : Odd u),
    ∃ (k : ℕ) (l m : GaloisField 2 k), orderOf l = s ∧ orderOf m = u :=
  @P16c.fields_exist

end P16c
