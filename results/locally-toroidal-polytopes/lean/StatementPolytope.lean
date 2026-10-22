import Mathlib
import P16c.PolytopeAssembly

/-! # P16c, polytope form

Definitions (checked against McMullen–Schulte, *Abstract Regular Polytopes*):
`IsPolytope`, `FlagAdjacent`, `IsRegular`, `IsCovering` (ARP §2A, 2B, 2D) in `P16c/Polytope.lean`;
`StringCGroup`, its coset poset `Face` with `rank` (ARP §2E) in
`P16c/CosetPoset.lean`; `Gamma s u` in `P16c/GroupPresentation.lean`; the toroid
presentation `Toroid.G s` in `P16c/Toroid.lean`; `toroidC`, `ToroidalMap` and
`gammaC` (the groups with their distinguished generators) in
`P16c/PolytopeAssembly.lean`. -/

universe v

namespace P16c

/-- **P16c (existence of the universal polytope).** For distinct odd `s, u ≥ 3`:
1. the toroidal maps `{4,4}_(s,0)`, `{4,4}_(u,0)` (the coset posets of their
   groups) are regular 3-polytopes;
2. `P(Γ(s,u))` is a regular 4-polytope, all of whose facets are `{4,4}_(s,0)` and
   all of whose vertex-figures are `{4,4}_(u,0)`, with automorphism group
   `Γ(s,u)` acting by left multiplication (ARP 2E11, 2E12(a));
3. every regular 4-polytope with all facets `{4,4}_(s,0)` and all vertex-figures
   `{4,4}_(u,0)` has automorphism group a quotient of `Γ(s,u)`, the generator
   `r_i` going to the distinguished generator for some base flag `Φ` (the
   automorphism moving exactly the `i`-face of `Φ`), and `P(Γ(s,u))` covers it
   (ARP 4A2: `P(Γ(s,u))` is the universal member of the class). -/
theorem p16c_polytope (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s) (hu3 : 3 ≤ u)
    (hsu : s ≠ u) :
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
  p16c_polytope_proof s u hs hu hs3 hu3 hsu

end P16c
