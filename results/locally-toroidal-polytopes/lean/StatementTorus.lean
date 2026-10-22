import Mathlib
import StatementPolytope
import P16c.TorusIso
import P16c.TorusOrbits
import P16c.PolytopeTransfer

/-! # P16c, polytope form with the geometric toroidal maps

`TorusMap s` (`P16c/TorusDefs.lean`) is ARP §1D's toroidal map `{4,4}_(s,0)`: the
square tessellation modulo `sℤ²`, its faces recorded as vertex sets in `(ℤ/s)²`
(the images of the plane's faces, `torus_faces_from_plane`; equal images are
exactly translates by `sℤ²`, and inclusion is incidence of representatives,
`torus_faces_are_orbits`) and ordered by inclusion, with rank `torusRank s`. No group enters its
definition. `torus_identification` proves it is the coset poset
`ToroidalMap s = P([4,4]_(s,0))` of the Coxeter–Moser presentation
(`P16c/Toroid.lean`), the identification earlier cited. `p16c_polytope_geometric`
is `p16c_polytope` with the geometric maps in place of the coset posets. -/

universe v

namespace P16c

/-- The faces of `TorusMap s` are exactly the images in `ℤ²/sℤ²` of the faces of
the square tessellation of the plane (`planeFaces`, vertex sets in `ℤ²`). -/
theorem torus_faces_from_plane (s : ℕ) :
    torusFaces s = (fun F => torusProj s '' F) '' planeFaces :=
  Torus.torusFaces_eq_image

/-- For `s ≥ 3`, vertex sets in `(ℤ/s)²` record the orbits of the plane's faces under
the translations by `sℤ²` and their incidence: two faces have the same image iff
they are translates by `sℤ²`, and the image of `F` lies in that of `G` iff some
such translate of `F` lies in `G`. -/
theorem torus_faces_are_orbits (s : ℕ) (hs3 : 3 ≤ s) (F G : Set (ℤ × ℤ))
    (hF : F ∈ planeFaces) (hG : G ∈ planeFaces) :
    (torusProj s '' F ⊆ torusProj s '' G ↔
      ∃ t : ℤ × ℤ, (s : ℤ) ∣ t.1 ∧ (s : ℤ) ∣ t.2 ∧ (· + t) '' F ⊆ G) ∧
    (torusProj s '' F = torusProj s '' G ↔
      ∃ t : ℤ × ℤ, (s : ℤ) ∣ t.1 ∧ (s : ℤ) ∣ t.2 ∧ (· + t) '' F = G) := by
  rw [Torus.proj_subset_iff hs3 hF hG, Torus.proj_eq_iff_translate hs3 hF hG]
  simp [Torus.InLattice, and_assoc]

/-- **The toroidal map `{4,4}_(s,0)` is `P([4,4]_(s,0))`** (Coxeter–Moser §8.3,
ARP §1D and 2E11). For odd `s ≥ 3`, the geometric toroidal map is order
isomorphic to the coset poset of `[4,4]_(s,0) = ⟨r0, r1, r2 | ri², (r0r1)⁴,
(r1r2)⁴, (r0r2)², (r0r1r2r1)^s⟩`, preserving rank. -/
theorem torus_identification (s : ℕ) (hs : Odd s) (hs3 : 3 ≤ s) :
    ∃ e : TorusMap s ≃o ToroidalMap s hs hs3,
      ∀ F, (toroidC s hs hs3).rank (e F) = torusRank s F :=
  ⟨(Torus.toroidIso hs hs3).symm, fun F => by
    rw [← Torus.toroidIso_rank hs hs3, OrderIso.apply_symm_apply]⟩

/-- **P16c (existence of the universal polytope), geometric form.** For distinct
odd `s, u ≥ 3`:
1. the toroidal maps `{4,4}_(s,0)`, `{4,4}_(u,0)` (ARP §1D) are regular 3-polytopes;
2. `P(Γ(s,u))` is a regular 4-polytope, all of whose facets are `{4,4}_(s,0)` and
   all of whose vertex-figures are `{4,4}_(u,0)`, with automorphism group
   `Γ(s,u)` acting by left multiplication;
3. every regular 4-polytope with all facets `{4,4}_(s,0)` and all vertex-figures
   `{4,4}_(u,0)` has automorphism group a quotient of `Γ(s,u)`, the generator
   `r_i` going to the distinguished generator for some base flag `Φ`, and
   `P(Γ(s,u))` covers it. -/
theorem p16c_polytope_geometric (s u : ℕ) (hs : Odd s) (hu : Odd u) (hs3 : 3 ≤ s)
    (hu3 : 3 ≤ u) (hsu : s ≠ u) :
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
          IsCovering (gammaC s u hs hu hs3 hu3 hsu).rank rank c := by
  obtain ⟨⟨ps, rs⟩, ⟨pu, ru⟩, ⟨pg, rg, hfac, hvf, hact⟩, huniv⟩ :=
    p16c_polytope.{v} s u hs hu hs3 hu3 hsu
  set es := Torus.toroidIso hs hs3
  set eu := Torus.toroidIso hu hu3
  refine ⟨⟨ps.of_orderIso es (Torus.toroidIso_rank hs hs3), rs.of_orderIso es⟩,
    ⟨pu.of_orderIso eu (Torus.toroidIso_rank hu hu3), ru.of_orderIso eu⟩,
    ⟨pg, rg, fun F hF => ?_, fun w hw => ?_, hact⟩,
    fun Q _ rank hQ hreg hF hV => huniv Q rank hQ hreg (fun F hr => ?_) (fun w hr => ?_)⟩
  · obtain ⟨e⟩ := hfac F hF; exact ⟨e.trans es⟩
  · obtain ⟨e⟩ := hvf w hw; exact ⟨e.trans eu⟩
  · obtain ⟨e⟩ := hF F hr; exact ⟨e.trans es.symm⟩
  · obtain ⟨e⟩ := hV w hr; exact ⟨e.trans eu.symm⟩

end P16c
