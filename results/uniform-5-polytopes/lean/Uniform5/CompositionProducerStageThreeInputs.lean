import Uniform5.CompositionU3IdentificationInputs
import Uniform5.CompositionCenteredStars

/-! The producer cross-checks QFOLLOW and LU, kept separate from U3.
Their floating prefilters and fitted frames are not certified in the paper.
These propositions record their exact mathematical claims, not the weaker
fact that the producer prints a successful status. No classification theorem
needs these cross-checks when the independent U3 route is used. -/
noncomputable section
namespace Uniform5.Composition
open Set
local instance : DecidableEq KnownFiveName := Classical.decEq _

/-- Exact point and facet indices, with a model-point correspondence for
 each facet. Only values on the model figure's vertices are used. -/
structure ProducerDiscreteData where
  pointCount : ℕ
  point : Fin pointCount → Space 5
  facetCount : ℕ
  facetType : Fin facetCount → CanonicalFacetName
  correspondence : Fin facetCount → Space 4 → Fin pointCount

noncomputable def ProducerDiscreteData.facet (N : LibraryNumericalData)
    (D : ProducerDiscreteData) (i : Fin D.facetCount) : Set (Space 5) :=
  convexHull ℝ ((D.point ∘ D.correspondence i) ''
    (N.figureModel (D.facetType i)).extremePoints ℝ)

/-- The indexed data are the actual vertices and facets of V; the
correspondences are exact isometries of the model figure. -/
structure ProducerDataRealizes (N : LibraryNumericalData)
    (D : ProducerDiscreteData) (V : Set (Space 5)) : Prop where
  points_injective : Function.Injective D.point
  points_exact : Set.range D.point = V.extremePoints ℝ
  facets_injective : Function.Injective (D.facet N)
  facets_exact : ∀ F, Facet V F ↔ ∃ i, D.facet N i = F
  correspondence_exact : ∀ i, ∃ g : Space 4 →ᵃⁱ[ℝ] Space 5,
    g '' N.figureModel (D.facetType i) = D.facet N i ∧
    ∀ t ∈ (N.figureModel (D.facetType i)).extremePoints ℝ,
      g t = D.point (D.correspondence i t)

/-- A data facet has its actual whole-polytope facet type and its exact
model-point correspondence. Merely matching the shape of X_K would not
identify K for the snub-prism orientation defects. -/
structure ProducerPolytopeDataRealizes (N : LibraryNumericalData)
    (D : ProducerDiscreteData) (P : Set (Space 5)) (v c : Space 5) : Prop where
  figure_data : ProducerDataRealizes N D (vertexFigure P v c)
  full_facets : ∀ i, ∃ g : Space 4 →ᵃⁱ[ℝ] Space 5,
    Facet P (g '' N.model (D.facetType i)) ∧
    g (N.baseVertex (D.facetType i)) = v ∧
    (g '' N.model (D.facetType i)) ∩ vertexFigure P v c = D.facet N i ∧
    ∀ t ∈ (N.figureModel (D.facetType i)).extremePoints ℝ,
      g t = D.point (D.correspondence i t)

/-- The producer branch data describe precisely its recorded full facets,
including the model correspondences, before any global extension claim. -/
structure ProducerStarDataRealizes (N : LibraryNumericalData)
    (D : ProducerDiscreteData) (X : U3StarData) : Prop where
  figure_data : ProducerDataRealizes N D (X.figureEmbedding '' X.figure.carrier)
  full_facets : ∃ p : Fin D.facetCount ≃ Fin X.facets.length, ∀ i,
    D.facetType i = (X.facets.get (p i)).name ∧
    D.facet N i = (X.facets.get (p i)).placement '' N.figureModel (D.facetType i) ∧
    ∀ t ∈ (N.figureModel (D.facetType i)).extremePoints ℝ,
      (X.facets.get (p i)).placement t = D.point (D.correspondence i t)

/-- The actual E_K tables used by the producer. Ridge labels are retained
explicitly; the source generates the tables by stabilizers and, for
polyhedron prisms, configuration-preserving cyclic relabellings. -/
structure ProducerRelabelingData where
  allowed : CanonicalFacetName → Set (Space 4 ≃ᵃⁱ[ℝ] Space 4)
  ridgeLabel : CanonicalFacetName → Set (Space 4) → CellType

/-- Every retained relabelling is exact, fixes K[0], preserves X_K, and
preserves the labels of its ridges. Missing exact relabellings can only
prevent a data match. -/
def ProducerRelabelingsExact (N : LibraryNumericalData)
    (E : ProducerRelabelingData) : Prop :=
  ∀ n e, e ∈ E.allowed n →
    e (N.baseVertex n) = N.baseVertex n ∧
    e '' N.figureModel n = N.figureModel n ∧
    ∀ H, Facet (N.figureModel n) H →
      Facet (N.figureModel n) (e '' H) ∧ E.ridgeLabel n (e '' H) = E.ridgeLabel n H

/-- Paper QFOLLOW comparison: ids = perm ∘ c ∘ e, one facet for one
facet, with its library type unchanged. This is an equality of indexed
exact data, not coordinate-ball overlap. -/
def ProducerDataIsomorphism (N : LibraryNumericalData) (E : ProducerRelabelingData)
    (Q b : ProducerDiscreteData) : Prop :=
  ∃ p : Fin Q.pointCount ≃ Fin b.pointCount,
    ∃ f : Fin Q.facetCount ≃ Fin b.facetCount, ∀ i,
      b.facetType (f i) = Q.facetType i ∧
      ∃ e ∈ E.allowed (Q.facetType i),
        ∀ t ∈ (N.figureModel (Q.facetType i)).extremePoints ℝ,
          b.correspondence (f i) t = p (Q.correspondence i (e t))

/-- The branch index and parsed construction name shared by the two
producer reports. -/
structure ProducerStageThreeRow where
  index : ℕ
  vf : ℕ
  branch : ℕ
  known : Option KnownFiveName

/-- Literal logical projection of either the QFOLLOW or LU computation
JSONL output. Timing and diagnostic search counters are omitted. -/
structure ProducerStageThreeReportRow where
  index : ℕ
  vf : ℕ
  branch : ℕ
  known : Option String
  status : String

def ProducerStageThreeReportRow.Interprets (r : ProducerStageThreeReportRow)
    (b : ProducerStageThreeRow) : Prop :=
  r.index = b.index ∧ r.vf = b.vf ∧ r.branch = b.branch ∧
    r.known = b.known.map KnownFiveName.sourceName

/-- Untrusted interpretation of the 979 producer branch records. The
known model coordinates and the exact branch star are explicit inputs. -/
structure ProducerStageThreeData where
  rows : Fin 979 → ProducerStageThreeRow
  qfollowReport : Fin 979 → ProducerStageThreeReportRow
  luReport : Fin 979 → ProducerStageThreeReportRow
  star : Fin 979 → U3StarData
  discrete : Fin 979 → ProducerDiscreteData
  knownDiscrete : KnownFiveName → ProducerDiscreteData

noncomputable def ProducerStageThreeData.identified (B : ProducerStageThreeData) :
    Finset (Fin 979) := Finset.univ.filter (fun i => (B.rows i).known.isSome)

/-- QFOLLOW, as stated: the 975 identified branches have the exact data
of their known constructions under a point bijection, with equal radii;
the other four branches have no identified name. Exact model/frame and
prefilter correctness are included in this input, not proved by its
successful producer status. -/
structure QFOLLOW (N : LibraryNumericalData) (M : U3KnownModelData)
    (E : ProducerRelabelingData) (B : ProducerStageThreeData) : Prop where
  report_projection : ∀ i, (B.qfollowReport i).Interprets (B.rows i)
  relabelings_exact : ProducerRelabelingsExact N E
  identified_count : B.identified.card = 975
  distinct_known_count : (B.identified.image (fun i => (B.rows i).known)).card = 628
  known_constructions : ∀ i n, (B.rows i).known = some n →
    KnownFiveModel n (M.model n) ∧ ∃ hQ : UnitUniform 5 (M.model n),
      M.root n ∈ (M.model n).extremePoints ℝ ∧
      M.center n = vertexCentroid (vertices (M.model n) (uniform_finitePolytope hQ.1))
  exact_data : ∀ i n, (B.rows i).known = some n →
    ProducerPolytopeDataRealizes N (B.knownDiscrete n)
      (M.model n) (M.root n) (M.center n) ∧
    ProducerStarDataRealizes N (B.discrete i) (B.star i) ∧
    ProducerDataIsomorphism N E (B.knownDiscrete n) (B.discrete i) ∧
    intrinsicRadius (M.model n) = (B.star i).radius
  report_identified : ∀ i n, (B.rows i).known = some n →
    (B.qfollowReport i).status = "follows"
  report_unidentified : ∀ i, (B.rows i).known = none →
    (B.qfollowReport i).status = "not-identified"
  unidentified_one_figure : ∀ i j, (B.rows i).known = none → (B.rows j).known = none →
    ((B.rows i).index, (B.rows i).vf) = ((B.rows j).index, (B.rows j).vf)

/-- No report needs a separate arithmetic assumption for the four
unidentified branches once its 975 identified entries are known. -/
theorem QFOLLOW.unidentified_count {N : LibraryNumericalData} {M : U3KnownModelData}
    {E : ProducerRelabelingData} {B : ProducerStageThreeData}
    (h : QFOLLOW N M E B) : (Finset.univ \ B.identified).card = 4 := by
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    h.identified_count]

/-- The vertex star used by the producer's facet-type signature. -/
noncomputable def producerModelStarPoints (N : LibraryNumericalData)
    (n : CanonicalFacetName) : Finset (Space 4) :=
  insert (N.baseVertex n) ((N.vertexSet n).filter (fun x => dist x (N.baseVertex n) = 1))

/-- Sorted squared distances over unordered pairs, precisely the distance
part of cert_qfollow.Lib.sig. -/
noncomputable def producerModelStarDistances (N : LibraryNumericalData)
    (n : CanonicalFacetName) : List ℝ :=
  let L := (producerModelStarPoints N n).toList
  let I := List.finRange L.length
  (((I.product I).filter (fun ij => ij.1 < ij.2)).map
    (fun ij => dist (L.get ij.1) (L.get ij.2) ^ 2)).mergeSort (· ≤ ·)

/-- Frobenius norm in the fixed five-dimensional orthonormal coordinate
basis, as used by the producer coset check. -/
noncomputable def producerFrobeniusDistance (g h : Space 5 ≃ᵃⁱ[ℝ] Space 5) : ℝ :=
  Real.sqrt (∑ i : Fin 5, ∑ j : Fin 5,
    ((g.linearIsometryEquiv (EuclideanSpace.single i 1)) j -
      (h.linearIsometryEquiv (EuclideanSpace.single i 1)) j) ^ 2)

/-- Any choice of orientations of the same full-facet types over the same
vertex-figure facet point sets. No convexity or separation is imposed:
these are precisely the alternatives that the orientation test may refute. -/
def ProducerAlternativeStar (N : LibraryNumericalData) (X Y : U3StarData) : Prop :=
  Y.root = X.root ∧ Y.center = X.center ∧ Y.radius = X.radius ∧
    ∃ p : Fin X.facets.length ≃ Fin Y.facets.length, ∀ i,
      (Y.facets.get (p i)).name = (X.facets.get i).name ∧
      (Y.facets.get (p i)).placement (N.baseVertex (Y.facets.get (p i)).name) = X.root ∧
      (Y.facets.get (p i)).placement '' N.figureModel (Y.facets.get (p i)).name =
        (X.facets.get i).placement '' N.figureModel (X.facets.get i).name

/-- A symmetry of the model figure at K[0] which does not extend to a
symmetry of the whole facet is precisely an orientation defect. -/
def ProducerOrientationDefect (N : LibraryNumericalData) (n : CanonicalFacetName) : Prop :=
  ∃ e : Space 4 ≃ᵃⁱ[ℝ] Space 4,
    e (N.baseVertex n) = N.baseVertex n ∧
    e '' N.figureModel n = N.figureModel n ∧ e '' N.model n ≠ N.model n

/-- Raw exact group, candidate and error-bound interpretations for a
producer branch. The list retains multiplicity; it is not a quotient by
rounded matrix values. -/
structure ProducerLocalData where
  generators : List (Space 5 ≃ᵃⁱ[ℝ] Space 5)
  group : Subgroup (Space 5 ≃ᵃⁱ[ℝ] Space 5)
  candidates : Space 5 → List (Space 5 ≃ᵃⁱ[ℝ] Space 5)
  first : Space 5 → Space 5 ≃ᵃⁱ[ℝ] Space 5
  coset : (w : Space 5) → Fin (candidates w).length → Space 5 ≃ᵃⁱ[ℝ] Space 5
  epsilon : (w : Space 5) → Fin (candidates w).length → ℝ
  epsilonMax : Space 5 → ℝ

/-- Four exact LU checks, with the paper's numbering. The candidate
coverage clause retains every genuinely compatible exact congruence.
The error comparison is a Frobenius bound, not equality inferred from
ball overlap. Orientation alternatives range over every exact placement. -/
structure ProducerFourChecks (N : LibraryNumericalData) (X : U3StarData)
    (D : ProducerLocalData) : Prop where
  step4_types : ∀ n m : CanonicalFacetName, n ≠ m →
    intrinsicRadius (N.model n) ≠ intrinsicRadius (N.model m) ∨
      producerModelStarDistances N n ≠ producerModelStarDistances N m
  step1_generated : D.group = Subgroup.closure {g | g ∈ D.generators}
  step1_fixes : ∀ g ∈ D.generators,
    g X.root = X.root ∧ g X.center = X.center ∧ facetSetImage g (X.star N) = X.star N
  step2_complete : ∀ w, starNeighbor X.root w (X.star N) →
    ∀ g ∈ neighborStarCandidates X.root w (X.star N), g X.center = X.center →
      g ∈ D.candidates w
  step2_anchor_geometry : ∀ w, starNeighbor X.root w (X.star N) →
    ∀ j : Fin (D.candidates w).length,
      let g := (D.candidates w).get j
      g X.root = w ∧ g X.center = X.center ∧
      ∃ ia ib : Fin X.facets.length,
        w ∈ X.facet N ia ∧ (∀ k : Fin X.facets.length, k.val < ia.val → w ∉ X.facet N k) ∧
        (X.facets.get ia).name = (X.facets.get ib).name ∧
        g '' X.facet N ib = X.facet N ia ∧
        ∃ a : Fin 5 → Space 5,
          a 0 = X.root ∧ LinearIndependent ℝ (fun k => a k - X.center) ∧
          (∀ k, a k ∈ (X.facet N ib).extremePoints ℝ ∧
            g (a k) ∈ (X.facet N ia).extremePoints ℝ) ∧
          ∀ k, k ≠ 0 → Edge (X.facet N ib) X.root (a k)
  step2_first : ∀ w, starNeighbor X.root w (X.star N) →
    (D.candidates w).head? = some (D.first w)
  step2_coset : ∀ w, starNeighbor X.root w (X.star N) →
    ∀ j : Fin (D.candidates w).length,
      D.coset w j ∈ D.group ∧
      producerFrobeniusDistance ((D.coset w j).trans (D.first w))
        ((D.candidates w).get j) ≤ D.epsilon w j ∧
      D.epsilon w j ≤ D.epsilonMax w
  step2_small : ∀ w, starNeighbor X.root w (X.star N) →
    2 * X.radius * D.epsilonMax w < 1 / 2
  step3_defect_types : ∀ n : CanonicalFacetName,
    ProducerOrientationDefect N n ↔
      n.val = FacetLibraryName.polyhedronPrism 16 ∨
      n.val = FacetLibraryName.polyhedronPrism 17
  step3_orientations : ∀ Y, ProducerAlternativeStar N X Y → Y.star N ≠ X.star N →
    (∃ F ∈ Y.star N, ∃ G ∈ Y.star N,
      ∃ x ∈ F.extremePoints ℝ, ∃ y ∈ G.extremePoints ℝ,
        0 < dist x y ∧ dist x y < 1) ∨
    ∃ a : Space 5 ≃ᵃⁱ[ℝ] Space 5,
      a X.root = X.root ∧ a X.center = X.center ∧
        facetSetImage a (X.star N) = Y.star N

/-- LU: all four checks pass for the 975 identified producer branches.
This is an explicit, unused-by-U3 cross-check input. The producer's
floating candidate/orientation prefilters do not discharge its exact
coverage clauses. -/
structure LU (N : LibraryNumericalData) (B : ProducerStageThreeData)
    (D : Fin 979 → ProducerLocalData) : Prop where
  report_projection : ∀ i, (B.luReport i).Interprets (B.rows i)
  identified_count : B.identified.card = 975
  checks : ∀ i n, (B.rows i).known = some n → ProducerFourChecks N (B.star i) (D i)
  report_identified : ∀ i n, (B.rows i).known = some n →
    (B.luReport i).status = "forced"
  report_unidentified : ∀ i, (B.rows i).known = none →
    (B.luReport i).status = "not-identified"

end Uniform5.Composition
