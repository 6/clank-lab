import Mathlib.Tactic

namespace ADKZPricing

/-- A cell relation retains its actual vertex set as well as its edges.
    Using an ambient graph with isolated nonvertices would create spurious
    product edges. V is the common original-label type, with no quotient. -/
structure LabelledCell (V : Type*) where
  vertex : V → Prop
  edge : V → V → Prop
  edge_vertices : ∀ x y, edge x y → vertex x ∧ vertex y

namespace LabelledCell
variable {V W : Type*}

def union (G H : LabelledCell V) : LabelledCell V where
  vertex x := G.vertex x ∨ H.vertex x
  edge x y := G.edge x y ∨ H.edge x y
  edge_vertices x y h := by
    rcases h with h | h
    · exact ⟨Or.inl (G.edge_vertices x y h).1, Or.inl (G.edge_vertices x y h).2⟩
    · exact ⟨Or.inr (H.edge_vertices x y h).1, Or.inr (H.edge_vertices x y h).2⟩

def cartesian (G : LabelledCell V) (H : LabelledCell W) : LabelledCell (V × W) where
  vertex x := G.vertex x.1 ∧ H.vertex x.2
  edge x y := (G.edge x.1 y.1 ∧ x.2 = y.2 ∧ H.vertex x.2) ∨
    (H.edge x.2 y.2 ∧ x.1 = y.1 ∧ G.vertex x.1)
  edge_vertices x y h := by
    rcases h with ⟨he, hxy, hv⟩ | ⟨he, hxy, hv⟩
    · obtain ⟨hx, hy⟩ := G.edge_vertices _ _ he
      exact ⟨⟨hx, hv⟩, ⟨hy, hxy ▸ hv⟩⟩
    · obtain ⟨hx, hy⟩ := H.edge_vertices _ _ he
      exact ⟨⟨hv, hx⟩, ⟨hxy ▸ hv, hy⟩⟩

/-- Literal equality of membership on the SAME label pairs; shared
    vertices and edges survive in both cells of the union. -/
theorem union_cartesian_vertex (G G' : LabelledCell V) (H : LabelledCell W)
    (x : V × W) :
    (union (cartesian G H) (cartesian G' H)).vertex x ↔
      (cartesian (union G G') H).vertex x := by
  simp only [union, cartesian]
  tauto

theorem union_cartesian_edge (G G' : LabelledCell V) (H : LabelledCell W)
    (x y : V × W) :
    (union (cartesian G H) (cartesian G' H)).edge x y ↔
      (cartesian (union G G') H).edge x y := by
  simp only [union, cartesian]
  tauto

theorem cartesian_union_vertex (G : LabelledCell V) (H H' : LabelledCell W)
    (x : V × W) :
    (union (cartesian G H) (cartesian G H')).vertex x ↔
      (cartesian G (union H H')).vertex x := by
  simp only [union, cartesian]
  tauto

theorem cartesian_union_edge (G : LabelledCell V) (H H' : LabelledCell W)
    (x y : V × W) :
    (union (cartesian G H) (cartesian G H')).edge x y ↔
      (cartesian G (union H H')).edge x y := by
  simp only [union, cartesian]
  tauto

/-- Endpoints of every projected step remain actual factor vertices.
    A guarded product step changes just one factor along an actual edge. -/
theorem cartesian_edge_projects (G : LabelledCell V) (H : LabelledCell W)
    (x y : V × W) (he : (cartesian G H).edge x y) :
    G.vertex x.1 ∧ G.vertex y.1 ∧ H.vertex x.2 ∧ H.vertex y.2 ∧
      ((G.edge x.1 y.1 ∧ x.2 = y.2) ∨ (H.edge x.2 y.2 ∧ x.1 = y.1)) := by
  have hv := (cartesian G H).edge_vertices x y he
  refine ⟨hv.1.1, hv.2.1, hv.1.2, hv.2.2, ?_⟩
  rcases he with ⟨he, hxy, _⟩ | ⟨he, hxy, _⟩
  · exact Or.inl ⟨he, hxy⟩
  · exact Or.inr ⟨he, hxy⟩

#print axioms union_cartesian_edge
#print axioms cartesian_union_edge
#print axioms cartesian_edge_projects
end LabelledCell
end ADKZPricing
