import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Steinberg

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def graphText : String := include_str "../../data/graph.txt"
def rotationText : String := include_str "../../data/rotation.txt"

/-- Commit one decimal field to the reversed current row. -/
def finishNumber (number : Option Nat) (row : List Nat) : List Nat :=
  match number with
  | none => row
  | some n => n :: row

/-- Unsigned decimal rows. A colon is a field separator; comments occupy whole lines. -/
def scanRows : List UInt8 → List Nat → List (List Nat) → Option Nat → Bool →
    Option (List (List Nat))
  | [], row, rows, number, _ =>
    let row := finishNumber number row
    some ((if row.isEmpty then rows else row.reverse :: rows).reverse)
  | c :: cs, row, rows, number, comment =>
    if c.toNat == 10 then
      let row := finishNumber number row
      scanRows cs [] (if row.isEmpty then rows else row.reverse :: rows) none false
    else if comment then scanRows cs row rows number true
    else if c.toNat == 35 then
      if row.isEmpty && number.isNone then scanRows cs [] rows none true else none
    else if 48 ≤ c.toNat && c.toNat ≤ 57 then
      scanRows cs row rows (some (number.getD 0 * 10 + (c.toNat - 48))) false
    else if c.toNat == 32 || c.toNat == 9 || c.toNat == 13 || c.toNat == 58 then
      scanRows cs (finishNumber number row) rows none false
    else none

def parseRows (text : String) : Option (List (List Nat)) :=
  scanRows text.toUTF8.data.toList [] [] none false

structure GraphData where
  vertices : Nat
  declaredEdges : Nat
  edges : List (Nat × Nat)

def parseEdges : List (List Nat) → Option (List (Nat × Nat))
  | [] => some []
  | [u, v] :: rows => do return (u, v) :: (← parseEdges rows)
  | _ => none

def parseGraph (text : String) : Option GraphData := do
  match ← parseRows text with
  | [n, m] :: rows => return ⟨n, m, ← parseEdges rows⟩
  | _ => none

def graphData : GraphData := (parseGraph graphText).getD ⟨0, 0, []⟩
def edgeList : List (Nat × Nat) := graphData.edges

def graphOK (data : GraphData) : Bool :=
  (data.vertices == 82) && ((data.declaredEdges == 136) &&
  ((data.edges.length == 136) && ((data.edges.all (fun e => e.1 < e.2 && e.2 < 82)) &&
    decide data.edges.Nodup)))

def rotationRows : List (List Nat) := (parseRows rotationText).getD []
def rotation : List (List Nat) := rotationRows.map List.tail

def rotationOK (rows : List (List Nat)) : Bool :=
  (rows.length == 82) && ((rows.map (fun r => r.headD 0) == List.range 82) &&
    rows.all (fun r => !r.isEmpty &&
      (r.tail.all (fun v => v < 82) &&
        (decide r.tail.Nodup && !(r.tail.contains (r.headD 0))))))

/-- The full included graph is parsed and validated by kernel reduction. -/
theorem graph_parse_valid : (parseGraph graphText).any graphOK = true := by decide +kernel

/-- The full included rotation is parsed and validated by kernel reduction. -/
theorem rotation_parse_valid : (parseRows rotationText).any rotationOK = true := by decide +kernel

theorem graph_checked : graphOK graphData = true := by
  have h := graph_parse_valid
  cases hp : parseGraph graphText with
  | none => simp [hp] at h
  | some data => simpa [graphData, hp] using h

theorem rotation_checked : rotationOK rotationRows = true := by
  have h := rotation_parse_valid
  cases hp : parseRows rotationText with
  | none => simp [hp] at h
  | some rows => simpa [rotationRows, hp] using h

theorem graph_header : graphData.vertices = 82 ∧ graphData.declaredEdges = 136 := by
  have h := graph_checked
  simp only [graphOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2.1⟩

theorem edgeList_length : edgeList.length = 136 := by
  have h := graph_checked
  simp only [graphOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.2.1

theorem edgeList_canonical : ∀ e ∈ edgeList, e.1 < e.2 ∧ e.2 < 82 := by
  have h := graph_checked
  simp only [graphOK, Bool.and_eq_true, beq_iff_eq] at h
  simpa only [edgeList, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h.2.2.2.1

theorem edgeList_nodup : edgeList.Nodup := by
  have h := graph_checked
  simp only [graphOK, Bool.and_eq_true, beq_iff_eq] at h
  exact of_decide_eq_true h.2.2.2.2

theorem rotation_length : rotation.length = 82 := by
  have h := rotation_checked
  simp only [rotationOK, Bool.and_eq_true, beq_iff_eq] at h
  simpa only [rotation, List.length_map] using h.1

theorem rotation_labels : rotationRows.map (fun r => r.headD 0) = List.range 82 := by
  have h := rotation_checked
  simp only [rotationOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.1

/-- The undirected simple graph defined by the exact parsed edge lines. -/
def graph : SimpleGraph (Fin 82) where
  Adj u v := u ≠ v ∧ ((u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList)
  symm := ⟨fun u v h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs
  (Decidable (u ≠ v ∧ ((u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList)))

theorem graph_adj_iff (u v : Fin 82) :
    graph.Adj u v ↔ u ≠ v ∧ ((u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList) := Iff.rfl

end Steinberg
