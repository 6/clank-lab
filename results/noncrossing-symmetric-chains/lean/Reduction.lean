import Transfer

namespace NoncrossingSCD

/-- Published classification data, not a Lean proof of Shephard--Todd. -/
def exceptionalNumbers : List Nat :=
  [4,5,6,8,9,10,14,16,17,18,20,21,23,24,25,26,27,28,29,30,32,33,34,35,36,37]
def citedSmallNumbers : List Nat :=
  [4,5,6,8,9,10,14,16,17,18,20,21,23,24,25,26,27,28,29,32]
def certificateNumbers : List Nat := [30,33,34,35,36,37]

/-- A machine-checked check that the table partition omits and adds no entry. -/
theorem exceptional_table_split (j : Nat) :
    j ∈ exceptionalNumbers ↔ j ∈ citedSmallNumbers ∨ j ∈ certificateNumbers := by
  simp only [exceptionalNumbers, citedSmallNumbers, certificateNumbers,
    List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Six explicit inputs and the cited small-type result suffice for the table.
The hypotheses are parameters, not axioms claiming the external results. -/
theorem exceptional_reduction (S : Nat → Prop)
    (cited : ∀ j, j ∈ citedSmallNumbers → S j)
    (h30 : S 30) (h33 : S 33) (h34 : S 34)
    (h35 : S 35) (h36 : S 36) (h37 : S 37) :
    ∀ j, j ∈ exceptionalNumbers → S j := by
  intro j hj
  rcases (exceptional_table_split j).1 hj with hs | hs
  · exact cited j hs
  · simp only [certificateNumbers, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h | h | h
    · simpa only [h] using h30
    · simpa only [h] using h33
    · simpa only [h] using h34
    · simpa only [h] using h35
    · simpa only [h] using h36
    · simpa only [h] using h37

/-- An expression for a product of already specified ranked factor models. -/
structure RankedModel where
  Carrier : Type
  cover : Carrier → Carrier → Prop
  rank : Carrier → Nat
  height : Nat

def RankedModel.HasSCD (M : RankedModel) : Prop :=
  Nonempty (SCD M.Carrier M.cover M.rank M.height)

def RankedModel.product (P Q : RankedModel) : RankedModel where
  Carrier := P.Carrier × Q.Carrier
  cover := ProductCover P.cover Q.cover
  rank x := P.rank x.1 + Q.rank x.2
  height := P.height+Q.height

def RankedModel.zero : RankedModel where
  Carrier := PUnit
  cover := Cover (fun _ _ => True)
  rank _ := 0
  height := 0

def productModels : List RankedModel → RankedModel
  | [] => RankedModel.zero
  | P :: ps => P.product (productModels ps)

/-- Arbitrarily many factors, including zero factors. -/
theorem finite_product_scd (ps : List RankedModel)
    (h : ∀ P, P ∈ ps → P.HasSCD) : (productModels ps).HasSCD := by
  induction ps with
  | nil => exact ⟨zeroSCD⟩
  | cons P ps ih =>
    obtain ⟨p⟩ := h P (by simp)
    obtain ⟨q⟩ := ih (by intro Q hQ; exact h Q (by simp only [List.mem_cons]; exact Or.inr hQ))
    exact ⟨productSCD p q⟩

#print axioms productSCD
#print axioms transportSCD
#print axioms productPosetSCD
#print axioms intervalSCD_map
#print axioms product_length_spec
#print axioms reflectionLength_map
#print axioms exceptional_reduction
#print axioms finite_product_scd

end NoncrossingSCD
