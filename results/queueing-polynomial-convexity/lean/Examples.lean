import Final

open BLSUnit1

example (a b : ℝ) : BLSH.complete [a, b] 2 = a^2 + a*b + b^2 := by
  norm_num [BLSH.complete, Finset.sum_range_succ]
  <;> ring

example (n L : ℕ) (x : Edge n L → ℝ) : sourcePolynomial n L 0 x = 1 := by
  simp [sourcePolynomial]

-- There is one edge when n = L = 2; repetitions retain both prefix denominators.
def soleEdge : Edge 2 2 := ⟨Finset.univ, by decide⟩

example : inclusivePrefix (fun _ : Fin 2 => soleEdge) 0 = Finset.univ := by decide
example : inclusivePrefix (fun _ : Fin 2 => soleEdge) 1 = Finset.univ := by decide

example : stdSimplex ℝ (Edge 2 3) = ∅ := BLSUnit3.empty_simplex (by decide)

example (x : Edge 2 2 → ℝ) :
    BLSUnit2.weight x (fun _ : Fin 2 => soleEdge) = (x soleEdge)^2 / 4 := by
  have h0 : inclusivePrefix (fun _ : Fin 2 => soleEdge) 0 = Finset.univ := by decide
  have h1 : inclusivePrefix (fun _ : Fin 2 => soleEdge) 1 = Finset.univ := by decide
  simp only [BLSUnit2.weight, Fin.prod_univ_two, h0, h1]
  norm_num
  ring
