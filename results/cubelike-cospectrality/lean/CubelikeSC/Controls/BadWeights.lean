import CubelikeSC.Cert.Defs
open CubelikeSC.Cert
-- Corruption control: the n = 127, m = 7 key of data/d7k3.cert with its weights
-- removed. Its plain coset minima stay within the budget, so the kernel proves the check false.
example : Entry.check (127, 7, [(-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3)], []) = false := by
  decide +kernel
