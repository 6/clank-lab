# Independent check for p = 11 and 13, and further credits

## The check

This check is not part of the proof; the proof is the Lean project in [../lean](../lean). It confirms the finite step of Section 6 of the paper with a program written from the statement of the symmetric layer criterion, sharing no code with the formal proof. Run it from the folder above this one, with Python 3.8 or later (standard library only):

```sh
python3 checks/shape_check.py
```

It takes under a second and ends with `PASS`; a shape that is neither exceptional nor has a witness is printed as `UNCOVERED`, and the program then exits nonzero.

For $p = 11$ and $p = 13$ it lists every concentrated profile up to order: $p$ class sizes between $0$ and $p-1$, with sum $2p-1$ and $\sum_g\binom{v_g}{2}\ge 2p-4$. For each it checks that the shape is one of the three exceptional shapes, or that rule B, some rule H($\rho$) with $2\le\rho\le p-1$, or a depth list of Table 1 of the paper meets the three conditions of the criterion, and otherwise it searches all depths of the right parity. The expected output is

```text
p = 11: 526 concentrated shapes; exceptional 3, rule B 390, rule H 130, Table 1 3, other witness 0, uncovered 0
p = 13: 1435 concentrated shapes; exceptional 3, rule B 1057, rule H 375, Table 1 0, other witness 0, uncovered 0
PASS
```

Other primes can be given as arguments. `python3 checks/shape_check.py 7` reports the three shapes $(5,4,4)$, $(4,3,3,3)$ and $(4,2,2,2,2,1)$ as uncovered, which is why the method starts at $p = 11$; for $p = 17$, $19$ and $23$ rules B and H cover every shape except the three exceptional ones.

## Further credits

- Weidong Gao and Ravindranathan Thangadurai, *A variant of Kemnitz conjecture*, Journal of Combinatorial Theory, Series A 107 (2004), 69–86, [doi:10.1016/j.jcta.2004.03.009](https://doi.org/10.1016/j.jcta.2004.03.009): the conjecture, the lower-bound example, the theorem for primes at least 67 (their Theorem 1), the lifting lemma (their Lemma 2.5) and the averaging over the $p+1$ subgroups of order $p$ (pp. 83–84).
- Weidong Gao, Alfred Geroldinger and Wolfgang A. Schmid, *Inverse zero-sum problems*, Acta Arithmetica 128 (2007), 245–279, [doi:10.4064/aa128-3-5](https://doi.org/10.4064/aa128-3-5): Theorem 5.1 (the extremal sets and $\mathsf g(C_p\oplus C_p) = 2p-1$ for primes $p\ge 47$), Lemma 5.3(1) (the lifting criterion), Lemma 5.13 (the averaging) and Lemmas 5.7 and 5.9 (the bound $2(v_g-2)$ per repeated element, and the theorem of Dias da Silva and Hamidoune on the support of the projected sequence with Cauchy–Davenport on pairs; Lemma 5.9 assumes $p\ge 47$).
- Weidong Gao, Qing-Hu Hou, Wolfgang A. Schmid and Ravindranathan Thangadurai, *On short zero-sum subsequences II*, Integers 7 (2007), #A21, [journal copy](https://math.colgate.edu/~integers/h21/h21.pdf): Lemma 5.2, the lifting criterion extended to higher rank.
- Béla Bajnok, *Additive Combinatorics: A Menu of Research Problems*, [arXiv:1705.07444v2](https://arxiv.org/abs/1705.07444v2) (2017; CRC Press, 2018): Proposition F.97, Conjecture F.98, Theorem F.99 and Problem F.100, "Prove that Conjecture F.98 holds for prime numbers 11 ≤ p ≤ 43."
- Arnfried Kemnitz, *On a lattice point problem*, Ars Combinatoria 16B (1983), 151–160: the lower bound and its example set, and the primes 3, 5 and 7, as recorded in Bajnok's book (Proposition F.97).
- Philippe Guillot, Luz E. Marchan, Oscar Ordaz, Wolfgang A. Schmid and Hanane Zerdoum, *On the Harborth constant of* $`C_3\oplus C_{3p}`$, Journal de Théorie des Nombres de Bordeaux 31 (2019), 613–633, [doi:10.5802/jtnb.1097](https://doi.org/10.5802/jtnb.1097): the 2019 statement of what was known.
- Heiko Harborth, *Ein Extremalproblem für Gitterpunkte*, Journal für die reine und angewandte Mathematik 262/263 (1973), 356–360: the origin of the constant.
- José António Dias da Silva and Yahya Ould Hamidoune, *Cyclic spaces for Grassmann derivatives and additive theory*, Bulletin of the London Mathematical Society 26 (1994), 140–146, [doi:10.1112/blms/26.2.140](https://doi.org/10.1112/blms/26.2.140), and Noga Alon, Melvyn B. Nathanson and Imre Ruzsa, *The polynomial method and restricted sums of congruence classes*, Journal of Number Theory 56 (1996), 404–417, [doi:10.1006/jnth.1996.0029](https://doi.org/10.1006/jnth.1996.0029): the restricted-sumset theorem, and the method by which it is formalized here.
- Augustin-Louis Cauchy (1813) and Harold Davenport, *On the addition of residue classes*, Journal of the London Mathematical Society 10 (1935), 30–32, [doi:10.1112/jlms/s1-10.37.30](https://doi.org/10.1112/jlms/s1-10.37.30): the Cauchy–Davenport theorem, taken from Mathlib.
- Lean 4 and [Mathlib](https://github.com/leanprover-community/mathlib4) provide the formal proof infrastructure, including the Combinatorial Nullstellensatz and the Cauchy–Davenport theorem.

## Source notes

- The quotations of Bajnok's book are from arXiv version 2; the CRC Press edition was not consulted.
- The page reference to Gao and Thangadurai's averaging (pp. 83–84) and the identification of their Lemma 2.5 with the lifting criterion are from a reading of the journal article; the other statements of their paper are quoted as Gao, Geroldinger and Schmid state them (Section 5 of *Inverse zero-sum problems*).
