# Further credits

Liam Solus, *Simplices for numeral systems*, Transactions of the American
Mathematical Society 371 (2019), 2089–2107,
[DOI](https://doi.org/10.1090/tran/7424),
[preprint version 2](https://arxiv.org/abs/1706.00480v2): Section 4 defines
the base-r $n$-simplex for $r \ge 2$ and $n \ge 1$ and proves that its
$h^\ast$-polynomial is real-rooted and unimodal. Section 5 observes that
"computations suggest that the simplices $B_{(r,n)}$ are also Ehrhart
positive." The theorem here answers that observation in the negative; the
real-rootedness theorem is unaffected.

Fu Liu, *On positivity of Ehrhart polynomials*, in Recent Trends in
Algebraic Combinatorics, Springer, 2019, 189–237,
[DOI](https://doi.org/10.1007/978-3-030-05141-9_6),
[preprint version 2](https://arxiv.org/abs/1711.09962v2): Section 5.1.1
states "Conjecture 5.1.1 (Solus). The base-r d-simplex is Ehrhart
positive." Formula (1.1), relating the Ehrhart polynomial to the
$h^\ast$-vector, and the equalities (1.2) are the standard facts the paper
quotes from this survey.

Fu Liu and Liam Solus, *On the relationship between Ehrhart unimodality and
Ehrhart positivity*, Annals of Combinatorics 23 (2019), 347–365,
[DOI](https://doi.org/10.1007/s00026-019-00429-8),
[preprint version 1](https://arxiv.org/abs/1804.08258v1): Section 2.3 gives
the convex-hull description of the base-r $d$-simplex and states
Conjecture 2.2, "For r ≥ 2 and d ≥ 1, the base-r d-simplex is Ehrhart
positive."

Two recent papers study Ehrhart positivity and unimodular triangulations
for other families of lattice simplices in Hermite normal form. Justus
Bruckamp, Jhon B. Caicedo and Martina Juhnke,
[Unimodular triangulations and Ehrhart theory for two families of Hermite normal form simplices](https://arxiv.org/abs/2608.28282v1)
(posted August 28, 2026), prove Ehrhart positivity in their Theorems 4.5
and 5.12 for the families they define there. Feihu Liu, Jinlong Tang, Sihao
Tao and Zihao Zhang,
[Two families of Hermite normal form simplices](https://arxiv.org/abs/2609.36818v3)
(first posted September 29, 2026), prove in their Theorem 1.2 that the
Ehrhart coefficients of the family they denote $T_{(d,N)}$ are positive and
unimodal. Neither paper addresses the base-r simplices, and the proof here
does not use their results.

Luis Ferroni and Akihiro Higashitani,
[Examples and counterexamples in Ehrhart theory](https://arxiv.org/abs/2307.10852v4),
collect polytopes with negative Ehrhart coefficients in Section 4.1;
Theorem 4.1 there, from Hibi, Higashitani, Tsuchiya and Yoshida, gives for
every $d \ge 3$ a lattice polytope whose coefficients of degree
$1, \dots, d-2$ are all negative. Esme Bajo, Benjamin Braun, Giulia
Codenotti, Johannes Hofscheier and Andrés R. Vindas-Meléndez,
[Local h\*-polynomials for one-row Hermite normal form simplices](https://arxiv.org/abs/2309.01186v4),
study the local $h^\ast$-polynomials of one-row Hermite normal form
simplices. Other negative coefficients have been found for other polytopes:
the coefficient $-687323/79200$ of $t^2$ for a 13-dimensional
permutohedron in a
[public notebook](https://github.com/avstdi/Schubitope_Ehrhart_Positivity_Counterexample/tree/7bbbae374e3de2686e1938e3276d8fc14b60640f),
and a negative linear coefficient for the order polytope of the full face
poset of a 13-gon in an
[AI-assisted collection](https://github.com/ArtificialZeng/AI-Has-Taste/tree/f3ae144b74f238f22c2b84b5283cb14ce912fd33).
None of these concerns a base-r simplex.

## Source access

As of November 1, 2026, the result is new as far as we could check.

- A MathOverflow question,
  [Ehrhart positivity question associated to key polynomials](https://mathoverflow.net/questions/515853)
  (question 515853, posted October 8, 2026), could not be read in full.
  On November 1 its page read "This question was voluntarily removed by
  its author", and the Stack Exchange API returned no post with that
  number, so its answers and comments are no longer public; no web
  archive holds a copy. The
  [site's rules](https://mathoverflow.net/help/deleted-questions), as read
  on November 1, don't let an author delete a question that "has an answer
  with one or more upvotes", "has multiple answers" or "has an accepted
  answer", so at the time of removal it had at most one answer, without
  upvotes; we can't tell what it held earlier. Its title, and the text of the
  question as a search engine rendered it before deletion, concern
  key polynomials rather than base-r simplices.
- MathDB lists this exact problem twice,
  [337801](https://mathdb.com/p/337801) and
  [339011](https://mathdb.com/p/339011); on November 1, 2026 both read
  "No solutions have been posted yet."
- The [MinMaxArena problem list](https://minmaxarena.com/en/problems) was
  read on November 1, 2026: its 75 problems are geometric optimization
  problems (packings, coverings, Heilbronn configurations and similar),
  none about Ehrhart polynomials.

Lean and Mathlib provide the kernel and library infrastructure. Their
dependencies are obtained from the pinned upstream versions, with their
upstream licenses.
