# Further credits

Elena Collina and Alessandro D'Andrea, *A graph-dynamical interpretation
of Kiselman's semigroups*, Journal of Algebraic Combinatorics 41 (2015),
1115–1132, [DOI](https://doi.org/10.1007/s10801-014-0569-7),
[2013 preprint](https://arxiv.org/abs/1311.3460v1) (titled *Sequential
dynamical systems on finite acyclic oriented graphs and Hecke-Kiselman
monoids*), [2014 revision](https://arxiv.org/abs/1311.3460v2): Proposition 2.4
shows that every update system satisfies the Hecke–Kiselman relations,
Theorem 6.3 implies the complete-graph case, and Conjecture 8.1 asks for all
finite acyclic graphs, in the form D(Γ) ≅ HK_Γ for the universal dynamics
monoid D(Γ) defined at the start of Section 8. The 2014 revision has the
journal numbering, except that the conjectures are Conjectures 1 and 2 of
Section 8; in the 2013 preprint they are in Section 9, and Proposition 2.4
and Theorem 6.3 are Proposition 2.3 and Theorem 7.2. The theorem here
answers Conjecture 8.1; Conjecture 8.2, that a particular pointed update
system on the complete graph is an initial object, is not part of the
statement.

Riccardo Aragona and Alessandro D'Andrea, *Normal form in Hecke-Kiselman
monoids associated with simple oriented graphs*,
[DOI](https://doi.org/10.12958/adm1571),
[preprint](https://arxiv.org/abs/1904.10745v1): Lemma 2.1 provides the
cancellation rules used in the proof, Remark 2.5 shows that the words they
cannot shorten, their normal forms, are the words the proof works with, and
Theorem 3.1 and Corollary 3.2 show that two normal forms of one element
differ by commutations of nonadjacent letters. The proof here shows
directly that two normal forms with the same final constructor state differ
in this way and does not use Theorem 3.1. In the journal version, Lemma 2.1,
Remark 2.5 and Theorem 3.1 are numbered Lemma 1, Remark 3 and Theorem 1. Alessandro D'Andrea's
[ANTIPODE 2 talk](https://hopfalgb.ulb.be/ANTIPODE2/Presentations/DAndrea.pdf),
September 12, 2022, slides 16 and 19, asks about reconstructing a word from
its update action. The two-letter trace reconstruction argument is the projection
lemma of Robert Cori and Dominique Perrin, *Automates et commutations
partielles*, RAIRO Informatique théorique 19 (1985), 21–32,
[DOI](https://doi.org/10.1051/ita/1985190100211), and Christine Duboc,
*On some equations in free partially commutative monoids*, Theoretical
Computer Science 46 (1986), 159–174,
[DOI](https://doi.org/10.1016/0304-3975(86)90028-9); it is proved
directly in `lean/CD13/Trace.lean`.

Christer O. Kiselman, *A semigroup of operators in convexity theory*,
Transactions of the American Mathematical Society 354 (2002), 2035–2053,
[DOI](https://doi.org/10.1090/S0002-9947-02-02915-X), is the origin of
Kiselman's semigroups. Olexandr Ganyushkin and Volodymyr Mazorchuk, *On
Kiselman quotients of 0-Hecke monoids*, International Electronic Journal of
Algebra 10 (2011), 174–191, [preprint](https://arxiv.org/abs/1006.0316v3),
introduced Hecke–Kiselman monoids (Section 5.1); Example 12 identifies
Kiselman's semigroup as the monoid of a complete acyclic graph, and
Proposition 13 identifies the opposite of a Hecke–Kiselman monoid with the
monoid of the opposite graph. Ganna Kudryavtseva and Volodymyr Mazorchuk,
*On Kiselman's semigroup*, Yokohama Mathematical Journal 55 (2009), 21–46,
[preprint](https://arxiv.org/abs/math/0511374v1), Theorem 34, prove that
Kiselman's semigroup has a faithful representation by matrices with
nonnegative integer entries; in their construction (Section 11.1) each
generator differs from the identity matrix in a single column.

Love Forsberg, *Effective representations of Hecke-Kiselman monoids of
type Aₙ*, [version 4](https://arxiv.org/abs/1205.0676v4), February 15, 2017,
proves that representations "constructed by Ganyushkin and Mazorchuk" are
effective (faithful): Corollary 4.6 for the graphs of type Aₙ in every
orientation, Theorem 5.1 for weighted representations of the graphs Zₙ with
arrows a → vᵢ → b, and Theorem 4.5 for graphs glued from such pieces at a
common source or sink. Passing to the opposite graph (Ganyushkin–Mazorchuk,
Proposition 13), transposing and reducing modulo a suitable prime turns
these into faithful local systems, so Conjecture 8.1 was already settled
for these graphs. Forsberg's introduction notes that the type-Aₙ monoids
"naturally appear as monoids of projection functors": Anna-Louise Grensing,
*Monoid algebras of projection functors*, Journal of Algebra 369 (2012),
16–41, [DOI](https://doi.org/10.1016/j.jalgebra.2012.07.002), Theorem 3.9,
gives defining relations for these monoids on admissible tree quivers, and
Grensing and Mazorchuk, *Categorification of the Catalan monoid*, Semigroup
Forum 89 (2014), 155–168, [DOI](https://doi.org/10.1007/s00233-013-9510-y),
and *Finitary 2-categories associated with dual projection functors*,
Communications in Contemporary Mathematics 19 (2017), 1650016,
[DOI](https://doi.org/10.1142/S0219199716500164), develop these functor
realizations; the second shows for admissible tree quivers that "the monoid
generated by dual projection functors is the Hecke–Kiselman monoid of the
underlying quiver." None of these covers arbitrary acyclic graphs.

Alessandro D'Andrea and Salvatore Stella, *Cardinalities of Kiselman monoids
and their parity asymptotics*, [version 1](https://arxiv.org/abs/2610.14331v1),
posted October 9, 2026: Propositions 1.1–1.2 and Theorem 2.1 use a suffix
order and a poset transform to obtain a counting recurrence for the
complete-graph monoids. Theorem 3.2 separates the even and odd asymptotic
constants. These results concern cardinalities of that family; they do
not prove the arbitrary-DAG local-action theorem. The present proof does
not use their counting theorem.

Zhen Feng Jin, Yan Feng Luo and Wen Ting Zhang, *Combinatorics and faithful
representations of cycle monoids*, [DOI](https://doi.org/10.1007/s00233-026-10687-7),
October 20, 2026: the abstract describes remaining reduced forms and
“faithful representations of Cyc_n with and without involution.” Its
stated graph family is directed cycles of length at least three, outside
this theorem. Its full text is subscription-only; see the list of sources
not read in full below.

Luka Andrenšek, *Homomorphisms of Hecke-Kiselman Monoids Associated to Simple Oriented Graphs*,
[version 3](https://arxiv.org/abs/2604.15497v3), Theorems 4.5 and 5.4,
describes homomorphisms and endomorphism monoids through admissible Boolean
matrices. These statements concern general homomorphisms, not the
prescribed coordinate-local dynamics used here.

Luis David Garcia, Abdul Salam Jarrah and Reinhard Laubenbacher,
*Sequential dynamical systems over words*, Applied Mathematics and
Computation 174 (2006), 500–510, [DOI](https://doi.org/10.1016/j.amc.2005.04.101)
(not Reidys's paper of the same title, below): in Definition 2.1 the
coordinate of a vertex may depend on every coordinate within distance d of
it, its own included, and Theorem 4.9 bounds the number of distinct systems
over the words of a given length by counts of acyclic orientations. Its
local maps may read their own state, so the relations used here need not
hold.

Tuğçe Ulutaş and Mehmet E. Köroğlu, *Counting complexity of period-3 orbits
in sequential dynamical systems and their relationship to error-correcting
codes over ternary fields*, Symmetry 18 (2026), 1658,
[DOI](https://doi.org/10.3390/sym18101658), open access: the abstract says
that the authors "recently showed that the maximum number of period-3 orbits
of an SDS on the complete graph equals the maximum size of a ternary code
with a minimum Hamming distance of at least four," extending Colin Defant's
period-2 correspondence with binary codes. That earlier result is Ulutaş and
Köroğlu, *Period-3 orbits of sequential dynamical systems and their
relationship to error-correcting codes over finite fields*, Graphs and
Combinatorics 42 (2026), 14, [DOI](https://doi.org/10.1007/s00373-025-03008-2),
and Defant's is *Binary codes and period-2 orbits of sequential dynamical
systems*, Discrete Mathematics and Theoretical Computer Science 19(3) (2017),
10, [DOI](https://doi.org/10.23638/DMTCS-19-3-10). The Symmetry paper studies
the computational cost of that correspondence for systems on complete graphs
with one common local function, which reads the vertex's own state.

Lean and Mathlib provide the kernel and library infrastructure. Their
dependencies are obtained from the pinned upstream versions, with their
upstream licenses.

## Sources not read in full

None of these sources could be read in full. Each one is listed here with the reason why,
to our knowledge, it does not contain the theorem. The findings come from legally available material:
abstracts, tables of contents, publishers' first-page previews, reference lists
and later papers. Nobody was contacted, and nothing was bought or requested.

- Elena Collina, *Dynamical systems on graphs and Hecke-Kiselman monoids*,
  PhD thesis, Sapienza Università di Roma, 2014. D'Andrea's publication page
  links a copy. On November 1, 2026 the university's server did not respond,
  and web archives hold no copy. The acknowledgments of the journal version of
  Collina and D'Andrea's paper say that its results are part of the thesis. The accepted
  version still poses Conjecture 8.1. Its evidence is a computer check
  of all graphs with at most four vertices and most graphs with five. D'Andrea's 2022
  lecture, slide 21, says that a redefined linking operation "works
  (experimentally)" on all graphs with at most eight vertices. No proof is mentioned.
- Jin, Luo and Zhang's cycle-monoid paper (above) and Yan Feng Luo, Zhen Feng Jin and
  Wen Ting Zhang, *Finite Gröbner–Shirshov bases and faithful representations
  for Catalan monoids*, Communications in Algebra 54 (2026), 185–195,
  [DOI](https://doi.org/10.1080/00927872.2025.2522155). Both are subscription-only.
  According to their abstracts, each treats one family of graphs: directed cycles, which
  lie outside this theorem, and oriented paths, which Forsberg already covers. The
  Catalan representation uses Boolean upper triangular matrices, and Mikhail Volkov's
  [arXiv:2510.05045v2](https://arxiv.org/abs/2510.05045v2) identifies it as a
  rediscovery of an earlier representation. Neither reference list includes Collina
  and D'Andrea's paper.
- Christopher Barrett, Henning Mortveit and Christian Reidys, *Elements of a theory of
  (computer) simulation* I–III, Applied Mathematics and Computation 98 (1999),
  107 (2000) and 122 (2001),
  [I](https://doi.org/10.1016/S0096-3003(97)10166-7),
  [II](https://doi.org/10.1016/S0096-3003(98)10114-5),
  [III](https://doi.org/10.1016/S0096-3003(00)00042-4);
  Mortveit and Reidys, *Discrete, sequential dynamical systems*, Discrete
  Mathematics 226 (2001), 281–295,
  [DOI](https://doi.org/10.1016/S0012-365X(00)00115-1);
  Reidys, *Sequential dynamical systems over words*, Annals of Combinatorics 10
  (2006), 481–498, [DOI](https://doi.org/10.1007/s00026-006-0301-y);
  Mortveit and Reidys, *An Introduction to Sequential Dynamical Systems*,
  Springer 2008, [DOI](https://doi.org/10.1007/978-0-387-49879-9), Chapter 7
  on words. In all of them, local maps act on an undirected graph and may read the
  updated vertex's own state, so idempotence and the Hecke–Kiselman relations
  for arrows do not hold in general. These works study the phase spaces of given
  systems and when two update orders give the same system, and they count those
  classes through acyclic orientations. They do not determine the universal kernel
  over all systems with outgoing-only updates on a directed acyclic graph.
  Collina and D'Andrea cite I–III and the book, and pose Conjecture 8.1 after them.
