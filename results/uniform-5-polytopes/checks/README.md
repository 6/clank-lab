# Checks and proof details

The proofs, the Lean formalization and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

All commands below run from the bundle root, the directory containing
[the main README](../README.md).

The theorem holds conditional on the cited 3-D and 4-D classifications, the correctness of the written reductions in Sections 2–5 (The reduction; The finite library and the known list; Case A; Case B), and the correctness of the certificate checkers.

[Schulte's 2017 Handbook chapter, §18.5](https://www.csun.edu/~ctoth/Handbook/chap18.pdf) records completeness only through dimension four. [Winter's 2021 dissertation, Appendix E.3, p. 167](https://martinwintermath.github.io/pdf/phd/thesis.pdf) states: “it is unknown whether there exist non-prismatic non-Wythoffian uniform polytopes in dimension five or above.” The contribution is completeness of the known list, with no new examples.

## Status

This is a computer-assisted proof, not expert-reviewed. The Lean project checks a conditional implication and selected geometric lemmas; the entire classification is not a completed Lean proof. The computational hypotheses and cited classifications remain assumptions, without a joint instance proved in Lean. The precise twelve computational hypotheses appear verbatim in the manuscript's appendix (from [data/core-hypotheses.txt](../data/core-hypotheses.txt)) and in [the Lean sources](../lean/README.md).

The written links not formalized in Lean are: the numerical library/model correspondence (Section 3); stage-1 enumeration and root coverage (Section 4.1); coverage of actual vertex figures by stage-2 signatures (Section 4.2); stage-3 encodings, identification and neighbor forcing, including the stuck-development refutation of the extra candidate (Sections 4.4–4.5); and the numerical B2, P1, partner-radius and W bounds used by the Case B structural argument (Section 5). Rooted determinism, congruence from discrete data and coset comparison are not formalized end to end for the concrete program encodings and candidate lists. Conditional formalized geometry does not establish those hypotheses for the supplied certificates. The extra candidate is the 8-vertex figure of circumradius √3/2 at polytope radius 1, described and excluded in the manuscript's “The one other vertex figure” subsection.

The automated checks described here have been run; no human expert review of the written reductions has taken place.

## How to check

Use Python 3.11 or later and Bash 4.4 or later with the dependencies in `checks/requirements.txt`. From the bundle root:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r checks/requirements.txt
PYTHON="$PWD/.venv/bin/python" bash checks/verify-public.sh full
```

Only full mode checks all computational claims used in the theorem; quick mode does not check the theorem. Neither mode verifies the written reductions automatically. Replace `full` by `quick` for a shorter non-proof check: it omits P=16 stages 2/3 and checks only a sample of W fans. P1's sampled tails are also non-proof checks; the all-parameter conclusion uses the written bounds and certified ranges.

Installation needs a package index; the replay itself needs no network, Git metadata or files outside the bundle other than installed tools and dependencies. The driver authenticates the scientific inputs and checkers, runs disposable copies and stops on any failed check. Certificate validation uses explicit errors and remains enabled under `python -O`; regression checks test corruptions under both `-O` and `-OO`.

The full check takes about half an hour. A successful full replay ends with:

```text
uniform-5-polytopes public full: PASS
```

Two stage-3 workers are used by default; set `S23_JOBS=1` for serial execution. Full mode checks every W fan, all 181 P=16 equivalence certificates (5,108 ordered options), and P=16 stages 2/3 with coverage checks. The P=6 quick control retains fixed 8- and 10-gon facets and has 136 classes rather than the literal cutoff's 129; the libraries coincide at P=10 and P=16.

The finite result is 563 classes, 629 signatures (628 known and one wholly refuted), zero OPEN cases and 890 matched construction names. The independent implementation has 657 raw realizations, including 28 additional mirror placements that it refutes. Construction names can be aliases and are not counts of distinct polytopes. The 628 polytopes include members of the infinite families.

## Proof inputs and independence

The 3-D classification gives the Platonic and 13 Archimedean solids, prisms and antiprisms; see Schulte §18.5 and [Grünbaum's account of vertex transitivity](https://doi.org/10.4171/EM/120). The 4-D input gives Wythoffians of A4, B4, D4, F4 and H4, the snub 24-cell, grand antiprism, polyhedral prisms and duoprisms; see Conway–Guy and Möller below. These classifications are not re-proved here.

For polygonal faces of at most 16 sides, finite enumeration covers every actual vertex neighborhood and excludes the one additional candidate. A face of at least 17 sides forces a product family. The radius cover has max Ω = 63.2195709614… because it includes closure roots that need not extend to any polytope; it is not the largest radius of a known polytope at the cutoff.

The implementations share some construction mathematics, inputs, model certificates and arithmetic libraries. The `check_u3` geometric/transcendental routines and `check_caseb` use mpmath intervals, exact arithmetic or outward-rounded binary64 intervals; both `independent-s1-b2` and `independent-s23` use Arb through python-flint and SymPy. Thus implementation independence does not imply arithmetic-library independence. Undecided cases stop or remain OPEN and cannot establish completeness.

In dimension six, a list of possible 5-D facets would not suffice: codimension-three faces become polyhedra, their metric/incidence data and the vertex-figure assembly grow, and Case B's argument does not classify the unbounded six-dimensional families. New structural reductions and certified parameter bounds are needed before a finite replay could settle that case.

## Credits

Möller's edge-neighborhood enumeration, forced-radius comparison and vertex-neighborhood completion are the direct methodological foundation:

- Conway and Guy, *Four-dimensional Archimedean polytopes*, 1965 colloquium, published 1967, pp. 38–39; Möller's [Hamburg dissertation](https://ediss.sub.uni-hamburg.de/handle/ediss/689) and [*4-dimensionale Archimedische Polytope*, Results in Mathematics 46 (2004), 271–360](https://doi.org/10.1007/BF03322887).
- Wythoff (1918), Coxeter's [*Wythoff's construction for uniform polytopes* (1935)](https://doi.org/10.1112/plms/s2-38.1.327), and Johnson's 1966 construction theory supply the known families. Johnson's thesis treats constructions in arbitrary dimension, including five; its discussion of known enumeration does not establish convex 5-D completeness. Johnson's unavailable 1991 manuscript is cited by Schulte for the 4-D list; no 5-D completeness claim is attributed to it here.
- Gosset, Elte and [Blind–Blind (1991)](https://doi.org/10.1007/BF02566640) treat the stricter regular-facet problem. Sopov (1970) and [Skilling (1975)](https://doi.org/10.1098/rsta.1975.0022) establish completeness for uniform polyhedra including nonconvex cases.
- [Bowers's polytera catalog](https://www.polytope.net/hedrondude/polytera.htm) and [Klitzing's catalog](https://bendwavy.org/klitzing/home.htm) document known examples and nomenclature. Bowers's search includes nonconvex objects and is not used as an exhaustive convex search. The input lists here are generated from construction recipes.

The verification design was developed with [Càllisto's honeycomb work](https://doi.org/10.5281/zenodo.22881686) as a known methodological precedent, including its division between Lean arguments and external finite certificate checks; none of its theorems or certificates is a premise here.

The manuscript gives the full bibliography and credits Lean, Mathlib, python-flint/Arb, SymPy, NumPy, SciPy and mpmath.

## Bundle and rebuilding

[paper/paper.pdf](../paper/paper.pdf) is the manuscript, with LaTeX source alongside it. `checks/` holds the checkers and their inputs; [data/README.md](../data/README.md) explains the certificates, manifests and how to retain regenerated states. [lean/README.md](../lean/README.md) gives the separate Lean build and axiom-audit commands. The Python replay does not run Lean.

Rebuild the PDF with Tectonic and the DejaVu Sans Mono font installed:

```bash
tectonic paper/paper.tex
```

Apache-2.0 (see the [repository's LICENSE](../../../LICENSE)), except the font material listed in [THIRD_PARTY.md](../THIRD_PARTY.md).
