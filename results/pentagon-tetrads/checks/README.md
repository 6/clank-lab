# Checking guide

This folder holds the programs the proof needs. The paper's Sections 3 and 4
reduce a holeless tetrad of congruent polygons to finitely many cases; the
programs here carry out that enumeration and check the certificates that
exclude every case.

## Commands

Python 3.12 or newer, from the result's folder:

```sh
python3 -m pip install -r checks/requirements.txt
python3 checks/check.py
```

This takes about three minutes on two cores and about 150 MB of memory. It
checks:

1. the boundary-map enumeration (`enumeration/maps.py`) reproduces the three
   maps in `data/maps-h0.jsonl`, and a separate enumeration of the primal
   maps (`enumeration/maps_primal.py`, sharing no code with it) also finds
   three;
2. the 116 cases in `data/closure-cases-n5.json` are exactly the
   length-feasible members of the angle-feasible cases in
   `data/angle-survivors-n5.jsonl`, decided by an exact rational linear
   program; they form the 22 relabeling classes in
   `data/closure-groups-n5.json`; every case has the explicit relabeling
   onto its class's closing member recorded in
   `data/closure-relabelings-n5.json`; and every class has a closing member
   (`enumeration/check_cover.py`). For all 116 cases, the angle formulas and
   the length-cone rays the relabelings compare are rederived exactly, the
   cones with the verifier's rational cone routine
   (`enumeration/all_cones.py`);
3. the verifier (`verifier/verifier.py`) accepts every certificate in
   `data/certificates/`, and both proofs of the class closed by an identity
   (`enumeration/group4.py`, `verifier/check_group4.py`) run;
4. the verifier rejects a certificate whose factorization constant has its
   sign flipped.

The exact angle screen behind `data/angle-survivors-n5.jsonl` is rerun by

```sh
python3 checks/check.py --full
```

which also confirms that no triangle or quadrilateral case is
angle-feasible. It takes about ten minutes for triangles and quadrilaterals and about five
CPU-hours for pentagons. `--full --part K/8`, for K = 0, …, 7, splits the
pentagon screen into eight parts; their survivors together must equal the
file.

## How the pieces fit

- `enumeration/` is the search: `maps.py` (plane duals of the boundary map),
  `placements.py` (corner placements), `angles.py`, `angles2.py` and
  `angles_exact.py` (the labeling search and the exact angle test),
  `exact_lp.py` and `exact_linear.py` (exact rational linear programming),
  `lengths.py` and `lcone.py` (length systems and cones), `groups.py`
  (relabeling classes), `check_cover.py` and `all_cones.py`.
- `verifier/` checks the certificates. It was written from a specification
  of the conditions (the paper's Sections 4 and 5) and the certificate
  format, without the search code, and imports nothing from `enumeration/`.
  It rederives each case's angle family, region and length cone from the
  case's map, placement, labels and reflex pattern, checks each
  factorization identity symbolically, and replays the cell subdivision with
  `mpmath`'s outward-rounded interval arithmetic (the certificates were
  produced with ball arithmetic from `python-flint`). It also checks the
  exclusion points inside a region that the certificates use.
- The certificate format: each line of `data/certificates/*.jsonl` is one
  case, with its map, placement, labels, reflex pattern, free angles,
  angle formulas, length-cone rays, and the certificate (the factorization
  of each closure and simplicity quantity, the subdivision tokens and the
  exclusion polygons). The paper's Lemma 7 describes the sign rules.

## Tests of the reduction

Two tests of the written reduction were run during the work and are not
repeated here, because they use drawings this folder does not redistribute.
Applied to hexagons without being given an example, the same programs found
holeless tetrads of four congruent hexagons, one with the angles of Scott
Kim's hexagon. Fed the drawn hexagon tetrad from the Wikipedia article and
four pentagon tetrads with a hole from Walter Trump's pages, the placement
and labeling search produced each drawing's actual placement and labeling,
and its side lengths passed the length conditions.

A separate implementation of the linear screens, written from a
specification without access to `enumeration/` and using exact polyhedra,
reproduced the counts of placements and of angle- and length-feasible cases
for every map, for triangles, quadrilaterals and pentagons.

## Further credits

- George Sicherman, [Polyform Tetrads](http://sicherman.net/tetrads/tetrads.html): a catalog of tetrads, including pentagon tetrads with holes.
- Karl Scherer, [Tetrads](https://doi.org/10.3840/08003126), Wolfram Demonstrations Project (2008).
- Scott Kim and Frank Rubin: earlier tetrads shown on [Trump's Question 15](https://www.trump.de/tetrads/question-15/question-15.htm).
- Trump's [Question 13](https://www.trump.de/tetrads/question-13/question-13.htm) states that four quadrilaterals cannot form a tetrad and asks for a short proof. The argument here covers only holeless tetrads, so it does not settle that statement.
- The tests of the reduction used the hexagon tetrad drawing in the Wikipedia article and pentagon tetrad drawings from Trump's [Question 14](https://www.trump.de/tetrads/question-14/question-14.htm).
