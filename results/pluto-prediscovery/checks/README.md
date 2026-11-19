# Checks

## What the scripts do

- `rerun.py WORK` is the entry point. It downloads every input from public services into `WORK`, repeats the measurements and controls listed below as "rerun", writes `WORK/results.json` and compares 44 of its numbers with [../data/expected.json](../data/expected.json), which gives each recorded value and its tolerance. It exits nonzero if any falls outside; other numbers in `results.json` are not checked. The random-position tests use fixed seeds, so they reproduce exactly. It also saves the inputs of the figure and the blinded sheet, which `figure.py` draws.
- `plates.py` is Method B: plate solution, matched filter, centroid, photometry, the replay of the measurement at shifted positions (`replay`), comparably faint stars and injections.
- `clock.py` dates an exposure from the trail of a known asteroid.
- `census.py WORK` lists the public plates covering Pluto's track from 1880 to June 1909 and writes `WORK/census.json` and `WORK/census-exposures.csv` (released as [../data/census-exposures.csv](../data/census-exposures.csv)).
- `figure.py WORK OUT.svg` draws the figure from the stamps `rerun.py` saves; `figure.py WORK OUT.pdf --blind KEY.json` draws the blinded sheet and writes its key.

Versions are pinned in `requirements.txt`; `figure.py` also needs matplotlib. The service calls retry when Harvard's API asks clients to slow down.

## Inputs

| Plate | Archive identifier | Exposure (UT), as used | Source of the time |
| --- | --- | --- | --- |
| MA 731 | DASCH DR7 plate `ma00731`, full-resolution mosaic | 1908-12-21 00:21:55 to 01:34:50 | trail of (179) Klytaemnestra |
| B2247a | HDAP `Bruceplatten/FITS/B2247a.fits` | 1909-02-20 18:50:10 to 21:50:12 | archive, checked by (417) Suevia |
| B2248b | HDAP `Bruceplatten/FITS/B2248b.fits` | 1909-02-20 18:50:22 to 21:50:24 | archive, checked by (417) Suevia |
| B3383a | HDAP `Bruceplatten/FITS/B3383a.fits` | 1914-01-23 17:38:05 to 20:18:06 | archive (accepted 1914 image) |
| B4816a | HDAP `Bruceplatten/FITS/B4816a.fits` | 1923-12-29, 3 hours | fixed-position control |

The Heidelberg scans are read as cut-outs through the GAVO SODA service, 0.7° around the target. Pluto's positions are JPL Horizons topocentric astrometric ICRF positions for Taunton, Massachusetts, where MA 731 was taken at Joel Metcalf's observatory (71.0903° W, 41.8997° N, as the DASCH plate record lists it) and for the Königstuhl (code 024).

## Clock corrections

Harvard's logbook start and stop readings for MA 731 were not available to us. The storage envelope gives "Dec. 20, 1908" (the local evening), "60m" and quality 4. DASCH's data guide says that Harvard exposure times "were generally recorded in Local Sidereal Time", and that the reported time is "the average of the start and stop times". The archive midpoint is 06:46:36.5 UT with a 60-minute exposure.

Trail fits, 1σ errors (the fit's covariance, inflated by 1 + 2 Σρ for the correlation of neighboring minutes). The errors hold only if the trail model, a band with blurred start and stop edges, is right; they are not bounds on the true times.

| Plate | Asteroid | Opening (UT) | Closing (UT) | Midpoint (UT) | Midpoint minus archive | Source |
| --- | --- | --- | --- | --- | ---: | --- |
| MA 731 | (179) Klytaemnestra | 00:21.9 ± 1.2 | 01:34.8 ± 0.5 | 00:58.4 ± 0.7 | −348.2 min | rerun |
| MA 731 | (179), separate code | | | 00:58.5 | −348.1 min | recorded |
| MA 731 | (1436), weak trail | | | 01:01.5 | −345.1 min | recorded |
| MA 731 | (2891), weak trail | | | 01:04.2 | −342.4 min | recorded |
| MA 731 | combined measurements along eight fainter asteroids' tracks | | | 01:02.5 | −344.1 min | recorded |
| B2247a | (417) Suevia | 18:48 ± 5 | 21:52 ± 5 | 20:20 ± 3.5 | 0.0 min | rerun |
| B2248b | (417) Suevia | 18:31 ± 8 | 21:57 ± 8 | 20:14 ± 5.2 | −6.7 min | rerun |

Of the eight fainter asteroids, 4 of the 7 testable on MA 731 (Salonta, McGetchin, Barsig, Samantha) show excess signal in the corrected window (p ≤ 0.004), and none of the 5 testable in the archive window; on MA 733, 4 of 8 do (McGetchin, Andrea Doria, Samantha, Urabe). An earlier version reported "9 of 15" pooled over both plates; the recorded tests give 8 of 15. The (179) fit reads only a square of ±700 pixels (±0.2°) around the asteroid's track. That square is 5.4° from Pluto, and on the Heidelberg plates the (417) square is 2.3° from Pluto. `rerun.py` records both distances, so no pixel near Pluto enters a clock. The clock was fitted, and checked against the other asteroids, before Pluto's position at the corrected time was measured.

In arcseconds along Pluto's track: on MA 731 the prediction moves 0.049″ per minute. The fit's 0.7-minute error moves it by 0.03″, and the 6-minute spread between asteroids by 0.3″. The fitted exposure lasts 73 minutes against the envelope's 60; a 60-minute exposure that began at the fitted opening or ended at the fitted closing would move the midpoint by 6.5 minutes, or 0.32″. At Heidelberg it moves 0.017″ per minute, so 20 minutes is 0.35″.

A logged sidereal start time (a clock set by the stars) read as local mean time (a clock set by the Sun) reproduces the archive midpoint to 2 minutes, a hypothesis not tested against the logbook. On the Heidelberg plates Method B's fits to the trails of (168) Sibylla and (179) Klytaemnestra gave no clean fit: their fitted durations, 3.7 to 7.2 hours, exceed the 3-hour exposure. `rerun.py` reports the (168) fits but does not use them. Method B adopts the archive midpoints there (20:20:11 and 20:20:23 UT). Method A fitted (168) Sibylla and (417) Suevia on both plates and (179) Klytaemnestra on B2248b, and adopts per-plate medians of 20:17:45 and 20:07:21 UT; the two choices move Pluto's prediction by at most 0.22″.

## Method B (rerun)

For each plate: a cut-out of about 70′ around the prediction; a cubic plate solution against Gaia DR3 propagated to the plate epoch; a Gaussian matched filter whose width is fitted on APASS stars of B 14–16; S/N against the robust scatter of the filtered scan at random points; a free centroid within 8 pixels; B from an APASS calibration quadratic in the logarithm of the peak, with a color term, evaluated at B − V = 0.78 and restricted to the calibration's monotonic branch. The same code and parameters are used on every plate. The restriction to the monotonic branch was added when the calibration on B2247a turned over near its faint end; it affects only the expected S/N and the brightness of injected sources, not any measured position, S/N or magnitude.

## Method A (recorded, not rerun)

Method A was written separately. On MA 731 it fits a local plane, cataloged neighbors and a profile trailed along Pluto's motion, with the profile and response fitted on stars away from the target and the target pixels masked until its rules were frozen. Its rules: amplitude above the 99th percentile of 200 matched translated tracks, centroid within 6″, B within 0.45 mag of the prediction. On the Heidelberg plates a second implementation, written without sight of the other measurements, uses the archive's plate solution with a local affine correction, empirical profiles and Gaia synthetic B magnitudes, under the same rules. Its values are in Table 2 of the paper. Its MA 731 center is RA 85.893481°, Dec +16.016531°; its Heidelberg centers, reconstructed from its recorded offsets, are 84.961402°, +16.133058° (B2247a) and 84.961295°, +16.133450° (B2248b). Against Method B's predictions these are 0.22″, 1.68″ and 0.87″ off; against its own adopted times, 0.24″, 1.68″ and 1.06″. The two methods' centers differ by 0.9″ on MA 731 and by 1.4″ and 2.1″ on the Heidelberg plates. Method A finds the images 0.07 to 0.3 mag brighter. Its depth (faintest tested B with at least 80% of 200 inserted images recovered) is at least 17.00 on MA 731 and at least 17.70 on B2247a, where the faintest grid point still passed, and 17.00 on B2248b. Its brightness rule is B within 0.45 mag of the prediction; on MA 731 its 15.96 is 0.37 mag brighter than 16.33.

## Controls

Rerun by `rerun.py`:

- The archive-time position on MA 731: S/N −0.2.
- Injected trailed sources at Pluto's B ± 0.5 mag on each plate (recovery at Pluto's B: 99% at S/N ≥ 3 on MA 731).
- The nearest Gaia DR3 star to each image: 11.4″ (G 18.86) on MA 731, 25.6″ (G < 19.5) on B2247a.
- IMCCE SkyBoT: Pluto alone within 0.04° of the December image and of the February position.
- The joint test (`plates.replay`): 300,000 random sky offsets (seed 1909), each applied to all three predictions; 230,352 lie more than 60″ from the real one and inside all three cut-outs. At each moved prediction the measurement itself is replayed: the brightest filtered pixel within 8 pixels, its windowed centroid, the S/N there, the centroid's distance from the moved prediction and a Gaia check within 3″ of the centroid. The thresholds are the replay's values at the real predictions (S/N 6.25, 4.84, 5.84; distances 0.65″, 0.31″, 1.90″). Results:
  - As close and as strong as observed on all three plates: 0 of 230,352 (95% upper bound 1.3 × 10⁻⁵); also 0 counting only centroids with no Gaia star within 3″.
  - On single plates: 29 on MA 731 (1.3 × 10⁻⁴), 6 on B2247a (2.6 × 10⁻⁵), 223 on B2248b (9.7 × 10⁻⁴); 1 on both February plates, 0 on both counting only centroids with no Gaia star within 3″; 2 on MA 731 alone with no Gaia star within 3″.
  - The search's own, looser acceptance rule, S/N ≥ 4 at the centroid wherever it falls: 8,581 offsets match all three plates, and in 3,360 (1.5%) the centroid has no Gaia star within 3″ on any plate. An earlier version of this test, which counted entries of a 9-pixel local-maximum list within a sky radius and used their S/N at the integer peak, reported 129 and 0; the exact replay corrects it. Most of these matches arise near bright stars just outside the window: the brightest filtered pixel lies on the star's outer profile and the centroid moves toward the star, a median 11–12″ from the moved prediction, yet stays more than 3″ from it. On single plates 12–15% of offsets pass this rule with no Gaia star within 3″; over half of those have a Gaia star of G < 16 within 20″.
  - Requiring, after seeing these counts, the centroid also to lie within 3″ of the moved prediction: 0 of 230,352. This cut was chosen after seeing the data.
  - Crowding matched: offsets where every plate's count of Gaia stars (G < 19.5) within 60″ is within 20% (at least 2) of the count at Pluto (25, 18 and 18). As close and as strong as observed on all three: 0 of 39,786 (bound 7.5 × 10⁻⁵); the loose rule with no Gaia star within 3″: 722.
  - These rates are per trial and conditional on the three plates and times reported, their observed thresholds and these definitions. They leave out the other plates and times examined (MA 733, and the archive times of MA 731 and MA 733) and how these three were selected, and they do not model plate defects.
- Comparably faint stars, measured exactly as the images: isolated APASS stars within 0.5 mag of Pluto's B and 1,500 pixels of the prediction, with the Gaia position as truth. They are drawn from the same APASS sample that fits the calibration, so the brightness comparison is internal. Median centroid miss: 1.24″ on MA 731 (193 stars), 1.03″ on B2247a (146) and 1.23″ on B2248b (124). The images' misses fall at the 20th, 6th and 73rd percentiles. Robust spread of calibrated minus catalog B: 0.21, 0.24 and 0.17 mag.
- The blinded sheet [../data/blind.pdf](../data/blind.pdf) shows, for each plate, the image and 11 controls in shuffled order. Each control is centered so that an uncataloged peak with S/N within 1 of the image's sits where the image sits relative to its prediction. The controls are drawn more than 2′ from the prediction and at least 200 pixels inside the cut-out, from 31, 57 and 48 such peaks. The key is in [../data/blind-key.json](../data/blind-key.json); look at the sheet first.
- Pluto's motion from December to February, 61 days: the December offset repeats in February to 0.84″ and 1.82″. Given the position match on each plate this is not a separate test, and the simultaneous pair adds no motion; it does show that no fixed object explains both epochs.
- Positive control: Method B finds Pluto on the accepted 1914 plate B3383a at S/N 6.8, 1.55″ from the prediction, B 16.45.
- Fixed position: on the 1923 plate B4816a the February position gives S/N −0.7, and injected B 16.4 sources are all recovered at S/N ≥ 3.

`figure.py` (run separately) draws the figure and the blinded sheet from the saved inputs.

Recorded, not rerun:

- Catalogs at the two positions. Gaia DR3, any magnitude: nearest 11.4″ (G 18.86) from the December image and 17.1″ (G 19.84) from the February position. 2MASS (VizieR II/246) and USNO-B1.0 (I/284) list the same star 11.3″ and 11.2″ from the December image and nothing closer within 15″; UCAC4 (I/322A) lists nothing within 15″ and VSX (B/vsx) nothing within 60″ of either position; at the February position none of the four lists anything. Pan-STARRS DR2 (MAST API): the nearest stack object is 8.7″ from the December image (r 22.1) and 14.3″ from the February position; within 15″ the mean catalog has only single-detection objects, including one z-band detection 0.9″ from the December image at an epoch when SkyBoT lists no known asteroid there, and nothing closer than 3.4″ at the February position. No completeness is claimed for these queries.
- Other DASCH plates at the same sky positions, by Method B: 24 sensitive of 87 at the December position (1909–1949, S/N −1.7 to +0.8) and 43 sensitive of 89 at the February position (1899–1953, −2.1 to +2.1). MA 733, the next night, is less deep and shows only a 2.6–3.0σ excess 3–4″ from its prediction.
- Known asteroids at the December image, at nominal predicted positions. JPL's small-body identification service finds no comet, Centaur, trans-Neptunian or other small-class body, but cannot search the near-Earth, main-belt or Trojan classes for 1908. For those, the nominal JPL Small-Body Database orbits (osculating elements at JD 2461200.5) of every asteroid that could reach V ≤ 18 there (all near-Earth objects and Mars-crossers with H > 17.3, every asteroid with H ≤ 17.3) were integrated back to 1908: REBOUND 4.6.0 with WHFast (4-day step, Sun and eight planets from Horizons) for the 143,321 others, and ASSIST 1.2.3 with JPL's DE440 and the sb441-n16 asteroid perturbers for the 38,826 near-Earth objects. Nothing besides Pluto falls within 6.3′. Checked against Horizons in random samples of 20 per class, main-belt positions agree to a median of 2.4″, but 15 of 63 sampled near-Earth objects and 1 of 20 Mars-crossers differ by more than 1°, so those classes are not reliably tested. The 32 other bodies whose nominal positions fall within 1° would have trailed 38–60″ during the exposure. At the February position the only test is SkyBoT (nothing besides Pluto within 10′). Neither test covers asteroids unknown today.
- Image shape on MA 731: width, ellipticity and concentration at the 40th, 54th and 17th percentiles of 48 nearby stars of the same S/N. Bright stars show no displaced secondary image. Still possible: a star-like grain cluster or flaw on MA 731, coincident separate defects on the two Heidelberg plates, and a scanning artifact common to both.

## Census (`census.py`)

Pluto's track from Horizons, daily, with B = V + 0.87 (the redder assumed color). Pluto's track is sampled every 30 days; a sample is skipped when Pluto is within 30° of the Sun on the sample date. At each kept sample DASCH is queried for exposures with midpoints within 15 days that cover Pluto's position at the sample date, whatever the elongation on their own dates; exposures only in the windows of skipped samples are not queried. Each returned exposure is placed against Pluto's position on its own date: "inside" when DASCH's edge distance at the sample point exceeds Pluto's distance from that point, "edge" (unresolved) when it is equal or smaller, "unknown" when DASCH gives no edge distance. A plate that covers Pluto on its date but not the sample point is missed. A row is one plate solution's exposure; an exposure returned by several samples is kept once with its best label, and merging the rows of different solutions of the same exposure leaves every count unchanged (`census.json`, `merged_solutions`). The depth margin is DASCH's limiting magnitude (APASS, else ATLAS) minus Pluto's B, both unrounded (B is rounded only in printed and exported copies); a missing limit is tested before the comparison, and a margin of zero or more passes. No margin lies within 0.17 mag of zero. [../data/census-exposures.csv](../data/census-exposures.csv) lists all 1,906 DASCH exposures counted (1,746 inside and 11 at the edge before December 1908, 149 inside after), one row per exposure: plate, date (UTC), series, plate solution, coverage, limit, Pluto's B, margin (to 0.001 mag) and verdict (passes, short, or not tested with the reason). It is regenerated by `census.py`; SHA-256 `1d2dda36fd391404ac68e959cc6cbec3b8637bc6c083087490be38fa8d9d3e8e`. With the combined 1933–34 color, B − V = 0.78, every margin rises by 0.09 mag; no further exposure passes (`census.json`, `margin_ge_0_with_BV_0.78`). Heidelberg plates centered at RA 30°–110°, Dec −10° to +35° are placed through their archived plate solutions; the archive gives no limiting magnitude. APPLAUSE DR4 exposures with a recorded time and pointing are listed with their distance from Pluto.

- December 1908 to June 1909: 149 DASCH exposures inside, 0 edge, 0 unknown; 56 have a limit. Only MA 731 passes (+0.47); MA 733 is 0.18 mag short. Heidelberg has only B2247a and B2248b, which recover injected images about 0.5 mag fainter than Pluto.
- Before December 1908: 1,746 DASCH exposures inside (1886 to 1908), 11 edge, 0 unknown; 525 of the 1,746 have a limit, and none passes. The best, I 31266 (December 14, 1903, 63 minutes), has a limit 0.76 mag brighter than Pluto's B and was not measured. Eight solved deep-series plates without a DASCH limit fail a depth screen on their scans. 70 plates of the deep B, C and I series of 30 minutes or more have no plate solution and were not screened. The remaining exposures without a limit are unassessed.
- Heidelberg before December 1908: ten plates from Wolf's double astrograph (G1120, G1123–G1125 of 1896; G2391–G2393 and G2420–G2422 of 1901), which did not reliably recover faint comparison stars near Pluto's position, and the Bruce plate B342a (1901), where Pluto lies 75 pixels from the scan edge and the cut-out could not be registered.
- APPLAUSE: 34 exposures before mid-1909, all from Potsdam (1893–1902); the nearest nominal pointing is 22.9° from Pluto.

## Plates without public scans

- We found no public scan of the 1903 Franklin-Adams plate. For the Yerkes plates of 1909 we located no published measured position and no full calibrated scan; a marked reproduction of the November 11, 1909 plate accompanies the 2015 Air & Space account of W. Osborn and F. Mills's inspection.
- The Harvard MB duplicate plates of December 20 and 21, 1908, noted on the storage envelopes, were never scanned and would be too shallow.

## Further credits

- E. C. Bower, "On the orbit and mass of Pluto with an ephemeris for 1931–1932", Lick Observatory Bulletin 15 (1931), for the list of prediscovery images and Max Wolf's measures of the 1914 Heidelberg pair, exposed by F. Kaiser.
- H. Shapley and D. Johnstone, Harvard College Observatory Bulletins 886 and 887 (1932), for the Harvard plate MC 6858: Arville D. Walker found the image, Constance D. Boyd measured it and E. C. Bower supplied the ephemeris and derived its position.
- W. J. Wild, G. Buchwald, M. J. DiMario and E. M. Standish, DPS abstract 30, 55.14 (1998), on the Yerkes plates; W. Osborn and F. Mills's re-examination, reported by T. Reichhardt in Air & Space Magazine (July 15, 2015).
- J. Grindlay et al. (2012) for DASCH; S. Laycock et al. (2010) and R. J. Simcoe et al. (2006) for its photometry, astrometry and scanner; P. K. G. Williams (2025) for DASCH Data Release 7.
- J. D. Giorgini et al. (1996) for JPL Horizons, with M. Brozović and R. A. Jacobson (2024) for the PLU060 orbit solution and R. S. Park et al. (2021) for DE440 and DE441; the JPL Small-Body Database.
- H. Rein and S.-F. Liu (2012) for REBOUND, H. Rein and D. Tamayo (2015) for WHFast, and M. J. Holman et al. (2023) for ASSIST.
- J. Berthier et al. (2006) for SkyBoT; the Gaia Collaboration (2023) for Gaia DR3 and P. Montegriffo et al. (2023) for its synthetic photometry; A. A. Henden et al. (2016) for APASS DR9; K. C. Chambers et al. (2016) and H. A. Flewelling et al. (2020) for Pan-STARRS DR2; M. F. Skrutskie et al. (2006) for 2MASS; N. Zacharias et al. (2013) for UCAC4 (data doi:10.26131/IRSA17); D. G. Monet et al. (2003) for USNO-B1.0; C. L. Watson et al. (2006) for VSX.
- H. Enke et al. (2024) and APPLAUSE Data Release 4 (doi:10.17876/plate/dr.4). Funding for APPLAUSE has been provided by DFG (German Research Foundation, Grant), Leibniz Institute for Astrophysics Potsdam (AIP), Dr. Remeis Sternwarte Bamberg (University Nuernberg/Erlangen), the Hamburger Sternwarte (University of Hamburg) and Tartu Observatory. Plate material also has been made available from Thüringer Landessternwarte Tautenburg, and from the archives of the Vatican Observatory.
- Pluto's B uses B − V = 0.78 ± 0.04 for 1933–34 (B. E. Schaefer, M. W. Buie and L. T. Smith 2008) and, as a redder assumed case, Pluto's resolved 0.87 (M. W. Buie, D. J. Tholen and L. H. Wasserman 1997; M. W. Buie et al. 2006, Table 4); Horizons' V includes Charon.
- Astropy, NumPy, SciPy, astroquery and Requests.
