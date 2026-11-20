# Recorded analyses

From the bundle root, install the pinned Python dependencies and run any of the steps below. Use an absolute or relative work directory outside the bundle. The runner uses Bash, curl, GNU time and GNU timeout. The orbit validation was run on Python 3.12. REBOUND and ASSIST may require a C compiler. These steps query public services and can take longer than the 62-value check in [checks/README.md](../checks/README.md).

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r recorded/requirements.txt
recorded/run.sh WORK all
```

Each step writes JSON named by plate or keyed by plate, along with cached inputs and supporting files under WORK. Each timed command saves a resource receipt under `WORK/receipts` and has a nine-minute limit. Use `PYTHON` to select a different interpreter. Start with an empty WORK for a fresh download. Reuse it to retain cached inputs. Live archive catalogs, orbital elements, and responses can change. Reference JSON files contain the figures from the original analysis at their available precision, and input hashes distinguish identical inputs from a fresh analysis with changed inputs. The time and memory estimates below are per single process unless marked as totals. Network waits are part of elapsed time.

## Method A, December

```sh
recorded/run.sh WORK methodA-december
```

Uses the [DASCH DR7 plate and cutout service](https://api.starglass.cfa.harvard.edu/public/), solution 0 of `mc06858`, `ma00731` and `ma00733`, the same-series Gaia DR3 and APASS/ATLAS query fields, [JPL Horizons](https://ssd.jpl.nasa.gov/horizons/) at Taunton, and [DE421](https://ssd.jpl.nasa.gov/ftp/eph/planets/bsp/de421.bsp). The two 1914 Heidelberg comparisons use `B3383a` and `B3384b` from the [GAVO Heidelberg collection](https://dc.g-vo.org/lswscans/res/positions/q/info). The original input SHA-256 values are in [archive-clock pair](../data/recorded/pair.json), [corrected pair](../data/recorded/corrected-pair.json), [historical control](../data/recorded/historical.json), [asteroid clocks](../data/recorded/plate-clocks.json), [diagnostics](../data/recorded/december-diagnostics.json) and [Heidelberg controls](../data/recorded/heidelberg-controls.json).

Outputs under `WORK/methodA-december` include the archived and corrected pair, the MC 6858 control, the 179/1436/2891 timing JSON for each MA plate, diagnostics, native-pixel comparisons, external catalog and geometry checks, 14 translated fields and the 1914 controls. Table 1 of the paper gives MA 731's Method A 1043/243 amplitude and threshold, B 15.96 and ≥80% amplitude recovery through B 17.0. The archive-clock experiments fail the two triggers. The corrected pair crosses their triggers, while the reciprocal fixed-site measurements stay below threshold. Allow 10–30 minutes overall and up to 2 GiB, depending on archive response times.

## Method A, February

```sh
recorded/run.sh WORK methodA-february
```

Uses GAVO HDAP scans `B2247a`, `B2248b`, `B3383a` and `B4816a`, with the `lsw.plates` `pub_did` values in the query result. Gaia DR3 and its synthetic Johnson photometry come from [ESA TAP](https://gea.esac.esa.int/tap-server/tap/sync). JPL Horizons observer 024 gives tracks for Pluto and asteroids 168, 179 and 417. The supplementary checks query [SkyBoT](https://ssp.imcce.fr/webservices/skybot/api/conesearch.php) and [MAST Pan-STARRS DR2](https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2/mean.html). [Input SHA-256 manifest](../data/recorded/heidelberg1909-inputs.sha256)

Outputs under `WORK/methodA-february` include the plate clocks, per-plate open JSON, control-only JSON and the pair's joint counts. The paper gives midpoints 20:17:45 and 20:07:21 UT, amplitudes/thresholds 12,015/2,439 and 9,371/2,818, B 16.41 and 16.28, and ≥80% amplitude recovery through B 17.70 and 17.00. At B 16.4 the individual counts are 200/200 and 199/200. B4816a scores −492 with a 1,293 trigger. [Per-plate reference values](../data/recorded/methodA-february.json)

Allow approximately 5–15 minutes overall and 2 GiB.

## Method B, MA 733

```sh
recorded/run.sh WORK ma733
```

Downloads DASCH DR7 full-resolution mosaics `ma00731` and `ma00733`, APASS DR9 and Gaia DR3 calibration stars, and JPL Horizons tracks for Pluto and (179) Klytaemnestra at Taunton. [Mosaic SHA-256 digests](../data/recorded/mosaics.json)

`WORK/ma733/ma00733.json` combines the measurement, archive-clock control, plate pipeline and nine shifts of its cutout center. The two trail JSON files give fitted opening, midpoint and closing for both nights. The paper reports a 2.6–3.0 sigma MA 733 excess 3–4 arcsec away, mostly across the track. `fixed-positions` measures the December image position on this plate. Allow 4–15 minutes, including roughly 1 GB of scans, and 1.6 GiB. [MA 733 references](../data/recorded/ma733.json)

## Fixed sky positions

```sh
recorded/run.sh WORK fixed-positions
```

Queries [DASCH DR7 exposures](https://api.starglass.cfa.harvard.edu/public/dasch/dr7/queryexps) at (85.893709844°, +16.016634745°) and (84.9614918°, +16.1337235°). It keeps solved plates with APASS, or if absent ATLAS, limit ≥15.9 and uses the DR7 cutout for each listed solution at that position. Method B fits Gaia DR3 and APASS DR9 stars. `WORK/fixed-positions` keeps both exposure replies, the plate ID lists, per-plate cutout measurements and the combined December and February JSON. Record-level input IDs include the plate name and solution number.

The paper records 87 and 89 successful measurements. Excluding MA 731, December's recorded 24 sensitive plates (calibrated S/N ≥4 at B 16.2) give measured S/N −1.7 to +0.8. The fresh replay measured 87 plates and found 32 sensitive plates by the same criterion, with measured S/N −1.6742 to +0.7540. The fresh February result matches the paper's 89 plates, with 43 sensitive plates giving measured S/N −2.1 to +2.1. Allow roughly 10–60 minutes and up to 0.7 GiB per worker. Set `FIXED_JOBS` to a positive worker count to process separate plates in parallel. [Fixed-position references](../data/recorded/fixed-positions.json)

## Catalogs

```sh
recorded/run.sh WORK catalogs
```

Uses the same positions, [VizieR](https://vizier.cfa.harvard.edu/) tables I/355 (Gaia DR3), II/246 (2MASS), I/322A (UCAC4), I/284 (USNO-B1.0) and B/vsx, [MAST Pan-STARRS DR2](https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2/mean.html) mean and stack, [Legacy Survey DR10](https://datalab.noirlab.edu/tap/sync), and a SkyBoT query at the December PS1 detection epoch. The larger Gaia calibration cone for Method B is saved separately. The February nearest Gaia report of 17.1 arcsec uses the larger February Method A field, beyond the 15 arcsec deep-catalog search. For the z-band image check on PS1 object 127220858937860206, run `checks/ps1_detection.py` as described in the [checks guide](../checks/README.md).

`WORK/catalogs/deepcats.json` and `WORK/catalogs/february/deepcats_1909.json` give distances and photometry. The paper records a December Gaia source at 11.4 arcsec (G 18.86), the same star in 2MASS and USNO-B1.0 at 11.3 and 11.2 arcsec, and no UCAC4 source within 15 arcsec or VSX source within 60 arcsec at either position. The nearest PS1 stack entries are 8.7 and 14.3 arcsec. The nearest single-detection mean entries are at 0.9 and 3.4 arcsec. The fresh February mean query returned six single-detection entries inside the paper's 8.1 arcsec comparison distance. The recorded output contains four entries inside that distance. The fresh mean queries return 13 December and 12 February single-detection entries within 15 arcsec. `WORK/catalogs/february/B2247a-gaia.json` propagates the larger Gaia field to 1909.14 and records the nearest source ID and the catalog file hash. Allow 2–10 minutes and 0.2 GiB. [Catalog references](../data/recorded/catalogs.json)

## Image shape

```sh
recorded/run.sh WORK shape
```

Uses the DASCH DR7 mosaic `ma00731` and Gaia DR3 and APASS DR9 for local astrometry and the comparison stars. Outputs `WORK/shape/defect.json` and `srcshape.json` record Gaussian widths, ellipticity, concentration and angles, and the displaced-image test. `profile.png` shows the profiles. The paper reports width, ellipticity and concentration percentiles 40, 54 and 17 among 48 comparison stars. Allow 1–5 minutes and 0.7 GiB. [Shape reference](../data/recorded/shape.json)

## Weak trails

```sh
recorded/run.sh WORK weak-trails
```

Uses DASCH DR7 mosaics `ma00731` and `ma00733` and Horizons tracks for bodies 179, 1436, 2891, 4204, 2175, 3147, 9593, 13567 and 25493. The per-plate/body JSON contains the Method B free fits. The per-plate summaries include the forced windows and the stacked clocks. The paper's 01:01.5 and 01:04.2 UT midpoints for (1436) and (2891) come from `methodA-december`. The Method B stack peaks at 01:02.5 UT for MA 731. Four of seven testable weaker trails on MA 731 and four of eight on MA 733 have significant excess in the fitted-time window. The archive window has zero of five testable signals on MA 731. Allow 5–25 minutes and 1.6 GiB. [Weak-trail reference](../data/recorded/weak-trails.json)

## Nominal orbit integration

```sh
recorded/run.sh WORK orbits
ORBIT_MODE=full recorded/run.sh WORK orbits
```

The default runs the seeded Horizons-validation sample, up to 20 bodies per dynamical class. Full mode integrates the nominal population in 64 REBOUND and 40 ASSIST shards, selects approaches by the nominal mid-exposure separation and reruns the topocentric Horizons follow-up. Partial scans stay in WORK for a restart. The source elements are live data from the [JPL Small-Body Database](https://ssd-api.jpl.nasa.gov/sbdb_query.api). The recorded elements were at JD 2461200.5. The [DE440 planetary file](https://ssd.jpl.nasa.gov/ftp/eph/planets/Linux/de440/linux_p1550p2650.440) has SHA-256 `29915576d0a6555766b99485ac3056ee415e86df4fce282611c31afb329ad062`. The [sb441-n16 perturber file](https://ssd.jpl.nasa.gov/ftp/eph/small_bodies/asteroids_de441/sb441-n16.bsp) has SHA-256 `919d612ce3c72a78fc7158f9120156542d0f21e6b8b052e4c1339c759747fd90`.

The validation JSON files under `WORK/orbits` are specific to MA 731. In the recorded sample the main-belt median position error was 2.4 arcsec, with errors over one degree for 15 of 63 near-Earth bodies and 1 of 20 Mars-crossers. With fresh elements the sample gave 11 of 63 near-Earth bodies over one degree and reproduced the main-belt median and the Mars-crosser count. The optional full sweep writes the one-degree candidates and their Horizons trails. Its recorded nearest nominal approach other than Pluto was 6.3 arcmin. The 32 other candidates within one nominal degree would have trailed 38–60 arcsec. Allow several minutes for sample integration and Horizons replies, and up to 1.1 GiB to process the element download. The original full integration used 6,565 CPU-seconds and less than 0.8 GiB per integration process. [Orbit and validation references](../data/recorded/orbits.json)

## Code provenance

The scripts in `method-a` and `method-b` are the originally recorded analyses. The release runner supplies public commands and work-directory paths. The Method A reference checker looks under `data/recorded`. The Method B Horizons downloader accepts a plate and body for separate runs. The fixed-position script keeps the original 15.9 depth filter when splitting the batch by plate. The cutout-robustness script accepts a single plate. The trail code sends the original Gaia DR3 query to the public Gaia@ARI and ESA synchronous TAP endpoints before trying Harvard VizieR. Gaia progress messages are suppressed to keep the measurement output machine-readable. In seven Method A and Method B scripts, spaces were added around the matrix-multiplication operator `@`. This is so the public privacy scan does not read a product like `D` times `s.a`, written without spaces, as an email address; the parsed code is unchanged. For the same scan, which reads a run of 12 digits as an internal identifier, seven values in the reference JSON files are rounded to 10 decimal places. Each changes by less than 1e-10, far inside the checker's tolerances.
