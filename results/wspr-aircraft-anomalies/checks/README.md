# Checks

## What the scripts do

- `selftest.py RESULTS` is the quick offline check (seconds). It tests the anomaly rule against a direct two-pass computation, including a triple with very large frequency values (the case behind the correction described below). It tests the crossing geometry on three synthetic tracks. Then it recomputes the verdict from [../data/results.json](../data/results.json), checks the identity $\Delta = E_\text{real} - (E_\text{placebo 1} + E_\text{placebo 2})/2$, and confirms that two corruptions of the results change the verdict.
- `days.py` lists the 36 sample days; `days.py --placebos` adds each day's next and previous sample day, which supply its placebo aircraft.
- `fetch.py DAY DATA` downloads one day's inputs: the wspr.live mirror of the WSPRnet database, hour by hour from 21:00 UTC on the day before to 01:00 UTC on the day after, and the ADS-B Exchange snapshots for minutes 0 to 60 of the eight blocks, each reduced to the fields used.
- `prep.py DAY NEXT PREVIOUS DATA OUT` computes, for every scored link-slot of DAY, the anomaly flags, the nearest high and airborne aircraft distances under the real and both placebo fleets, the coverage mask, and the planted-control flags.
- `analyze.py OUT UNITS...` runs the two designs, the placebo-differenced statistic, the day bootstrap, the variants and the verdict, and writes `results.json`.
- `check.py UNITS DATA N SEED [corrupt-label|corrupt-anomaly]` is an independent spot check that imports nothing from the pipeline. For N random units it recomputes the flags from the raw WSPR files in plain Python, and the aircraft distances from re-downloaded raw ADS-B snapshots, with haversine and cross-track formulas at 1-second sampling. It exits 1 on any mismatch; each corruption must make it exit 1.
- `replay-day.sh DAY WORK` replays one day from the public data: fetch, prep, `compare_day.py` against [../data/per_day.csv](../data/per_day.csv) (1% tolerance, since the mirror can gain late reports), then `check.py` on 20 units.
- `replay.sh WORK [JOBS]` replays everything (about 12 CPU-hours, 8 GB of memory per worker, about 0.5 GB of reduced downloads per day), then runs `sens.py`.
- `sens.py OUT UNITS...`, `geocheck.py UNITS DATA SEED N OUT` and `dayprofile.py OUT UNITS...` are the sensitivity runs and the day profile described below.
- `exactflags.py`, `loo_withheld.py` and `tallies.py` are the checks added in review, described below.
- `days_new.py` lists the second sample's 36 dates (`--placebos` as for `days.py`, within the second sample), and `replay-new.sh WORK [JOBS]` replays the second sample and the pooled analysis after `replay.sh WORK` (about 13 CPU-hours).

## The protocol fixed before the outcome

[protocol-frozen.txt](protocol-frozen.txt) is the protocol exactly as frozen, before the outcome on the sample days was computed. Its links to other files point to the working repository, which is not released. Its SHA-256 at the freeze is `36aea2d539f92b32daf015959fd66598b901a1806220b32f669497cf05521b08`. The order of freeze and computation rests on the working repository's commit history; no outside timestamping service was used.

A one-day pilot outside the sample (December 1, 2023, with November 1, 2023 as its placebo day) set the design before the freeze. Its outcome statistic was not computed. It found that under a first draft, with "uncrossed" meaning no aircraft within 50 km, only 41 of 175,839 covered link-slots were uncrossed. It also found a bug that left placebo snapshots on their own day's clock. Both were fixed before the freeze.

Departures from the protocol, all reported in the paper:

- The author's extension of sparse windows over ±3 days is not implemented. Reports with fewer than five window reports are dropped instead. This changes which link-slots are compared and could shift the contrast in either direction. The protocol's own sentence that it "cannot create an association" is not supported, and is withdrawn here.
- Six-character locator centers replace the author's private antenna-position database.

## Correction made after the outcome was seen

After the first full run, `check.py` found 8 mismatches in 20 units on October 1, 2025, all in the frequency score. `prep.py` took window sums from one floating-point running sum over the whole day, and a triple with frequencies far from its first value pushed the running sum of squares past $2^{53}$, so small windows later in the sort order lost their variance. The fix uses exact integer window sums. It changed 439,157 frequency scores on 4 of the 36 days and no SNR score. The verdict was negative before the fix (design W +0.73 per 100, interval −0.37 to 1.83; design M +0.20, −0.97 to 1.27) and after it (+0.75, −0.37 to 1.85; +0.22, −0.95 to 1.29). After the fix, `check.py` found no mismatch in 140 units on 7 days, and a full rerun of the fixed `prep.py` on October 1, 2025 equals the recomputed flags array for array.

## Independent reimplementation

A reimplementation written from the protocol alone, without the code or the results, gave:

| Quantity | Reimplementation | This run |
| --- | --- | --- |
| Verdict | negative | negative |
| Δ, design W, per 100 | +0.54 (−0.51 to 1.64) | +0.75 (−0.37 to 1.85) |
| Δ, design M | −0.09 (−1.17 to 0.83) | +0.22 (−0.95 to 1.29) |
| Planted Δ, W and M | +3.19 and +1.94 | +3.68 and +2.34 |
| Crossed share of covered link-slots | 96.6% | 96.8% |
| Cases and controls, W | 44,096 and 67,996 | 36,359 and 53,853 |
| Cases and controls, M | 39,893 and 56,799 | 32,371 and 46,083 |
| Scored link-slots | 27,870,551 | 24,306,881 |

The comparison criteria were fixed before it started: same verdict, Δ within 0.5 per 100 in each design, planted lower limits above zero, and case and control counts within 5% with the crossed share within 1 point. All pass except the counts, which differ by 21% to 26%. Most of the gap comes from the mobile-station rule. The protocol drops "a call sign reported with more than one locator in the downloaded day". This run builds each call sign's locator set over all reports, so a station alternating four- and six-character locators (for example JN59 and JN59mo) is dropped. The reimplementation used six-character reports only. On February 1, 2023 the two readings keep 2,543,894 and 3,219,013 reports (ratio 1.265, against 1.26 for scored link-slots that day). The two implementations also differ in smaller ways (odd-minute reports, baseline order, altitude assignment, strict cutoffs and the planted selection), so this accounts for most of the gap, not all of it. A first round of the reimplementation had labeled only 3 of the 8 blocks; that error was found and fixed before the round reported here.

## Sensitivity runs

These were added after the frozen run, to check choices the protocol left open. None replaces the frozen verdict. [../data/sens.json](../data/sens.json) and [../data/per_date_sums.csv](../data/per_date_sums.csv) hold their output; [../data/geocheck.json](../data/geocheck.json) summarizes the geometry check, and [../data/day_profile.json](../data/day_profile.json) profiles each day's design-W cases.

- Matching variants. `sens.py` reruns both designs with matching on the two-minute slot start (`t // 120 * 120`) instead of the exact report time, with reports not timed on an even minute dropped, with strict control cutoffs (> 25 km and > 5 km), and with all three together. The odd-minute drop happens at the matching stage only: the precomputed distances, coverage and flag windows of the remaining reports are kept. Δ changes by at most 0.02 per 100 and every run is negative. The strict run returns the same statistics as the frozen one. The first version of `sens.py` keyed slots before testing for odd minutes, so its "all three" run kept every report and equaled the slot-key run; review round 56 found this, the order is fixed, and the corrected run equals the odd-minute run (slot keys change only odd-minute times).
- Dependence between days. Each day's aircraft also serve as a placebo for its neighbors, so `sens.py` resamples moving blocks of 2, 3, 4 and 6 successive sampled dates in date order, wrapping at the end (10,000 draws, seed 20261121 plus the block length). This keeps part of the dependence, not all of it: in the pooled run the blocks follow the date order across both samples, while placebos wrap within each sample. The widest design-W interval is −0.49 to 1.97 (blocks of 3); all are negative.
- Leaving out one day. `sens.py` recomputes Δ and its interval without each day's sums in turn, with the frozen resampling scheme and seed, keeping every other label and match, including the neighbors' placebo labels made from the removed day's aircraft (`loo_withheld.py`, below, removes those too). 35 of the 36 deletions are negative (largest upper limits 1.975 in design W and 1.457 in design M). Without December 1, 2025, design W gives +0.91 (−0.18 to 2.01), which the decision rule would call inconclusive; design M gives +0.24 (−0.96 to 1.35) and the planted effect is still detected. [../data/per_date_sums.csv](../data/per_date_sums.csv) holds the per-day sums these use.
- The influential day. On December 1, 2025, design W's real excess is −2.61 per 100 over 1,441 cases, against +0.39 and +0.82 with its placebo fleets (December 1, 2022, by the cyclic rule, and November 1, 2025). Three days have lower single-day Δ but fewer cases; leaving out any of them gives upper limits of 1.97 to 1.98. `dayprofile.py` shows nothing else unusual about the day: 524 links, the five busiest holding 8% of its cases (median over the days 8.4%), median path 290 km (271 km), and its most frequent station in 18% of its cases (5% to 28% on other days).
- Crossing geometry. `geocheck.py` compares the pipeline's distances with `check.py`'s unscreened distance (every aircraft in the raw snapshots, 1-second sampling) on 960 units: 6 randomly drawn days, and on each, with seed 1123, 40 units from each of four classes (high-track distance 3 to 7 km and 23 to 27 km, any-aircraft distance 3 to 7 km, and controls that a design uses). Three units change class. On December 1, 2022 and September 1, 2025, a control lies next to an aircraft whose reported positions jump 230 km in 74 s and 600 km in 63 s; the reference interpolates across the jump. On August 1, 2024, a report timed at 03:15 UTC is sampled from its slot start by the pipeline and from its own time by the reference. The odd-minute variant drops such reports at matching but keeps the other precomputed quantities, so it does not show what a different timing convention throughout the pipeline would give. On the other 957 units the distances agree within 0.5 km.

## The second sample

[protocol-addendum.txt](protocol-addendum.txt) is the addendum exactly as committed before any data for the new dates was downloaded (its sections 5 and 6, the timed piece and the date replacements, were added before any of them was labeled). The first sample's negative outcome rested on one day, so a second sample was fixed by one rule: the 36 most recent first-of-month dates not used before, counting back from November 1, 2026, with any date missing an ADS-B snapshot replaced by the next earlier complete one. December 1, 2020 and January 1, 2021 lacked snapshots and were replaced by October 1, 2020 and August 1, 2020 (September 1, 2020 also lacked two). The code ran unchanged, with placebos cyclic within the second sample. The decision was fixed with it: the negative outcome counts as robust only if the pooled analysis is negative under the frozen rule and stays negative under each of the 72 single-day deletions and at block lengths 2, 3, 4 and 6. It is.

- Second sample alone ([../data/second-sample/results.json](../data/second-sample/results.json)): design W Δ −0.29 per 100 (−1.22 to 0.65); design M +0.46 (−0.64 to 1.65); planted +2.29 and +2.96; negative. All 36 deletions and block lengths are negative.
- Pooled 72 days ([../data/pooled/results.json](../data/pooled/results.json)): design W +0.21 (−0.53 to 0.95), design M +0.35 (−0.46 to 1.17); planted +2.96 and +2.68; negative. The largest single-deletion upper limits are 1.02 (W, without December 1, 2025) and 1.25 (M, without July 1, 2026); the widest block intervals are −0.58 to 0.99 (W) and −0.48 to 1.15 (M).
- Checks: every new date had all 488 snapshots; `check.py` found no mismatch in 20 units on each of February 1, 2022, November 1, 2022 and August 1, 2026 (drawn at random); August 1, 2026 labeled in two different environments gave byte-identical units files. [../data/second-sample/per_day.csv](../data/second-sample/per_day.csv) holds the per-day counts a replay compares.
- A second reimplementation, written from the protocol and the addendum alone (without the code, the results or the addendum's account of the first sample), ran all 72 days. Its criteria were fixed before it started: the same verdicts, Δ within 0.5 per 100, planted lower limits above zero, the robust condition, and counts within 5% with the crossed share within 1 point. All hold. Second sample: W −0.34 (−1.26 to 0.58), M +0.37 (−0.75 to 1.59). Pooled: W +0.21 (−0.50 to 0.92), M +0.32 (−0.44 to 1.11), negative in every deletion (largest upper limits 1.00 and 1.21) and block length. Its counts are 2% to 5% above this run's, crossed share 96.3% against 96.4%. It counts a station as mobile only when its locator changes, not when it reports a square in four and in six characters, which is the reading behind the first reimplementation's larger gap.
- `analyze.py` resamples days in the order of its sorted file paths, so the pooled run puts the second sample's dates first (as `replay-new.sh` does); `sens.py` sorts by date. Their pooled limits differ by at most 0.02 per 100.

## Checks added in review

Review round 56 (November 23, 2026) asked for these. None changes the frozen verdict.

- `exactflags.py DAY DATA UNITS OUT` rechecks the SNR and frequency flags of every scored link-slot in exact integer arithmetic: |z| > 0.75 exactly when 16(nx − S1)²(n − 1) > 9n(nS2 − S1²), with no flag at zero variance, using the real and the planted SNR. On all 72 dates (45,033,331 link-slots) no flag differs from the recorded units. Exactly at |z| = 0.75 there are 5,633 SNR and 20,631 frequency scores, and none is flagged, as the strict rule requires. On four dates (June, August, September and October 2025) a malformed report puts a frequency about 2^32 Hz from its link's first value, beyond what `prep.py`'s 64-bit squares hold; the exact check, in unbounded integers, covers those dates too. Summary: [../data/review/exactflags.json](../data/review/exactflags.json).
- `loo_withheld.py OUT SUMS UNITS...` repeats the single-date deletions with the deleted date's aircraft removed everywhere: a remaining date whose placebo came from the deleted date uses its other placebo for both. Pooled, all 72 deletions are negative (largest upper limits 1.06 in design W and 1.35 in design M; smallest planted lower limit 1.60). In the second sample alone all 36 are negative, with design M up to 1.999 without February 1, 2021. In the first sample alone 7 of 36 are inconclusive, with design W upper limits from 2.00 to 2.16. Outputs: [../data/review/](../data/review/), `loo-withheld-*.json`.
- `tallies.py OUT UNITS...` counts, from the units files, the covered, crossed and uncrossed link-slots, the planted link-slots and the median path lengths. Pooled, 4,128,269 of the 41,301,615 crossed link-slots with labels were planted, 2,572,854 of them covered and crossed. Counting each link-slot once, the median length is 957.6 km for covered crossed link-slots and 197.1 km for uncrossed ones. Output: [../data/review/tallies.json](../data/review/tallies.json).
- The corrected "all three together" run of `sens.py` (above) replaces the earlier one in each `sens.json`.

## Implementation notes

- WSPR reports whose time is not on an even minute are put in the slot that contains them. A slot's track sampling starts at its first selected report's time.
- A track counts as high (FL200 or above) for the whole slot if any of its three snapshots reports a barometric altitude of at least 20,000 ft.
- Control cutoffs are inclusive (25 km and 5 km count as uncrossed).
- A snapshot position's age is the snapshot's `now` minus the aircraft's `seen_pos`; a missing `seen_pos` counts as 0 s, and positions older than 60 s are dropped.
- Distances are capped at 30 km behind a 90 km candidate screen, with a 0.1 rad guard on sign changes along the track.
- The coverage mask samples each arc every 10 km or less and counts every aircraft, on the ground or not, with the available snapshots as divisor (no snapshot was missing on any sample day).
- The planted control draws from every crossed link-slot with labels, inside the coverage mask or not.

## Data notes

- The WSPR mirror can gain late reports, and ADS-B Exchange can change its samples. A replay compares counts with a 1% tolerance for that reason.
- ADS-B Exchange offers its first-of-month samples "for testing and evaluation". No raw data are redistributed here; the scripts download them.
- Python 3 with NumPy 2.1.3 ([requirements.txt](requirements.txt)). The recorded run used one thread per worker.

## Further credits

The anomaly rule and the hypothesis are Richard Godfrey's, stated on the OE-FGR case study page; Godfrey's later reports are written with Hannes Coetzee and Simon Maskell. Godfrey credits Robert Westphal with first proposing WSPR for tracking MH370; Westphal's working paper of February 28, 2025 describes balloon-borne WSPR beacons used as test transmitters. The critical literature includes Victor Iannello's posts, Steve Kent's link-budget paper, Mick Gilbert's check of the QF6036 blind test, Nils Schiffhauer's spectrogram measurements and Joe Taylor's statement relayed by Mike Exner, all as recorded in Iannello's "WSPR Can't Find MH370" (December 19, 2021) and its comments. Ed Anderson's one-day comparison of ADS-B and WSPR paths in those comments is the closest earlier analysis. The University of Liverpool team (Simon Maskell, Alberto Acuto, Paul Horridge and Shashi Lakra) announced a study of WSPR data on known trajectories in March 2024; no result from it had been published when this was written.
