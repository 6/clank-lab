# A placebo-controlled test of WSPR signal anomalies on radio paths crossed by tracked aircraft

[![Checks](https://github.com/6/clank-lab/actions/workflows/wspr-aircraft-anomalies.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/wspr-aircraft-anomalies.yml)

Over 72 sampled days, we compared similar signal reports from the [WSPR](https://en.wikipedia.org/wiki/WSPR_(amateur_radio_software)) amateur radio network with and without a tracked plane crossing the path between the two stations. We found no detectable difference in how often readings looked unusual. These reports give no support for using unusual readings to track aircraft, as Richard Godfrey, Hannes Coetzee and Simon Maskell proposed for [Malaysia Airlines Flight 370](https://en.wikipedia.org/wiki/Malaysia_Airlines_Flight_370).

We flagged unusual readings with a rule adapted from Godfrey's 2024 proposal and fixed before the analysis. We counted a path as crossed when a tracked plane at 20,000 feet or higher came within 5 km of the shortest path between the stations along Earth's surface. In the airspace covered by the public tracking data, 96% of scored records met that definition. Only 0.3% of crossed records had a matching record with no tracked plane nearby. We compared those records, then repeated the comparison with aircraft positions from other days and subtracted that result. With either matching method, the upper limit of the 95% interval was below two extra flags per 100 matched records from crossed paths, even when we left out any one day. Both methods detected a simulated increase.

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24459621](https://doi.org/10.5281/zenodo.24459621)

## Abstract

Pooled over a first sample of 36 dates and a follow-up of 36 chosen after the first result and before its data were downloaded, the placebo-adjusted excess of a prespecified adaptation of Godfrey's 2024 WSPR anomaly flag is $+0.21$ per 100 for same-link matching (95% nominal interval $-0.53$ to $0.95$) and $+0.35$ for shared-station matching ($-0.46$ to $1.17$). These are matched records on covered paths whose surface arc between the stations' locator centers passes within 5 km of a modeled high-altitude (at least 20,000 ft) aircraft track, 0.3% of all such records. WSPR is an amateur-radio network reporting decoded weak signals; with ADS-B, aircraft broadcast their positions. Godfrey and colleagues proposed that aircraft near a transmitter–receiver path raise the anomaly rate, and used anomalies to propose a path for flight MH370. Controls are matched records near no tracked aircraft; the same comparison with other days' aircraft is subtracted. A simulated 6 dB SNR increase on 10% of such records, drawn before coverage filtering and matching, is detected. The adjusted flag rate shows no detectable increase on matched covered paths: both upper limits stay below the pre-set 2 per 100, also without any one date.

This work has not yet been reviewed by experts. The analysis, the code and the text were produced by AI models from OpenAI and Anthropic, working under the author's direction.

## Check it

Needs Python 3.10 or later with NumPy (`pip install -r checks/requirements.txt`). The quick check runs offline in seconds:

```
python3 checks/selftest.py data/results.json
python3 checks/selftest.py data/second-sample/results.json
python3 checks/selftest.py data/pooled/results.json
```

It tests the anomaly rule and the crossing geometry on synthetic inputs, recomputes the verdict from the recorded results of each sample and the pooled analysis, and confirms that two corruptions of the results change the verdict. Replaying from the public data takes much longer. `sh checks/replay-day.sh DAY WORK` replays one sample day (about 30 CPU-minutes, 8 GB of memory) and compares its counts with the recorded run. `sh checks/replay.sh WORK` replays the first sample's 36 days and its sensitivity runs (about 12 CPU-hours), and `sh checks/replay-new.sh WORK` the second sample and the pooled analysis (about 13 CPU-hours). [checks/README.md](checks/README.md) describes the scripts, the protocol fixed before the outcome, a correction made after it, an independent reimplementation, the sensitivity runs, the second sample and the checks added in review.

## Credits

The hypothesis and the anomaly rule are Richard Godfrey's, stated on the OE-FGR case study page. The OE-FGR report is by Godfrey and Hannes Coetzee, and the QTR901, THY161, MH370 and global passive radar reports by Godfrey, Coetzee and Simon Maskell; the 2025 report on 48 flights is the closest earlier controlled comparison. Robert Westphal first proposed using archived WSPR data for MH370 (HamSCI, 2021). The University of Liverpool team (Maskell, Alberto Acuto, Paul Horridge and Shashi Lakra) announced in 2024 a study of WSPR data on flights with known trajectories. The controls answer the critique collected in Victor Iannello's post "WSPR Can't Find MH370" and its comments, and Steve Kent's link-budget analysis. The closest earlier analysis of all traffic is Ed Anderson's one-day comparison of ADS-B positions with WSPR paths, which this test extends to 72 days with fixed controls.

The WSPR reports come from the WSPRnet community through the wspr.live mirror, and the aircraft positions from the sample data of ADS-B Exchange. Neither is redistributed here; the scripts download them. Further credits are in [checks/README.md](checks/README.md#further-credits). Apache-2.0 (see the repository's LICENSE).

## Cite

```bibtex
@misc{GrahamWsprAircraftAnomalies2026,
  author = {Graham, Peter},
  title = {{A placebo-controlled test of WSPR signal anomalies on radio paths crossed by tracked aircraft}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/wspr-aircraft-anomalies-v2/results/wspr-aircraft-anomalies}},
  doi          = {10.5281/zenodo.24459621}
}
```
