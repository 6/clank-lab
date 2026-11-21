# Candidate images of Pluto on archival plates from 1908 and 1909

[![Checks](https://github.com/6/clank-lab/actions/workflows/pluto-prediscovery.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/pluto-prediscovery.yml)

[Pluto](https://en.wikipedia.org/wiki/Pluto) was found by Clyde Tombaugh in 1930. Astronomers then searched older photographs for it. The earliest measurements used in the [Minor Planet Center's orbit of Pluto](https://minorplanetcenter.net/db_search/show_object?object_id=134340) come from two Heidelberg plates of January 1914. A team at Yerkes Observatory reported images on plates of August and November 1909, with estimated positions; we found no published numerical astrometry for them. B. E. Schaefer searched the Harvard plate collection in 1982 and again in 2004 and found nothing earlier. The published list of the 1982 search does not include the MA series, and the account of the 2004 search does not list its plates.

We find faint, star-like images at Pluto's predicted position on three public plate scans, a separate image on each: Harvard plate MA 731 of December 21, 1908, and the Heidelberg plates B2247a and B2248b, exposed simultaneously on February 20, 1909. Asteroid trails on MA 731 put its exposure midpoint 5.8 hours before the archived one; at the archived time the scan shows no image within 6 arcseconds of the prediction. Each image lies within about 2 arcseconds of Pluto's position predicted for its plate's adopted midpoint, and two independent measurements agree. The catalogs and comparison plates searched show no steady source there, and no known asteroid of the classes we could test is predicted there from its nominal (best-fit) orbit.

The images are near the plates' limits. The February pair is one night's exposure and cannot confirm the December image, which rests on MA 731 alone. No other qualifying image was found on the earlier plates screened in the three public archives searched, but earlier images are not excluded, and many plates and other collections are not covered. If the identification is correct, the Heidelberg pair predates the Yerkes plates of August 1909, and MA 731 predates both. We offer it as a hypothesis for experts. Examining the original glass, above all MA 731, is the key next check.

<img src="data/stamps.svg" width="650" alt="Three square panels, 2 arcminutes across, from MA 731 (December 21, 1908) and the Heidelberg plates B2247a and B2248b (February 20, 1909). Each shows a faint round image inside a small circle at Pluto's predicted position, with brighter stars nearby.">

Computer-assisted; not yet reviewed by experts.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.24387450](https://doi.org/10.5281/zenodo.24387450)

## Abstract

We report candidate prediscovery images of Pluto on three public plate scans: a Harvard plate of December 21, 1908 and two Heidelberg plates exposed simultaneously on February 20, 1909. At each plate's adopted exposure midpoint (from asteroid trails at Harvard, 5.8 hours before the archived one; archived at Heidelberg) the scan shows a faint star-like image within about 2 arcseconds of Pluto's predicted position, and two independent measurements agree. The brightnesses match Pluto's with the 1933–34 color measured by Schaefer, Buie and Smith, whose account of two Harvard searches reports no earlier image. They would predate the 1914 start of Pluto's orbit fit and the 1909 Yerkes images, reported with estimated positions but no published numerical astrometry. Of 230,352 common random shifts of the predictions, none matched the observed distances and signal-to-noise ratios on every plate. Signal-to-noise at least 4 at any distance, with no Gaia DR3 star brighter than G = 19.5 within 3 arcseconds of the fitted center, on each plate, occurred in 1.5% of trials. The identification is a hypothesis for experts.

This work has not yet been reviewed by experts. The measurements, the code and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

## Check it

Tested with Python 3.14:

```
pip install -r checks/requirements.txt
python checks/rerun.py WORK
```

This downloads the public scans and catalogs (about 0.6 GB) into the folder `WORK`, dates the exposures from asteroid trails, measures the three plates and the 1914 and 1923 Heidelberg control plates, runs the random-position, injection, held-out faint-star, Gaia and SkyBoT controls, and compares 62 numbers with [data/expected.json](data/expected.json). It takes about ten minutes, mostly downloading, and about 1.2 GB of memory. The figure and the blinded sheet are drawn by `checks/figure.py`, and `python checks/ps1_detection.py WORK` rereads the Pan-STARRS artifact (about 135 MB); Method A, the deep catalogs and the asteroid integration are recorded, not rerun. `python checks/census.py WORK` rebuilds the census of earlier plates in under an hour, mostly waiting on the Harvard service; its exposure-level list is [data/census-exposures.csv](data/census-exposures.csv). [checks/README.md](checks/README.md) describes the method, every control and the second, independent measurement.

## Credits

Clyde Tombaugh found Pluto at Lowell Observatory in 1930. E. C. Bower listed the prediscovery images of 1914 to 1927, beginning with the Heidelberg pair of January 1914, exposed by F. Kaiser and measured by Max Wolf. P. J. Melotte reported, then withdrew, a possible 1903 image. A. D. Walker found, C. D. Boyd measured and Bower reduced a Harvard image of 1914 that Schaefer and colleagues later doubted. E. E. Barnard took the Yerkes plates of 1909; W. Wild, G. Buchwald, M. DiMario and E. M. Standish reported Pluto on them, Buchwald, DiMario and Wild followed up, and T. Reichhardt reported W. Osborn and F. Mills's re-examination. B. E. Schaefer searched the Harvard plates in 1982, with Doug Mink's ephemeris, and in 2004. Schaefer, M. W. Buie and L. T. Smith described those searches, measured Pluto's 1930s color and showed that Harvard's MA plates match the Johnson B system. Their account defined the question this work takes up.

The plates were taken by Harvard College Observatory and by August Kopff at Heidelberg. The scans come from Harvard's [DASCH](https://dasch.cfa.harvard.edu/) project (J. Grindlay, P. K. G. Williams and colleagues) and the [Heidelberg Digitized Astronomical Plates](https://dc.g-vo.org/lswscans/res/positions/q/info) (H. Mandel, K. Birkle and M. Demleitner). Positions come from [JPL Horizons](https://ssd.jpl.nasa.gov/horizons/) (Pluto orbit PLU060, planetary ephemeris DE441), known bodies from [IMCCE SkyBoT](https://ssp.imcce.fr/webservices/skybot/) and the JPL Small-Body Database integrated with REBOUND and ASSIST, stars from Gaia DR3 and its synthetic photometry and from APASS, and further plates from APPLAUSE DR4. Murtagh and colleagues recently ran a related DASCH and APPLAUSE search for the distant object 2026 ED138, with plate-time and date checks and Gaia DR3 local astrometry. Further credits are in [checks/README.md](checks/README.md#further-credits). Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamPlutoPrediscovery2026,
  author = {Graham, Peter},
  title = {{Candidate images of Pluto on archival plates from 1908 and 1909}},
  year = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/pluto-prediscovery-v1/results/pluto-prediscovery}},
  doi          = {10.5281/zenodo.24387450}
}
```
