"""The 36 new sample dates (protocol-addendum.txt section 1): the 36 most recent first-of-month
dates not used before, counting back from 2026-11-01. --placebos adds each date's next and
previous date of the new sample, cyclically (the same format as days.py --placebos)."""
import sys
used = ["2022-12-01"] + [f"{y}-{m:02d}-01" for y in (2023, 2024, 2025) for m in range(1, 13)]  # old sample + pilot
missing = {"2017-10-01",   # no ADS-B Exchange sample
           "2020-12-01", "2021-01-01", "2020-09-01"}   # snapshots missing; replaced (protocol-addendum.txt section 6)
days, y, m = [], 2026, 11
while len(days) < 36:
    d = f"{y}-{m:02d}-01"
    if d not in used and d not in missing:
        days.append(d)
    y, m = (y, m - 1) if m > 1 else (y - 1, 12)
days.sort()
assert len(days) == 36 and days[0] == "2020-08-01" and days[-1] == "2026-11-01"
if "--placebos" in sys.argv:
    for i, d in enumerate(days):
        print(d, days[(i + 1) % 36], days[i - 1])
else:
    print("\n".join(days))
