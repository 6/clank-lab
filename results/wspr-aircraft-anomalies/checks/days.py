"""The 36 sample days (protocol-frozen.txt section 2); --placebos adds each day's previous and next."""
import sys
days = ["2022-12-01"] + [f"{y}-{m:02d}-01" for y in (2023, 2024, 2025) for m in range(1, 13)]
days.remove("2023-12-01")   # the pilot
days.sort()
assert len(days) == 36
if "--placebos" in sys.argv:
    for i, d in enumerate(days):
        print(d, days[(i + 1) % 36], days[i - 1])
else:
    print("\n".join(days))
