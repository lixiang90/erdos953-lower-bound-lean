"""Turn saved random point sets into exact rational rectangle-area certificates.

The grid is a conservative subset of an adaptive ball union. Integer square
roots determine which whole cells fit; no floating point enters the area or
geometric certification. Random coordinates/radii are rounded before checking.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json
import math

import numpy as np

from verify_953_random_balls import verify_certificate

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def ceil_div(a, b):
    return -((-a)//b)


def make_certificate(result, grid=1000):
    saved = np.load(HERE / f"erdos953-random-points-{result['case']}.npz")
    centers = saved["points"][saved["selected"]]
    Q = 100_000_000
    assert Q % (2*grid) == 0
    coords = np.rint(centers*Q).astype(np.int64)
    radii = np.floor(saved["ball_radii"]*Q).astype(np.int64)-32
    balls = [[int(x), int(y), int(r)] for (x, y), r in zip(coords, radii)]
    rn, rd = int(round(2*result["R"])), 2
    Rq = rn*Q//rd
    h, half = Q//grid, Q//(2*grid)
    origin_mid = -Rq+half
    side = 2*Rq//h
    rows = [[] for _ in range(side)]
    disk_intervals = []
    for row in range(side):
        y = origin_mid+row*h
        limit = Rq*Rq-(abs(y)+half)**2-1
        if limit < 0:
            disk_intervals.append((1, 0))
            continue
        dx = math.isqrt(limit)-half
        disk_intervals.append((ceil_div(-dx-origin_mid, h), (dx-origin_mid)//h))
    for witness, (cx, cy, r) in enumerate(balls):
        low_row = max(0, ceil_div(cy-r+half-origin_mid, h))
        high_row = min(side-1, (cy+r-half-origin_mid)//h)
        for row in range(low_row, high_row+1):
            y = origin_mid+row*h
            limit = r*r-(abs(y-cy)+half)**2-1
            if limit < 0:
                continue
            dx = math.isqrt(limit)-half
            if dx < 0:
                continue
            dlo, dhi = disk_intervals[row]
            lo = max(0, dlo, ceil_div(cx-dx-origin_mid, h))
            hi = min(side-1, dhi, (cx+dx-origin_mid)//h)
            if lo <= hi:
                rows[row].append((lo, hi, witness))
    rectangle_runs = []
    cell_count = 0
    for row, intervals in enumerate(rows):
        covered_until = -1
        for lo, hi, witness in sorted(intervals):
            start = max(lo, covered_until+1)
            if start <= hi:
                rectangle_runs.append([row, start, hi, witness])
                cell_count += hi-start+1
                covered_until = hi
    area = Fraction(cell_count, grid*grid)
    data = {"experiment": result["case"], "coordinate_denominator": Q,
            "radius_numerator": rn, "radius_denominator": rd, "balls": balls,
            "grid_cell_denominator": grid, "rectangle_runs": rectangle_runs,
            "area_fraction": str(area),
            "construction": "union of the open interiors of pairwise interior-disjoint rational rectangles"}
    audit = verify_certificate(data)
    filename = HERE / f"erdos953-random-ball-grid-{result['case']}.json"
    filename.write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")
    return filename, audit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--top", type=int, default=2, help="number of adaptive-union candidates per R")
    parser.add_argument("--grid", type=int, default=1000)
    parser.add_argument("--radii", nargs="+", type=float,
                        help="only certify these outer disk radii")
    args = parser.parse_args()
    path = HERE / f"erdos953-random-point-results-{STAMP}.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    audits = []
    for R in sorted({r["R"] for r in report["results"]}):
        if args.radii is not None and R not in args.radii:
            continue
        candidates = sorted((r for r in report["results"] if r["R"] == R),
                            key=lambda r: r["adaptive_disk_union"]["area"], reverse=True)[:args.top]
        for result in candidates:
            filename, audit = make_certificate(result, args.grid)
            result["ball_grid_certificate"] = filename.name
            result["exact_ball_grid_area_fraction"] = audit["area_fraction"]
            result["exact_ball_grid_area"] = float(Fraction(audit["area_fraction"]))
            audits.append({"file": filename.name, **audit})
            print(json.dumps({"case": result["case"], **audit}), flush=True)
            path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    (HERE / f"erdos953-random-ball-grid-audit-{STAMP}.json").write_text(json.dumps(audits, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
