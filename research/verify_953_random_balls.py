"""Independent, standard-library-only exact verifier for random ball/grid sets.

Each rectangle is strictly inside a declared ball and D_R. Every pair of balls
has distance intervals strictly excluding each relevant positive integer.
Disjoint rectangle interiors have the exact area reported by the certificate.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json


def verify_balls(data):
    Q = data["coordinate_denominator"]
    rn, rd = data["radius_numerator"], data["radius_denominator"]
    assert all(isinstance(v, int) and v > 0 for v in [Q, rn, rd])
    assert rn*Q % rd == 0
    Rq = rn*Q//rd
    balls = data["balls"]
    m = (2*rn + rd-1)//rd
    for ball in balls:
        assert len(ball) == 3 and all(isinstance(v, int) for v in ball)
        x, y, r = ball
        assert r > 0 and 2*r < Q
        assert x*x+y*y < Rq*Rq
    pairs = 0
    for i, (x, y, r) in enumerate(balls):
        for u, v, s in balls[i+1:]:
            d2 = (x-u)**2+(y-v)**2
            radius_sum = r+s
            for k in range(1, m+1):
                target = k*Q
                if d2 < target*target:
                    assert target > radius_sum
                    assert d2 < (target-radius_sum)**2, f"balls conflict near {k}"
                else:
                    assert d2 > (target+radius_sum)**2, f"balls conflict near {k}"
            pairs += 1
    return {"balls_checked": len(balls), "ball_pairs_checked": pairs,
            "integers_checked": list(range(1, m+1))}


def verify_rectangles(data):
    Q = data["coordinate_denominator"]
    rn, rd = data["radius_numerator"], data["radius_denominator"]
    Rq = rn*Q//rd
    grid = data["grid_cell_denominator"]
    assert isinstance(grid, int) and grid > 0 and Q % grid == 0
    h = Q//grid
    assert 2*Rq % h == 0
    side = 2*Rq//h
    previous_row, previous_end = -1, -1
    cells = 0
    for rectangle in data["rectangle_runs"]:
        assert len(rectangle) == 4 and all(isinstance(v, int) for v in rectangle)
        row, start, end, witness = rectangle
        assert 0 <= row < side and 0 <= start <= end < side
        assert 0 <= witness < len(data["balls"])
        assert row >= previous_row
        if row == previous_row:
            assert start > previous_end, "rectangle interiors overlap"
        else:
            previous_end = -1
        cx, cy, radius = data["balls"][witness]
        xlo, xhi = -Rq+start*h, -Rq+(end+1)*h
        ylo, yhi = -Rq+row*h, -Rq+(row+1)*h
        for x in [xlo, xhi]:
            for y in [ylo, yhi]:
                assert (x-cx)**2+(y-cy)**2 < radius*radius
                assert x*x+y*y < Rq*Rq
        cells += end-start+1
        previous_row, previous_end = row, end
    area = Fraction(cells, grid*grid)
    if "area_fraction" in data:
        assert area == Fraction(data["area_fraction"])
    return {"rectangles_checked": len(data["rectangle_runs"]), "grid_cells": cells,
            "area_fraction": str(area)}


def verify_certificate(data):
    return {"status": "passed all exact integer checks", **verify_balls(data), **verify_rectangles(data)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="*")
    parser.add_argument("--output")
    args = parser.parse_args()
    files = [Path(p) for p in args.files] if args.files else sorted(Path(__file__).parent.glob("erdos953-random-ball-grid-R*.json"))
    results = []
    for path in files:
        data = json.loads(path.read_text(encoding="utf-8"))
        results.append({"file": path.name, **verify_certificate(data)})
    payload = {"certificates_verified": len(results), "results": results}
    if args.output:
        Path(args.output).write_text(json.dumps(payload, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({"certificates_verified": len(results), "output": args.output}))
    else:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
