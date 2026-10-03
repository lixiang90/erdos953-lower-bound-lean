"""Pure-integer/Fraction verifier of rational pieces in distinct grid triangles.

Unlike a polygon packing checker, shared edges/vertices are allowed: membership
in distinct triangles proves disjoint interiors. Conflict intervals are checked
on the closed rational polygons, a stronger condition than their open interiors.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json

import numpy as np
from numba import njit, prange


@njit(cache=True, parallel=True)
def uncertain_box_flags(boxes, Q, kmax):
    """Exact int64 pruning only; the caller first proves overflow cannot occur."""
    count = len(boxes)
    flags = np.zeros((count, count), dtype=np.uint8)
    for ii in prange(count):
        i = np.int64(ii)
        ax0, ax1, ay0, ay1 = boxes[i, 0], boxes[i, 1], boxes[i, 2], boxes[i, 3]
        for j in range(i+1, count):
            bx0, bx1, by0, by1 = boxes[j, 0], boxes[j, 1], boxes[j, 2], boxes[j, 3]
            dx = max(0, ax0-bx1, bx0-ax1)
            dy = max(0, ay0-by1, by0-ay1)
            lower = dx*dx+dy*dy
            dx = max(abs(ax0-bx1), abs(ax1-bx0))
            dy = max(abs(ay0-by1), abs(ay1-by0))
            upper = dx*dx+dy*dy
            for k in range(1, kmax+1):
                target = k*Q*k*Q
                if lower <= target <= upper:
                    flags[i, j] = 1
                    break
    return flags


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def squared(a, b):
    return (a[0]-b[0])**2+(a[1]-b[1])**2


def area_twice(polygon):
    return sum(a[0]*b[1]-a[1]*b[0] for a, b in zip(polygon, polygon[1:]+polygon[:1]))


def point_segment_squared(p, a, b):
    length = squared(a, b)
    if length == 0:
        return Fraction(squared(p, a))
    dot = (p[0]-a[0])*(b[0]-a[0])+(p[1]-a[1])*(b[1]-a[1])
    if dot <= 0:
        return Fraction(squared(p, a))
    if dot >= length:
        return Fraction(squared(p, b))
    return Fraction(cross(a, b, p)**2, length)


def expected_triangle(grid_id, Q, rn, rd, n):
    i, j, local = grid_id
    assert -n <= i < n and -n <= j < n and local in [0, 1]
    assert rn*Q % (rd*n) == 0
    h = rn*Q//(rd*n)
    a, b, c, d = [[i*h, j*h], [(i+1)*h, j*h], [(i+1)*h, (j+1)*h], [i*h, (j+1)*h]]
    options = [[a, b, c], [a, c, d]] if (i+j) % 2 == 0 else [[a, b, d], [b, c, d]]
    return options[local]


def polygon_box(polygon):
    return (min(p[0] for p in polygon), max(p[0] for p in polygon),
            min(p[1] for p in polygon), max(p[1] for p in polygon))


def polygons_avoid_integers(a, b, Q, kmax, abox=None, bbox=None):
    if abox is None:
        abox, bbox = polygon_box(a), polygon_box(b)
    ax0, ax1, ay0, ay1 = abox
    bx0, bx1, by0, by1 = bbox
    box_lower = max(0, ax0-bx1, bx0-ax1)**2+max(0, ay0-by1, by0-ay1)**2
    box_upper = max(abs(ax0-bx1), abs(ax1-bx0))**2+max(abs(ay0-by1), abs(ay1-by0))**2
    upper, vertex_lower = None, None
    lower = None
    for k in range(1, kmax+1):
        target = (k*Q)**2
        if box_upper < target or box_lower > target:
            continue
        if upper is None:
            values = [squared(x, y) for x in a for y in b]
            upper, vertex_lower = max(values), min(values)
        if upper < target:
            continue
        if vertex_lower <= target:
            return False
        if lower is None:
            lower = min([point_segment_squared(p, x, y) for p in a for x, y in zip(b, b[1:]+b[:1])]
                        + [point_segment_squared(p, x, y) for p in b for x, y in zip(a, a[1:]+a[:1])])
        if lower <= target:
            return False
    return True


def verify_certificate(data, fast=False):
    Q, rn, rd, n = (data[k] for k in ["coordinate_denominator", "radius_numerator", "radius_denominator", "grid_n"])
    assert all(isinstance(v, int) and v > 0 for v in [Q, rn, rd, n])
    seen, polygons, total_twice = set(), [], 0
    for piece in data["pieces"]:
        grid_id = tuple(piece["grid_id"])
        assert grid_id not in seen, "duplicate mesh cell"
        seen.add(grid_id)
        triangle = expected_triangle(grid_id, Q, rn, rd, n)
        assert piece["triangle"] == triangle
        polygon = piece["polygon"]
        assert len(polygon) >= 3 and all(isinstance(v, int) for p in polygon for v in p)
        area = area_twice(polygon)
        assert area > 0
        for a, b in zip(polygon, polygon[1:]+polygon[:1]):
            assert a != b
            assert all(cross(a, b, p) >= 0 for p in polygon), "non-convex polygon"
        for x, y in polygon:
            assert (x*x+y*y)*rd*rd <= rn*rn*Q*Q
            assert all(cross(a, b, [x, y]) >= 0 for a, b in zip(triangle, triangle[1:]+triangle[:1])), "outside its mesh triangle"
        assert max(squared(a, b) for a in polygon for b in polygon) < Q*Q
        total_twice += area
        polygons.append(polygon)
    kmax = (2*rn+rd-1)//rd
    pairs = 0
    boxes = [polygon_box(polygon) for polygon in polygons]
    fallback_pairs = None
    if fast and polygons:
        max_coordinate = max(abs(v) for box in boxes for v in box)
        assert max(8*max_coordinate*max_coordinate, (kmax*Q)**2) < 2**63-1, "int64 overflow bound"
        flags = uncertain_box_flags(np.array(boxes, dtype=np.int64), np.int64(Q), kmax)
        ii, jj = np.nonzero(flags)
        fallback_pairs = len(ii)
        del flags
        for i, j in zip(ii.tolist(), jj.tolist()):
            assert polygons_avoid_integers(polygons[i], polygons[j], Q, kmax, boxes[i], boxes[j]), f"conflicting polygons {i}, {j}"
        pairs = len(polygons)*(len(polygons)-1)//2
    else:
        for i, a in enumerate(polygons):
            for j in range(i+1, len(polygons)):
                assert polygons_avoid_integers(a, polygons[j], Q, kmax, boxes[i], boxes[j]), f"conflicting polygons at pair {pairs}"
                pairs += 1
    return {"status": "passed all exact integer and rational checks", "pieces_checked": len(polygons),
            "piece_pairs_checked": pairs, "forbidden_integers_checked": list(range(1, kmax+1)),
            "exact_bbox_acceleration": bool(fast), "fraction_fallback_pairs": fallback_pairs,
            "area_fraction": str(Fraction(total_twice, 2*Q*Q)),
            "circle_inclusion_and_grid_disjoint_interiors": "verified"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="*")
    parser.add_argument("--output")
    parser.add_argument("--fast", action="store_true", help="exact int64 box pruning; Python integers/Fraction for uncertain pairs")
    args = parser.parse_args()
    files = [Path(p) for p in args.files] if args.files else sorted(Path(__file__).parent.glob("erdos953-triangle-certificate-R*.json"))
    results = [{"file": path.name, **verify_certificate(json.loads(path.read_text(encoding="utf-8")), args.fast)} for path in files]
    report = {"certificates_verified": len(results), "results": results}
    if args.output:
        Path(args.output).write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({"certificates_verified": len(results), "output": args.output}))
    else:
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
