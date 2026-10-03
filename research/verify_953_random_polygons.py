"""Pure-integer/Fraction verifier for open convex polygon constructions.

Checks convexity, disk inclusion, same-component diameter < 1, disjointness,
and every positive integer against exact cross-component distance intervals.
No numpy, scipy, random generator, or floating-point arithmetic is used.
"""

from fractions import Fraction
from pathlib import Path
import argparse
import json
import math


def cross(a, b, c):
    return (b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])


def distance_sq(a, b):
    return (a[0]-b[0])**2 + (a[1]-b[1])**2


def polygon_area_twice(polygon):
    return abs(sum(a[0]*b[1]-a[1]*b[0]
                   for a, b in zip(polygon, polygon[1:]+polygon[:1])))


def point_segment_distance_sq(p, a, b):
    length = distance_sq(a, b)
    if not length:
        return Fraction(distance_sq(p, a))
    dot = (p[0]-a[0])*(b[0]-a[0])+(p[1]-a[1])*(b[1]-a[1])
    if dot <= 0:
        return Fraction(distance_sq(p, a))
    if dot >= length:
        return Fraction(distance_sq(p, b))
    return Fraction(cross(a, b, p)**2, length)


def on_segment(a, b, p):
    return (cross(a, b, p) == 0 and min(a[0], b[0]) <= p[0] <= max(a[0], b[0])
            and min(a[1], b[1]) <= p[1] <= max(a[1], b[1]))


def segments_intersect(a, b, c, d):
    x, y, z, w = cross(a, b, c), cross(a, b, d), cross(c, d, a), cross(c, d, b)
    if x*y < 0 and z*w < 0:
        return True
    return ((x == 0 and on_segment(a, b, c)) or (y == 0 and on_segment(a, b, d))
            or (z == 0 and on_segment(c, d, a)) or (w == 0 and on_segment(c, d, b)))


def contained(p, polygon):
    signs = [cross(a, b, p) for a, b in zip(polygon, polygon[1:]+polygon[:1])]
    return all(s >= 0 for s in signs) or all(s <= 0 for s in signs)


def polygon_distance_sq(a, b):
    ae = list(zip(a, a[1:]+a[:1]))
    be = list(zip(b, b[1:]+b[:1]))
    if contained(a[0], b) or contained(b[0], a):
        return Fraction(0)
    if any(segments_intersect(x, y, u, v) for x, y in ae for u, v in be):
        return Fraction(0)
    return min([point_segment_distance_sq(p, u, v) for p in a for u, v in be]
               + [point_segment_distance_sq(p, x, y) for p in b for x, y in ae])


def compatible(a, b, denominator):
    lower = polygon_distance_sq(a, b)
    upper = max(distance_sq(x, y) for x in a for y in b)
    # Disjoint polygons allow exact area addition.
    if lower <= 0:
        return False, None
    k = 1
    while k*k*denominator*denominator <= upper:
        if lower <= k*k*denominator*denominator:
            return False, None
        k += 1
    return True, {"minimum_squared_distance": str(lower / denominator**2),
                  "maximum_squared_distance": str(Fraction(upper, denominator**2))}


def verify_certificate(data):
    denominator = int(data["coordinate_denominator"])
    rn, rd = int(data["radius_numerator"]), int(data["radius_denominator"])
    polygons = data["polygons"]
    assert denominator > 0 and rn > 0 and rd > 0
    diameters = []
    for polygon in polygons:
        assert len(polygon) >= 3 and polygon_area_twice(polygon) > 0
        # Every other vertex must be on the same side of each oriented edge.
        orientation = cross(polygon[0], polygon[1], polygon[2])
        assert orientation != 0
        for a, b in zip(polygon, polygon[1:]+polygon[:1]):
            assert a != b
            assert all(cross(a, b, p)*orientation >= 0 for p in polygon)
        for x, y in polygon:
            assert (x*x+y*y)*rd*rd < rn*rn*denominator*denominator
        largest = max(distance_sq(a, b) for a in polygon for b in polygon)
        assert largest < denominator*denominator
        diameters.append(str(Fraction(largest, denominator*denominator)))
    cross_checks = []
    for i, a in enumerate(polygons):
        for j in range(i+1, len(polygons)):
            success, interval = compatible(a, polygons[j], denominator)
            assert success, f"incompatible polygons {i}, {j}"
            cross_checks.append({"polygons": [i, j], **interval})
    area = Fraction(sum(polygon_area_twice(p) for p in polygons), 2*denominator*denominator)
    return {"status": "passed exact integer and rational checks", "polygon_count": len(polygons),
            "area_fraction": str(area), "area_fraction_value": area,
            "component_squared_diameters": diameters, "cross_distance_checks": cross_checks}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="*")
    parser.add_argument("--output")
    args = parser.parse_args()
    paths = [Path(p) for p in args.files] if args.files else sorted(Path(__file__).parent.glob("erdos953-random-polygons-R*.json"))
    output = []
    for path in paths:
        data = json.loads(path.read_text(encoding="utf-8"))
        result = verify_certificate(data)
        del result["area_fraction_value"]
        output.append({"file": path.name, **result})
    payload = {"certificates_verified": len(output), "results": output}
    if args.output:
        Path(args.output).write_text(json.dumps(payload, indent=2)+"\n", encoding="utf-8")
        print(json.dumps({"certificates_verified": len(output), "output": args.output}))
    else:
        print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
