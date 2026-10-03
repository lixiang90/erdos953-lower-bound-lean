"""Independent standard-library audit of sequential full-integer annulus fills."""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
from bisect import bisect_left, insort
import argparse
import hashlib
import json
import math
from verify_953_infinite_ring_extension import params, points, phase_bounds

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def baseline(d):
    report = json.loads((HERE/f"erdos953-Ainfty-ring-extension-independent-audit-{STAMP}.json").read_text())
    assert report["all_passed"]
    old_path = HERE/d["old_hole_certificate"]
    assert sha(old_path) == d["old_hole_certificate_sha256"] == report["additional_hole_extension"]["sha256"]
    result = [(F(-1, 2), F(1, 2), F(-23, 32), F(5, 32))]
    generations = [None]
    for j in range(6, 14):
        path = HERE/f"erdos953-Ainfty-ring-block-j{j}-{STAMP}.json"
        previous = next(b for b in report["blocks"] if b["j"] == j)
        assert sha(path) == previous["sha256"]
        block = json.loads(path.read_text())
        k, n = params(j)
        D = block["height_denominator"]
        centers = points(j, k, n)
        assert len(centers) == len(block["height_numerators"])
        for (x, y), h in zip(centers, block["height_numerators"]):
            result.append((F(x)-F(1, 6), F(x)+F(1, 6), F(y)-F(h, 2*D), F(y)+F(h, 2*D)))
            generations.append(j)
    old = json.loads(old_path.read_text())
    result.extend(tuple(map(F, r)) for r in old["added_rectangles"])
    generations.extend([6]*len(old["added_rectangles"]))
    assert len(result) == d["baseline_source_rectangles_with_base_enclosure"]
    return result, generations


def forbidden(a, b, S, E):
    low = 0
    high = 0
    for start, stop, bottom, top in ((a[0], a[1], b[0], b[1]), (a[2], a[3], b[2], b[3])):
        closest = max(bottom-stop, start-top, 0)
        farthest = max(abs(start-top), abs(stop-bottom))
        low += closest*closest
        high += farthest*farthest
    # Enumerate the first possible integer band from the LOWER distance.
    m = math.isqrt(low)//S
    for k in (max(1, m), max(1, m)+1):
        if low <= (k*S+E)**2 and high >= (k*S-E)**2:
            return True
    return False


def interior_overlap(a, b):
    return a[0] < b[1] and b[0] < a[1] and a[2] < b[3] and b[2] < a[3]


def disjoint_rectangles(rectangles):
    events = []
    for i, (left, right, bottom, top) in enumerate(rectangles):
        events.extend(((left, 1, bottom, top, i), (right, 0, bottom, top, i)))
    active = []
    for x, add, bottom, top, i in sorted(events):
        item = (bottom, top, i)
        at = bisect_left(active, item)
        if not add:
            assert at < len(active) and active[at] == item
            active.pop(at)
        else:
            assert at == 0 or active[at-1][1] <= bottom
            assert at == len(active) or top <= active[at][0]
            insort(active, item)
    assert not active


def audit(path):
    d = json.loads(path.read_text())
    sources, generations = baseline(d)
    added = [tuple(map(F, r)) for r in d["added_rectangles"]]
    S = math.lcm(*(z.denominator for b in sources+added for z in b),
                 *(F(g["epsilon"]).denominator for g in d["groups"]))
    ints = [tuple(int(z*S) for z in box) for box in sources]
    total, cursor, exact_pairs, window_pairs, overlap_pairs = F(0), 0, 0, 0, 0
    groups = []
    for group in d["groups"]:
        assert group["first_rectangle"] == cursor and group["source_before_count"] == len(ints)
        j, digits = group["j"], group["digits"]
        k, n = params(j)
        assert len(digits) == n and all(0 <= v <= k-2 for v in digits)
        X = 2**j+sum(v*k**i for i, v in enumerate(digits))
        Y = 3*4**j+8*k*sum(v*k**(2*i) for i, v in enumerate(digits))
        assert group["center"] == [X, Y]
        xl, xr, yl, yr = map(F, group["offset_window"])
        eps = F(group["epsilon"])
        assert 0 <= eps < F(1, 2)
        assert (xr-xl)**2+(yr-yl)**2 < (1-eps)**2
        low, high = phase_bounds(X, Y, max(abs(xl), abs(xr))+F(1, 6),
                                  max(abs(yl), abs(yr))+F(1, 512), 2**14, F(1, 512))
        assert [str(low), str(high)] == group["tail_phase_bounds"]
        window = (F(X)+xl, F(X)+xr, F(Y)+yl, F(Y)+yr)
        iwindow = tuple(int(z*S) for z in window)
        E = int(eps*S)
        assert F(E, S) == eps
        ring_sources = [r for r in ints if forbidden(iwindow, r, S, E)]
        overlapping_sources = [r for r in ints if interior_overlap(iwindow, r)]
        window_pairs += len(ints)
        end = cursor+group["rectangle_count"]
        current = added[cursor:end]
        disjoint_rectangles(current)
        area = F(0)
        for box in current:
            assert X+xl <= box[0] < box[1] <= X+xr and Y+yl <= box[2] < box[3] <= Y+yr
            assert all((box[z]-((X, X, Y, Y)[z]))*group["grid_denominators"][z//2] ==
                       int((box[z]-((X, X, Y, Y)[z]))*group["grid_denominators"][z//2]) for z in range(4))
            assert low-(box[3]-Y) > eps and high-(box[2]-Y) < 1-eps
            ibox = tuple(int(z*S) for z in box)
            assert all(not forbidden(ibox, r, S, E) for r in ring_sources)
            assert all(not interior_overlap(ibox, r) for r in overlapping_sources)
            exact_pairs += len(ring_sources)
            overlap_pairs += len(overlapping_sources)
            area += (box[1]-box[0])*(box[3]-box[2])
        assert area == F(group["area_fraction"])
        groups.append({"round": group["round"], "j": j, "digits": digits, "rectangles": len(current),
            "area_fraction": str(area), "all_previous_sources_checked": len(ints),
            "ring_pairs_checked": len(current)*len(ring_sources),
            "all_future_scales_excluded": True})
        ints.extend(tuple(int(z*S) for z in box) for box in current)
        sources.extend(current)
        total += area
        cursor = end
        print(json.dumps(groups[-1]), flush=True)
    assert cursor == len(added) and total == F(d["added_area_fraction"])
    assert total+F(d["old_hole_area_fraction"]) == F(d["old_and_new_hole_area_fraction"])
    for round_ in d["rounds"]:
        actual = sum((F(g["area_fraction"]) for g in d["groups"] if g["round"] == round_["round"]), F(0))
        assert actual == F(round_["area_fraction"])
    report = {"certificate": path.name, "sha256": sha(path), "all_passed": True,
        "added_rectangles": len(added), "added_area_fraction": str(total),
        "old_and_new_hole_area_fraction": d["old_and_new_hole_area_fraction"],
        "window_source_interval_pairs_checked": window_pairs, "rectangle_source_ring_pairs_checked": exact_pairs,
        "rectangle_overlap_pairs_checked": overlap_pairs, "groups": groups,
        "all_positive_integer_radii_included": True, "all_future_scales_included": True,
        "method": "independent standard-library arbitrary-precision arithmetic and exact sweep disjointness",
        "source_baseline_hashes_verified": True, "lean_formalized": False,
        "new_asymptotic_order_proved": False, "finite_optimum_proved": False}
    outfile = HERE/f"{path.stem}-independent-audit.json"
    outfile.write_text(json.dumps(report, indent=2))
    return report


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("certificate")
    a = p.parse_args()
    report = audit(HERE/a.certificate)
    print(json.dumps({k: v for k, v in report.items() if k != "groups"}))
