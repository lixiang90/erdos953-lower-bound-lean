"""Independent exact audit of removals, replacements and generation floors."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
from verify_953_iterated_ring_holes import baseline, forbidden, interior_overlap
from verify_953_infinite_ring_extension import params, phase_bounds

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def sources_from_input(path):
    d = json.loads(path.read_text())
    audit = json.loads(path.with_name(path.stem+"-independent-audit.json").read_text())
    assert audit["all_passed"] and audit["sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
    boxes, labels = baseline(d)
    for g in d["groups"]:
        a, b = g["first_rectangle"], g["first_rectangle"]+g["rectangle_count"]
        boxes.extend(tuple(map(F, box)) for box in d["added_rectangles"][a:b])
        labels.extend([g["j"]]*(b-a))
    return boxes, labels


def audit(path):
    d = json.loads(path.read_text())
    input_path = HERE/d["input_certificate"]
    assert hashlib.sha256(input_path.read_bytes()).hexdigest() == d["input_sha256"]
    boxes, labels = sources_from_input(input_path)
    assert len(boxes) == d["initial_components_including_base_enclosure"]
    area = [F(0) if i == 0 else (b[1]-b[0])*(b[3]-b[2]) for i, b in enumerate(boxes)]
    by_gen = {j: sum((a for a, l in zip(area, labels) if l == j), F(0)) for j in range(6, 14)}
    assert {str(j): str(a) for j, a in by_gen.items()} == d["generation_areas_before"]
    floors = {j: F((params(j)[0]-1)**params(j)[1], 108*params(j)[0]**3) for j in range(6, 14)}
    assert {str(j): str(a) for j, a in floors.items()} == d["uniform_generation_floors"]
    eps = F(d["epsilon"])
    new = [tuple(map(F, o["added_rectangle"])) for o in d["operations"]]
    S = math.lcm(eps.denominator, *(z.denominator for b in boxes+new for z in b))
    ints = [tuple(int(z*S) for z in b) for b in boxes]
    E = int(eps*S)
    active = set(range(len(boxes)))
    gain, operations, pairs = F(0), [], 0
    for op, box in zip(d["operations"], new):
        j, digits = op["j"], op["digits"]
        k, n = params(j)
        assert len(digits) == n and all(0 <= a <= k-2 for a in digits)
        X = 2**j+sum(a*k**i for i, a in enumerate(digits))
        Y = 3*4**j+8*k*sum(a*k**(2*i) for i, a in enumerate(digits))
        assert op["center"] == [X, Y]
        assert X-F(2, 5) <= box[0] < box[1] <= X+F(2, 5)
        assert Y-F(1, 8) <= box[2] < box[3] <= Y+F(1, 8)
        assert (box[1]-box[0])**2+(box[3]-box[2])**2 < (1-eps)**2
        radius = 4**(j+1)
        assert max(box[0]**2, box[1]**2)+max(box[2]**2, box[3]**2) < radius*radius
        low, high = phase_bounds(X, Y, F(2, 5)+F(1, 6), F(1, 8)+F(1, 512), 2**14, F(1, 512))
        assert [str(low), str(high)] == op["tail_phase_bounds"]
        assert low-(box[3]-Y) > eps and high-(box[2]-Y) < 1-eps
        r = tuple(int(z*S) for z in box)
        removed = sorted(i for i in active if forbidden(r, ints[i], S, E) or interior_overlap(r, ints[i]))
        pairs += len(active)
        assert removed == op["removed_ids"] and 0 not in removed
        if not op["allowed_to_remove_original_digital_blocks"]:
            assert not any(0 < i < 2703 for i in removed)
        cost = sum((area[i] for i in removed), F(0))
        added_area = (box[1]-box[0])*(box[3]-box[2])
        profit = added_area-cost
        assert profit > 0 and cost == F(op["removed_area_fraction"])
        assert added_area == F(op["added_area_fraction"]) and profit == F(op["net_gain_fraction"])
        for i in removed:
            by_gen[labels[i]] -= area[i]
            active.remove(i)
        assert op["added_id"] == len(boxes)
        active.add(len(boxes))
        boxes.append(box)
        ints.append(r)
        labels.append(j)
        area.append(added_area)
        by_gen[j] += added_area
        assert all(by_gen[t] >= floors[t] for t in floors)
        assert {str(t): str(a) for t, a in by_gen.items()} == op["generation_areas_after"]
        gain += profit
        operations.append({"step": op["step"], "removed_components": len(removed),
            "original_digital_rectangles_removed": sum(0 < i < 2703 for i in removed),
            "added_area_fraction": str(added_area), "removed_area_fraction": str(cost),
            "net_gain_fraction": str(profit), "all_finite_sources_checked": pairs,
            "all_future_scales_excluded": True, "all_uniform_generation_floors_retained": True})
    assert gain == F(d["net_gain_fraction"])
    assert sorted(active) == d["active_component_ids"]
    report = {"certificate": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "all_passed": True, "operations": operations, "net_gain_fraction": str(gain),
        "exact_candidate_active_source_pairs": pairs, "active_components": len(active),
        "all_integer_distances_excluded": True, "all_future_scales_included": True,
        "all_uniform_generation_floors_retained": True, "uniform_all_R_lower_coefficient": "1/55296",
        "method": "independent standard-library exact arithmetic plus subset/deletion inheritance",
        "full_lean_formalization": False, "new_asymptotic_order_proved": False,
        "finite_optimum_proved": False}
    path.with_name(path.stem+"-independent-audit.json").write_text(json.dumps(report, indent=2))
    print(json.dumps(report))
    return report


if __name__ == "__main__":
    audit(HERE/f"erdos953-ring-exchange-{STAMP}.json")
