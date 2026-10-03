"""Independent subset-lineage and integer-annulus audit of local cropping."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
from verify_953_ring_exchange import sources_from_input
from verify_953_iterated_ring_holes import forbidden, interior_overlap, disjoint_rectangles

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def audit(path):
    d = json.loads(path.read_text())
    exchange_path = HERE/d["exchange_certificate"]
    assert hashlib.sha256(exchange_path.read_bytes()).hexdigest() == d["exchange_sha256"]
    ex_audit = json.loads(exchange_path.with_name(exchange_path.stem+"-independent-audit.json").read_text())
    assert ex_audit["all_passed"] and ex_audit["sha256"] == d["exchange_sha256"]
    exchange = json.loads(exchange_path.read_text())
    input_path = HERE/d["input_certificate"]
    assert hashlib.sha256(input_path.read_bytes()).hexdigest() == d["input_sha256"] == exchange["input_sha256"]
    initial, labels = sources_from_input(input_path)
    active = set(exchange["active_component_ids"])
    removed = sorted({i for op in exchange["operations"] for i in op["removed_ids"] if i < len(initial) and i not in active})
    assert [g["source_id"] for g in d["groups"]] == removed and 0 not in removed
    targets = [tuple(map(F, op["added_rectangle"])) for op in exchange["operations"] if op["added_id"] in active]
    pieces = [tuple(map(F, piece["box"])) for g in d["groups"] for piece in g["retained_pieces"]]
    eps = F(d["epsilon_against_active_new_targets"])
    assert eps == F(exchange["epsilon"])
    S = math.lcm(eps.denominator, *(z.denominator for b in targets+pieces for z in b))
    E = int(eps*S)
    itargets = [tuple(int(z*S) for z in b) for b in targets]
    area = F(0)
    by_gen = {int(j): F(a) for j, a in exchange["generation_areas_after"].items()}
    total_pieces = 0
    for group in d["groups"]:
        i = group["source_id"]
        parent = initial[i]
        assert group["generation"] == labels[i]
        assert tuple(map(F, group["source_box"])) == parent
        kept = []
        subtotal = F(0)
        for piece in group["retained_pieces"]:
            path_ = piece["split_path"]
            assert len(path_) % 2 == 0 and len(path_) <= 2*d["split_depth"]
            replayed = list(parent)
            for z in range(0, len(path_), 2):
                axis, side = int(path_[z]), path_[z+1]
                assert axis in (0, 1) and side in "LR"
                lo, hi = axis*2, axis*2+1
                midpoint = (replayed[lo]+replayed[hi])/2
                replayed[hi if side == "L" else lo] = midpoint
            box = tuple(map(F, piece["box"]))
            assert box == tuple(replayed)
            assert parent[0] <= box[0] < box[1] <= parent[1]
            assert parent[2] <= box[2] < box[3] <= parent[3]
            r = tuple(int(z*S) for z in box)
            assert all(not forbidden(r, t, S, E) and not interior_overlap(r, t) for t in itargets)
            subtotal += (box[1]-box[0])*(box[3]-box[2])
            kept.append(box)
        disjoint_rectangles(kept)
        assert subtotal == F(group["retained_area_fraction"])
        assert subtotal <= (parent[1]-parent[0])*(parent[3]-parent[2])
        by_gen[labels[i]] += subtotal
        area += subtotal
        total_pieces += len(kept)
    assert area == F(d["restored_area_fraction"])
    removed_cost = sum((F(op["removed_area_fraction"]) for op in exchange["operations"]), F(0))
    assert removed_cost == F(d["original_whole_removal_cost_fraction"])
    assert removed_cost-area == F(d["final_deleted_area_fraction"])
    assert F(exchange["net_gain_fraction"])+area == F(d["exchange_plus_restoration_net_gain_fraction"])
    assert all(by_gen[int(j)] >= F(a) for j, a in exchange["uniform_generation_floors"].items())
    report = {"certificate": path.name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "all_passed": True, "removed_initial_components": len(removed), "restored_pieces": total_pieces,
        "restored_area_fraction": str(area), "final_deleted_area_fraction": d["final_deleted_area_fraction"],
        "exchange_plus_restoration_net_gain_fraction": d["exchange_plus_restoration_net_gain_fraction"],
        "generation_areas_after": {j: str(a) for j, a in by_gen.items()},
        "all_integer_distances_excluded": True, "all_future_scales_included": True,
        "all_uniform_generation_floors_retained": True, "uniform_all_R_lower_coefficient": "1/55296",
        "method": "independent split-path reconstruction, sweep disjointness, exact target annuli, and certified subset inheritance",
        "full_lean_formalization": False, "new_asymptotic_order_proved": False, "finite_optimum_proved": False}
    path.with_name(path.stem+"-independent-audit.json").write_text(json.dumps(report, indent=2))
    print(json.dumps(report))
    return report


if __name__ == "__main__":
    audit(HERE/f"erdos953-ring-exchange-restoration-{STAMP}.json")
