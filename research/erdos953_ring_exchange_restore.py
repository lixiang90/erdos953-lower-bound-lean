"""Restore safe portions of removed INITIAL blocks after rectangle exchanges."""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import hashlib
from erdos953_ring_exchange import initial_sources
from erdos953_iterated_ring_holes import conflict, overlap

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def shadowed(r, target, S, E):
    # A point of r has a distance interval to target. If one integer band
    # lies in EVERY such interval, no point of r can be restored robustly.
    maxmin = 0
    minmax4 = 0
    for l, h, L, H in ((r[0], r[1], target[0], target[1]), (r[2], r[3], target[2], target[3])):
        maxmin += max(0, L-l, h-H)**2
        gap2 = max(2*l-L-H, L+H-2*h, 0)
        minmax4 += (gap2+H-L)**2
    m = math.isqrt(maxmin)//S
    return any(maxmin <= (k*S+E)**2 and minmax4 >= 4*(k*S-E)**2
               for k in (max(1, m), max(1, m)+1))


def crop(r, targets, S, E, depth, path=""):
    blockers = [t for t in targets if conflict(r, t, S, E) or overlap(r, t)]
    if not blockers:
        return [(r, path)]
    if depth == 0 or any((t[0] <= r[0] and r[1] <= t[1] and t[2] <= r[2] and r[3] <= t[3])
                         or shadowed(r, t, S, E) for t in blockers):
        return []
    uncertainty = [0, 0]
    for t in blockers:
        for axis, (l, h, L, H) in enumerate(((r[0], r[1], t[0], t[1]), (r[2], r[3], t[2], t[3]))):
            near = max(0, L-h, l-H)
            far = max(abs(l-H), abs(h-L))
            uncertainty[axis] += far*far-near*near
    axis = 0 if uncertainty[0] >= uncertainty[1] else 1
    low, high = axis*2, axis*2+1
    midpoint = (r[low]+r[high])//2
    assert 2*midpoint == r[low]+r[high]
    left, right = list(r), list(r)
    left[high], right[low] = midpoint, midpoint
    return crop(tuple(left), blockers, S, E, depth-1, path+f"{axis}L")+crop(tuple(right), blockers, S, E, depth-1, path+f"{axis}R")


def run(depth=12):
    path = HERE/f"erdos953-ring-exchange-{STAMP}.json"
    exchange = json.loads(path.read_text())
    source_path = HERE/exchange["input_certificate"]
    sources, labels = initial_sources(source_path)
    initial_count = len(sources)
    active = set(exchange["active_component_ids"])
    removed = sorted({i for op in exchange["operations"] for i in op["removed_ids"] if i < initial_count and i not in active})
    target_boxes = [tuple(map(F, op["added_rectangle"])) for op in exchange["operations"] if op["added_id"] in active]
    eps = F(exchange["epsilon"])
    S = math.lcm(eps.denominator, *(z.denominator for r in sources+target_boxes for z in r))*2**depth
    E = int(eps*S)
    targets = [tuple(int(z*S) for z in r) for r in target_boxes]
    groups = []
    area = F(0)
    for i in removed:
        r = tuple(int(z*S) for z in sources[i])
        pieces = crop(r, targets, S, E, depth)
        recovered = sum((F((b[1]-b[0])*(b[3]-b[2]), S*S) for b, p in pieces), F(0))
        groups.append({"source_id": i, "generation": labels[i], "source_box": [str(z) for z in sources[i]],
            "retained_pieces": [{"box": [str(F(z, S)) for z in b], "split_path": p} for b, p in pieces],
            "retained_area_fraction": str(recovered)})
        area += recovered
    cost = sum((F(o["removed_area_fraction"]) for o in exchange["operations"]), F(0))
    payload = {"exchange_certificate": path.name, "exchange_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "input_certificate": source_path.name, "input_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
        "split_depth": depth, "epsilon_against_active_new_targets": str(eps), "groups": groups,
        "restored_area_fraction": str(area), "original_whole_removal_cost_fraction": str(cost),
        "final_deleted_area_fraction": str(cost-area),
        "whole_exchange_net_gain_fraction": exchange["net_gain_fraction"],
        "exchange_plus_restoration_net_gain_fraction": str(F(exchange["net_gain_fraction"])+area),
        "safety_against_other_old_components": "each retained piece is a subset of a removed initial component; all initial components mutually compatible",
        "future_safety": "inherited from the corresponding certified initial source component",
        "all_uniform_generation_floors_retained": True, "uniform_all_R_lower_coefficient": "1/55296",
        "full_lean_formalization": False, "new_asymptotic_order_proved": False, "finite_optimum_proved": False}
    (HERE/f"erdos953-ring-exchange-restoration-{STAMP}.json").write_text(json.dumps(payload, indent=2))
    print(json.dumps({k: v for k, v in payload.items() if k != "groups"}))


if __name__ == "__main__":
    run()
