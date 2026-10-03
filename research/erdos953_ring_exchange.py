"""Area-positive rectangle exchanges after certified full-annulus filling.

Floating conflict matrices rank candidates only. Before each accepted exchange,
the entire active finite set is checked with arbitrary-precision integer
distance intervals, the future-tail phase enclosure is checked, and each
modified generation retains at least its previously proved uniform area.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import math
import numpy as np
from scipy.sparse import coo_matrix, csr_matrix, hstack
from erdos953_all_ring_hole_extension import load_sources
from erdos953_square_limit_construction import parameters, center
from erdos953_iterated_ring_holes import conflict, overlap, tail_bounds, windows_for

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
EPS = F(1, 32768)
OFFSETS = (F(-2, 5), F(2, 5), F(-1, 8), F(1, 8))


def initial_sources(input_path):
    d = json.loads(input_path.read_text())
    base, _ = load_sources()
    labels = [None]
    for j in range(6, 14):
        k, n = parameters(j)
        labels.extend([j]*(k-1)**n)
    old = json.loads((HERE/d["old_hole_certificate"]).read_text())
    base.extend(tuple(map(F, r)) for r in old["added_rectangles"])
    labels.extend([6]*len(old["added_rectangles"]))
    assert len(base) == d["baseline_source_rectangles_with_base_enclosure"]
    for g in d["groups"]:
        first, stop = g["first_rectangle"], g["first_rectangle"]+g["rectangle_count"]
        base.extend(tuple(map(F, r)) for r in d["added_rectangles"][first:stop])
        labels.extend([g["j"]]*(stop-first))
    assert len(base) == len(labels)
    return base, labels


def template_windows():
    result = [(6, ds, xy) for ds, xy in windows_for(6, full=True)]
    result += [(7, ds, xy) for ds, xy in windows_for(7, full=True)]
    for j in range(8, 14):
        result += [(j, ds, xy) for ds, xy in windows_for(j)]
    return result


def templates():
    candidates, groups = [], []
    for j, ds, (X, Y) in template_windows():
        first = len(candidates)
        low, high = tail_bounds(X, Y, OFFSETS)
        for width in (F(1, 5), F(2, 5), F(3, 5), F(4, 5)):
            for height in (F(1, 128), F(1, 64), F(1, 32), F(1, 16), F(1, 8)):
                for u in (F(v, 10) for v in range(-3, 4)):
                    if not OFFSETS[0] <= u-width/2 < u+width/2 <= OFFSETS[1]:
                        continue
                    for v in (F(t, 32) for t in range(-3, 4)):
                        bottom, top = v-height/2, v+height/2
                        if not OFFSETS[2] <= bottom < top <= OFFSETS[3]:
                            continue
                        if not low-top > EPS or not high-bottom < 1-EPS:
                            continue
                        box = (F(X)+u-width/2, F(X)+u+width/2, F(Y)+bottom, F(Y)+top)
                        candidates.append({"j": j, "digits": ds, "center": [X, Y], "box": box,
                            "area": width*height, "tail_phase_bounds": [str(low), str(high)]})
        last = len(candidates)
        groups.append({"j": j, "X": X, "Y": Y, "first": first, "last": last,
            "offsets": np.array([[float(b["box"][0]-X), float(b["box"][1]-X),
                                  float(b["box"][2]-Y), float(b["box"][3]-Y)] for b in candidates[first:last]])})
    return candidates, groups


def float_conflicts(box, group):
    if group["last"] == group["first"]:
        return np.zeros(0, dtype=bool)
    X, Y, A = group["X"], group["Y"], group["offsets"]
    ul, ur, vl, vr = A.T
    left, right, bottom, top = box
    l, r = float(left-X), float(right-X)
    sy = round((bottom+top)/2)
    a, sb, st = sy-Y, float(bottom-sy), float(top-sy)
    intersects = (ur > l) & (ul < r) & (vr > float(bottom-Y)) & (vl < float(top-Y))
    dx = np.maximum(np.maximum(l-ur, ul-r), 0)
    farx = np.maximum(np.abs(ul-r), np.abs(ur-l))
    if bottom >= F(Y)+OFFSETS[3]:
        dlo, dhi = sb-vr, st-vl
        ylo, yhi = a+dlo, a+dhi
        lo = dlo+dx*dx/(np.sqrt(ylo*ylo+dx*dx)+ylo)
        hi = dhi+farx*farx/(np.sqrt(yhi*yhi+farx*farx)+yhi)
        forbidden = np.floor(hi+float(EPS)+1e-11) >= np.ceil(lo-float(EPS)-1e-11)
    elif top <= F(Y)+OFFSETS[2]:
        dlo, dhi = vl-st, vr-sb
        ylo, yhi = -a+dlo, -a+dhi
        lo = dlo+dx*dx/(np.sqrt(ylo*ylo+dx*dx)+ylo)
        hi = dhi+farx*farx/(np.sqrt(yhi*yhi+farx*farx)+yhi)
        forbidden = np.floor(hi+float(EPS)+1e-11) >= np.ceil(lo-float(EPS)-1e-11)
    else:
        dy = np.maximum(np.maximum(float(bottom-Y)-vr, vl-float(top-Y)), 0)
        fary = np.maximum(np.abs(vl-float(top-Y)), np.abs(vr-float(bottom-Y)))
        lo, hi = np.sqrt(dx*dx+dy*dy), np.sqrt(farx*farx+fary*fary)
        first = np.maximum(1, np.ceil(lo-float(EPS)-1e-11))
        forbidden = first <= hi+float(EPS)+1e-11
    return intersects | forbidden


def build_matrix(sources, candidates, groups, S):
    rr, cc = [], []
    E = int(EPS*S)
    integer = [tuple(int(z*S) for z in b) for b in sources]
    for group in groups:
        X, Y = group["X"], group["Y"]
        win = tuple(int(z*S) for z in (F(X)+OFFSETS[0], F(X)+OFFSETS[1], F(Y)+OFFSETS[2], F(Y)+OFFSETS[3]))
        for i, r in enumerate(integer):
            if not conflict(win, r, S, E) and not overlap(win, r):
                continue
            hit = np.flatnonzero(float_conflicts(sources[i], group))
            if len(hit):
                rr.append(hit+group["first"])
                cc.append(np.full(len(hit), i, dtype=np.int32))
        print(json.dumps({"matrix_window_j": group["j"], "center": [X, Y],
                          "candidates": group["last"]-group["first"]}), flush=True)
    if not rr:
        return csr_matrix((len(candidates), len(sources)), dtype=np.int8)
    rows, cols = np.concatenate(rr), np.concatenate(cc)
    return coo_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(len(candidates), len(sources))).tocsr()


def run(input_name, steps=8):
    input_path = HERE/input_name
    sources, labels = initial_sources(input_path)
    candidates, groups = templates()
    initial_count = len(sources)
    S = math.lcm(EPS.denominator, *(z.denominator for b in sources for z in b),
                 *(z.denominator for c in candidates for z in c["box"]))
    matrix = build_matrix(sources, candidates, groups, S)
    active = np.ones(len(sources), dtype=bool)
    area = [F(0) if i == 0 else (b[1]-b[0])*(b[3]-b[2]) for i, b in enumerate(sources)]
    floors = {j: F((parameters(j)[0]-1)**parameters(j)[1], 108*parameters(j)[0]**3) for j in range(6, 14)}
    by_generation = {j: sum((v for v, label in zip(area, labels) if label == j), F(0)) for j in floors}
    totals_before = {j: str(v) for j, v in by_generation.items()}
    E, excluded = int(EPS*S), set()
    certificate = {"input_certificate": input_name, "input_sha256": hashlib.sha256(input_path.read_bytes()).hexdigest(),
        "initial_components_including_base_enclosure": initial_count, "epsilon": str(EPS),
        "operations": [], "net_gain_fraction": "0", "generation_areas_before": totals_before,
        "uniform_generation_floors": {j: str(v) for j, v in floors.items()},
        "finite_prefix_last": 13, "analytic_tail_first": 14,
        "curved_base_kept": True, "all_future_original_tail_components_kept": True,
        "retains_uniform_all_R_lower_coefficient": "1/55296",
        "full_lean_formalization": False, "new_asymptotic_order_proved": False,
        "finite_optimum_proved": False, "candidate_count": len(candidates)}
    gain = F(0)
    for step in range(steps):
        weights = np.array([float(v) for v in area])*active
        score = np.array([float(c["area"]) for c in candidates])-matrix.dot(weights)
        protected = np.zeros(len(sources), dtype=np.int32)
        protected[0] = int(active[0])
        # First half explores replacing only supplemental holes; later steps may
        # also remove finite digital rectangles, subject to generation floors.
        if step < steps//2:
            protected[1:2703] = active[1:2703]
        score[matrix.dot(protected) > 0] = -np.inf
        if excluded:
            score[list(excluded)] = -np.inf
        accepted = None
        for idx in np.argsort(score)[::-1][:100]:
            if score[idx] <= 0:
                break
            candidate = candidates[int(idx)]
            r = tuple(int(z*S) for z in candidate["box"])
            removed = [i for i, b in enumerate(sources) if active[i] and
                       (conflict(r, tuple(int(z*S) for z in b), S, E) or overlap(r, tuple(int(z*S) for z in b)))]
            if 0 in removed or (step < steps//2 and any(0 < i < 2703 for i in removed)):
                excluded.add(int(idx))
                continue
            cost = sum((area[i] for i in removed), F(0))
            profit = candidate["area"]-cost
            after = by_generation.copy()
            for i in removed:
                after[labels[i]] -= area[i]
            after[candidate["j"]] += candidate["area"]
            if profit <= 0 or any(after[j] < floors[j] for j in floors):
                excluded.add(int(idx))
                continue
            accepted = int(idx), candidate, removed, cost, profit, after
            break
        if accepted is None:
            print(json.dumps({"step": step, "no_positive_certified_exchange_found": True}), flush=True)
            continue
        idx, candidate, removed, cost, profit, after = accepted
        new_id = len(sources)
        for i in removed:
            active[i] = False
        sources.append(candidate["box"])
        labels.append(candidate["j"])
        area.append(candidate["area"])
        active = np.r_[active, True]
        col = np.zeros(len(candidates), dtype=np.int8)
        for group in groups:
            col[group["first"]:group["last"]] = float_conflicts(candidate["box"], group)
        matrix = hstack((matrix, csr_matrix(col.reshape(-1, 1))), format="csr")
        operation = {"step": step, "j": candidate["j"], "digits": candidate["digits"],
            "center": candidate["center"], "added_rectangle": [str(z) for z in candidate["box"]],
            "added_id": new_id, "added_area_fraction": str(candidate["area"]),
            "removed_ids": removed, "removed_area_fraction": str(cost), "net_gain_fraction": str(profit),
            "original_digital_rectangles_removed": sum(0 < i < 2703 for i in removed),
            "tail_phase_bounds": candidate["tail_phase_bounds"],
            "generation_areas_after": {j: str(v) for j, v in after.items()},
            "allowed_to_remove_original_digital_blocks": step >= steps//2}
        gain += profit
        by_generation = after
        certificate["operations"].append(operation)
        certificate["net_gain_fraction"] = str(gain)
        certificate["generation_areas_after"] = operation["generation_areas_after"]
        certificate["active_component_ids"] = np.flatnonzero(active).tolist()
        (HERE/f"erdos953-ring-exchange-{STAMP}.json").write_text(json.dumps(certificate, indent=2))
        print(json.dumps({k: v for k, v in operation.items() if k not in ("removed_ids", "generation_areas_after")}), flush=True)
    return certificate


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("input_certificate")
    p.add_argument("--steps", type=int, default=8)
    a = p.parse_args()
    run(a.input_certificate, a.steps)
