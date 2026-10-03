"""Adaptive OUTER graphs for points avoiding a fixed delta-neighbourhood of Z.

An edge means EVERY distance between two closed leaves is strictly forbidden.
Each leaf has diameter < delta, so a robust set has at most one point per leaf.
The graph independence bound is a genuine robust-point upper bound at finite
resolution. It is not a continuous-area bound uniform over all delta.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import math
import time
import numpy as np
from numba import njit
from threadpoolctl import threadpool_limits
from erdos953_theta_cuts import propose, separate, cut_entries, Q, R

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


@njit(cache=True)
def forced(a, b, margin, denominator, kmax):
    x, y, s = a
    u, v, t = b
    dx = max(0, x-u-t, u-x-s)
    dy = max(0, y-v-t, v-y-s)
    lower = dx*dx+dy*dy
    dx = max(abs(x-u-t), abs(x+s-u))
    dy = max(abs(y-v-t), abs(y+s-v))
    upper = dx*dx+dy*dy
    if upper < margin*margin:
        return True
    for k in range(1, kmax+1):
        if lower > (k*denominator-margin)**2 and upper < (k*denominator+margin)**2:
            return True
    return False


@njit(cache=True)
def graph_array(boxes, margin, denominator, kmax):
    n = len(boxes)
    adj = np.zeros((n, n), dtype=np.bool_)
    for i in range(n):
        for j in range(i):
            adj[i, j] = adj[j, i] = forced(boxes[i], boxes[j], margin, denominator, kmax)
    return adj


@njit(cache=True)
def lookahead(boxes, adj, X, margin, denominator, kmax):
    scores = np.zeros(len(boxes))
    new_edges = np.zeros(len(boxes), dtype=np.int64)
    for i in range(len(boxes)):
        x, y, s = boxes[i]
        if s < 2:
            continue
        h = s//2
        for dx in (0, h):
            for dy in (0, h):
                child = np.array([x+dx, y+dy, h], dtype=np.int64)
                for j in range(len(boxes)):
                    if i != j and not adj[i, j] and forced(child, boxes[j], margin, denominator, kmax):
                        scores[i] += max(0.0, X[i, j])/4
                        new_edges[i] += 1
    return scores, new_edges


def children(box):
    x, y, s = box
    assert s >= 2 and s % 2 == 0
    h = s//2
    return [(x+dx, y+dy, h) for dx in (0, h) for dy in (0, h)]


def choose(boxes, scores, width, count):
    index = {tuple(b): i for i, b in enumerate(boxes)}
    groups = {}
    for i, (x, y, s) in enumerate(boxes):
        if s < 2:
            continue
        orbit = tuple(sorted({(x, y, s), (width-x-s, y, s),
                              (x, width-y-s, s), (width-x-s, width-y-s, s)}))
        assert all(b in index for b in orbit)
        groups[orbit] = sum(float(scores[index[b]]) for b in orbit)/len(orbit)
    picked = []
    for orbit, score in sorted(groups.items(), key=lambda pair: -pair[1]):
        if score <= 1e-12:
            break
        if len(picked)+len(orbit) <= count:
            picked.extend(orbit)
    return picked


def packing_capacity(rectangle, D, delta):
    x, y, w, h = rectangle
    width, height = F(w, D), F(h, D)
    micro = F(7, 10)*delta
    grid_bound = math.ceil(width/micro)*math.ceil(height/micro)
    pi_lower = F(314159, 100000)
    disk_bound = math.floor(1+4*width*height/(pi_lower*delta*delta)
                           +4*(width+height)/(pi_lower*delta))
    return min(grid_bound, disk_bound)


def spatial_cuts(M, delta, D, boxes, X, limit=150):
    """Valid for actual robust point occupancies, not all graph stable sets."""
    width = M*D
    side = int(delta*D)
    candidates = []
    while side <= width:
        stride = max(1, side//2)
        for x in range(0, width-side+1, stride):
            for y in range(0, width-side+1, stride):
                rectangle = [x, y, side, side]
                group = [i for i, (u, v, h) in enumerate(boxes)
                         if x <= u and u+h <= x+side and y <= v and v+h <= y+side]
                capacity = packing_capacity(rectangle, D, delta)
                if capacity < 2 or capacity >= len(group):
                    continue
                for anchor in group:
                    H = [u for u in group if u != anchor]
                    alpha = capacity-1
                    violation = 2*float(X[anchor, H].sum())-2*alpha*float(X[anchor, anchor])
                    if violation > 1e-9:
                        score = violation/math.sqrt(4*alpha*alpha+2*len(H))
                        candidates.append((score, {"kind": "spatial_capacity", "anchor": anchor,
                            "vertices": H, "alpha": alpha, "rectangle_units": rectangle,
                            "capacity": capacity, "proof": "delta-separated disk packing or strict-diameter microcover"}))
        side *= 2
    candidates.sort(key=lambda item: -item[0])
    return [c for score, c in candidates[:limit]], {"violated_spatial_candidates": len(candidates),
            "new_spatial_cuts": min(limit, len(candidates))}


def capacity_strengthen(M, delta, seconds=30):
    label = f"{delta.numerator}over{delta.denominator}"
    manifest = json.loads((HERE/f"erdos953-adaptive-outer-results-M{M}-d{label}-{STAMP}.json").read_text())
    last = max((r for r in manifest["results"] if r["tag"].startswith("adaptive")),
               key=lambda r: (r["vertices"], -F(r["alpha_upper_fraction"])))
    source = json.loads((HERE/last["certificate"]).read_text())
    boxes = [tuple(b) for b in source["leaves"]]
    D = source["coordinate_denominator"]
    rows, adj, X = solve_partition(M, delta, D, boxes, source["refinement_history"],
                                   "capacity-control", seconds/2, cut_rounds=0)
    K, mu, X, diagnostics = propose(adj, [], seconds/2)
    cuts, sep = spatial_cuts(M, delta, D, boxes, X)
    if cuts:
        K, mu, X, diagnostics = propose(adj, cuts, seconds, initial={"X": X, "K": K, "mu": mu})
        diagnostics.update(separation=sep)
        rows.append(certify(M, delta, D, boxes, source["refinement_history"], adj, K, cuts, mu,
                            "capacity-spatial", diagnostics))
    manifest["results"].extend(rows)
    manifest["best_robust_point_upper"] = min(r["robust_point_upper"] for r in manifest["results"])
    (HERE/f"erdos953-adaptive-outer-results-M{M}-d{label}-{STAMP}.json").write_text(json.dumps(manifest, indent=2))


def root_capacity_strengthen(M, delta, seconds=45):
    label = f"{delta.numerator}over{delta.denominator}"
    manifest_path = HERE/f"erdos953-adaptive-outer-results-M{M}-d{label}-{STAMP}.json"
    manifest = json.loads(manifest_path.read_text())
    last = max((r for r in manifest["results"] if r["tag"].startswith("adaptive")), key=lambda r: r["vertices"])
    source = json.loads((HERE/last["certificate"]).read_text())
    boxes, D = [tuple(b) for b in source["leaves"]], source["coordinate_denominator"]
    n = len(boxes)
    assert n < 512
    capacity = packing_capacity([0, 0, M*D, M*D], D, delta)
    adj = graph_array(np.array(boxes, dtype=np.int64), int(delta*D), D, math.ceil(math.sqrt(2)*M)+1)
    cuts = [{"kind": "spatial_capacity", "anchor": v,
        "vertices": [u for u in range(n) if u != v], "alpha": capacity-1,
        "rectangle_units": [0, 0, M*D, M*D], "capacity": capacity,
        "proof": "delta-separated disk packing or strict-diameter microcover"} for v in range(n)]
    mu = np.full(n, .5)
    K, X = np.zeros((n, n)), np.eye(n)/n
    rows = [certify(M, delta, D, boxes, source["refinement_history"], adj, K, cuts, mu,
                    "root-capacity-exact", {"source": "explicit analytic zero-Gram certificate"})]
    K, mu, X, diagnostics = propose(adj, cuts, seconds, initial={"X": X, "K": K, "mu": mu})
    rows.append(certify(M, delta, D, boxes, source["refinement_history"], adj, K, cuts, mu,
                        "root-capacity-sdp", diagnostics))
    manifest["results"].extend(rows)
    manifest["best_robust_point_upper"] = min(r["robust_point_upper"] for r in manifest["results"])
    manifest_path.write_text(json.dumps(manifest, indent=2))


def certify(M, delta, denominator, boxes, history, adj, K, cuts, mu, tag, diagnostics):
    n = len(boxes)
    multipliers = np.maximum(0, np.rint(mu*Q)).astype(np.int64)
    correction = np.zeros((n, n), dtype=np.int64)
    active = []
    for cut, weight in zip(cuts, multipliers):
        if weight:
            for idx, value in cut_entries(cut, n).items():
                correction.ravel()[idx] += int(weight)*value
            active.append({**cut, "multiplier_numerator": int(weight)})
    units = np.rint((K+K.T)*Q/2).astype(np.int64)
    nonedge = ~adj & ~np.eye(n, dtype=bool)
    units[nonedge] = np.minimum(units[nonedge], correction[nonedge]-Q)
    matrix = units.astype(float)/Q
    shift = max(1e-5, -float(np.linalg.eigvalsh(matrix)[0])+1e-5)
    L = np.linalg.cholesky(matrix+shift*np.eye(n))
    lint = np.rint(L*R).astype(np.int64)
    assert n*int(np.max(np.abs(lint)))**2 < 2**62
    residual = units*(R*R//Q)-lint@lint.T
    diagonal = np.diag(residual).copy()
    offsum = np.sum(np.abs(residual), axis=1)-np.abs(diagonal)
    gamma = max(0, int(np.max(offsum-diagonal)))+1
    assert np.all(diagonal+gamma >= offsum)
    bound = 1+F(int(np.max(np.diag(units-correction))), Q)+F(gamma, R*R)
    upper = bound.__floor__()
    delta_label = f"{delta.numerator}over{delta.denominator}"
    filename = f"erdos953-adaptive-outer-M{M}-d{delta_label}-{tag}-{STAMP}.json"
    cert = {"kind": "adaptive_robust_point_outer_upper", "M": M,
        "delta_fraction": str(delta), "coordinate_denominator": denominator,
        "leaves": [list(b) for b in boxes], "refinement_history": history,
        "vertices": n, "tag": tag, "cuts": active,
        "matrix_denominator": Q, "matrix_units": units.tolist(),
        "multiplier_denominator": Q, "gram_denominator": R,
        "gram_factor_units": lint.tolist(), "diagonal_shift_numerator": gamma,
        "diagonal_shift_denominator": R*R, "alpha_upper_fraction": str(bound),
        "robust_point_upper": upper, "delta_squared_point_upper_fraction": str(delta*delta*upper),
        "finite_delta_point_upper_proved": True, "continuous_area_upper_proved": False,
        "uniform_over_delta_proved": False, "new_asymptotic_order_proved": False,
        "optimizer_optimality_proved": False, "lean_formalized": False,
        "diagnostics": diagnostics}
    (HERE/filename).write_text(json.dumps(cert, separators=(",", ":")), encoding="utf-8")
    brief = {k: v for k, v in cert.items() if k not in
             ("leaves", "cuts", "matrix_units", "gram_factor_units", "refinement_history")}
    brief.update(certificate=filename, active_cuts=len(active),
        leaf_side_fractions=sorted({str(F(b[2], denominator)) for b in boxes}, key=F))
    print(json.dumps(brief), flush=True)
    return brief


def solve_partition(M, delta, D, boxes, history, tag, seconds, cut_rounds=1):
    margin = int(delta*D)
    assert F(margin, D) == delta and all(2*b[2]**2 < margin**2 for b in boxes)
    adj = graph_array(np.array(boxes, dtype=np.int64), margin, D, math.ceil(math.sqrt(2)*M)+1)
    cuts = []
    K, mu, X, diagnostics = propose(adj, [], seconds)
    rows = [certify(M, delta, D, boxes, history, adj, K, [], mu, tag+"-plain", diagnostics)]
    # Adaptive indices have no square-grid symmetry; keep cuts below 512 leaves.
    if len(boxes) < 512:
        for r in range(cut_rounds):
            added, sep = separate(adj, X, cuts, limit=100, seed=953+r)
            if not added:
                break
            cuts.extend(added)
            K, mu, X, diagnostics = propose(adj, cuts, seconds,
                                            initial={"X": X, "K": K, "mu": mu})
            diagnostics.update(separation=sep)
            rows.append(certify(M, delta, D, boxes, history, adj, K, cuts, mu,
                                tag+f"-cut{r+1}", diagnostics))
    return rows, adj, X


def run(M, delta, seconds=12, steps=3, budget=448, uniform_control=False):
    D = 128
    margin = delta*D
    assert margin.denominator == 1 and margin.numerator % 2 == 0 and 0 < delta < F(1, 2)
    base = margin.numerator//2
    width = M*D
    assert width % base == 0
    boxes = [(x, y, base) for x in range(0, width, base) for y in range(0, width, base)]
    initial = boxes.copy()
    history = []
    rows = []
    for step in range(steps+1):
        current, adj, X = solve_partition(M, delta, D, boxes, history.copy(),
                                         f"adaptive{step}", seconds)
        rows.extend(current)
        if step == steps or len(boxes)+12 > budget:
            break
        scores, new_edges = lookahead(np.array(boxes, dtype=np.int64), adj, X,
                                     margin.numerator, D, math.ceil(math.sqrt(2)*M)+1)
        count = min(32 if len(boxes) < 256 else 16, (budget-len(boxes))//3)
        picked = choose(boxes, scores, width, count)
        if not picked:
            break
        marked = set(picked)
        history.append({"refined_boxes": [list(b) for b in picked],
            "selection_rule": "fractional-correlation weighted lookahead at integer annulus boundaries",
            "sum_score_diagnostic": sum(float(scores[boxes.index(b)]) for b in picked),
            "potential_new_child_edges": sum(int(new_edges[boxes.index(b)]) for b in picked)})
        boxes = sorted([b for b in boxes if b not in marked]+[c for b in picked for c in children(b)])
    if uniform_control:
        control = sorted(c for b in initial for c in children(b))
        if len(control) <= 1024:
            control_history = [{"refined_boxes": [list(b) for b in initial], "selection_rule": "uniform control"}]
            current, adj, X = solve_partition(M, delta, D, control, control_history,
                                             "uniform1", seconds*2, cut_rounds=1)
            rows.extend(current)
    result = {"M": M, "delta_fraction": str(delta), "results": rows,
        "best_robust_point_upper": min(r["robust_point_upper"] for r in rows),
        "scope": "fixed-delta robust point upper bounds; no continuous area upper or new order claimed"}
    label = f"{delta.numerator}over{delta.denominator}"
    (HERE/f"erdos953-adaptive-outer-results-M{M}-d{label}-{STAMP}.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--M", type=int, required=True)
    p.add_argument("--delta", required=True)
    p.add_argument("--seconds", type=float, default=12)
    p.add_argument("--steps", type=int, default=3)
    p.add_argument("--budget", type=int, default=448)
    p.add_argument("--uniform-control", action="store_true")
    p.add_argument("--capacity-strengthen", action="store_true")
    p.add_argument("--root-capacity", action="store_true")
    a = p.parse_args()
    with threadpool_limits(limits=1):
        if a.root_capacity:
            root_capacity_strengthen(a.M, F(a.delta), a.seconds)
        elif a.capacity_strengthen:
            capacity_strengthen(a.M, F(a.delta), a.seconds)
        else:
            run(a.M, F(a.delta), a.seconds, a.steps, a.budget, a.uniform_control)
