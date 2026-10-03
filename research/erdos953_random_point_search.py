"""Random-point independent-set search for small-radius distance avoidance.

The optimized training fraction is NOT a proved area or an upper bound on M(R).
Two continuous reconstructions are reported separately: epsilon/2 disk unions
(measured on an independent test sample), and convex polygons whose rational
coordinates are independently checked by verify_953_random_polygons.py.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
from numba import njit
from scipy.spatial import ConvexHull, cKDTree
from scipy.spatial.distance import cdist
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from scipy.optimize import milp, Bounds, LinearConstraint
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Polygon

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def uniform_disk(n, R, rng):
    angle = rng.uniform(0, 2 * math.pi, n)
    radius = R * np.sqrt(rng.random(n))
    return np.column_stack((radius * np.cos(angle), radius * np.sin(angle)))


def conflict_graph(points, epsilon, forbidden):
    """Exhaustive pair testing, in small matrix blocks (no neighbor truncation)."""
    n = len(points)
    rows, cols = [], []
    for start in range(0, n, 128):
        stop = min(start + 128, n)
        dist = cdist(points[start:stop], points)
        bad = np.zeros(dist.shape, dtype=bool)
        for k in forbidden:
            bad |= np.abs(dist - k) <= epsilon + 1e-12
        rr, cc = np.nonzero(bad)
        rr += start
        keep = rr < cc
        rows.append(rr[keep].astype(np.int32))
        cols.append(cc[keep].astype(np.int32))
    row = np.concatenate(rows)
    col = np.concatenate(cols)
    graph = coo_matrix((np.ones(2 * len(row), dtype=np.int8),
                        (np.r_[row, col], np.r_[col, row])), shape=(n, n)).tocsr()
    graph.sort_indices()
    return graph, row, col


@njit(cache=True)
def greedy(indptr, indices, order, initial):
    chosen = initial.copy()
    blocked = np.zeros(len(chosen), dtype=np.int32)
    for v in range(len(chosen)):
        if chosen[v]:
            for e in range(indptr[v], indptr[v + 1]):
                blocked[indices[e]] += 1
    for v in order:
        if not chosen[v] and blocked[v] == 0:
            chosen[v] = True
            for e in range(indptr[v], indptr[v + 1]):
                blocked[indices[e]] += 1
    return chosen


@njit(cache=True)
def local_search(indptr, indices, initial, seed, sweeps):
    """Hard-core local swaps with annealing, then repeated greedy completion."""
    np.random.seed(seed)
    n = len(initial)
    chosen = initial.copy()
    blocked = np.zeros(n, dtype=np.int32)
    for v in range(n):
        if chosen[v]:
            for e in range(indptr[v], indptr[v + 1]):
                blocked[indices[e]] += 1
    size = np.sum(chosen)
    best_size = size
    best = chosen.copy()
    temperatures = (1.5, 0.7, 0.3, 0.12, 0.0)
    for temperature in temperatures:
        for step in range(sweeps * n):
            v = np.random.randint(n)
            if chosen[v]:
                # Occasional deletions allow shape changes, never create conflicts.
                if temperature > 0 and np.random.random() < 0.06 * np.exp(-1 / temperature):
                    chosen[v] = False
                    size -= 1
                    for e in range(indptr[v], indptr[v + 1]):
                        blocked[indices[e]] -= 1
                continue
            count = blocked[v]
            accept = count <= 1
            if not accept and temperature > 0 and count <= 4:
                accept = np.random.random() < np.exp((1 - count) / temperature)
            if accept:
                for e in range(indptr[v], indptr[v + 1]):
                    u = indices[e]
                    if chosen[u]:
                        chosen[u] = False
                        size -= 1
                        for ee in range(indptr[u], indptr[u + 1]):
                            blocked[indices[ee]] -= 1
                chosen[v] = True
                size += 1
                for e in range(indptr[v], indptr[v + 1]):
                    blocked[indices[e]] += 1
                if size > best_size:
                    best_size = size
                    best = chosen.copy()
        # Restart from the largest independent set, retain all best states.
        chosen = best.copy()
        size = best_size
        blocked[:] = 0
        for v in range(n):
            if chosen[v]:
                for e in range(indptr[v], indptr[v + 1]):
                    blocked[indices[e]] += 1
    order = np.random.permutation(n)
    return greedy(indptr, indices, order, best)


def shrunken_lobes(points, R, epsilon, angle):
    """Known construction with strict epsilon separation, used as a control."""
    m = int(round(2 * R))
    r = (1 - epsilon) / 2 - 1e-10
    outer = R - epsilon / 2 - 1e-10
    t = (m - 1 + epsilon) / 2 + 1e-10
    c = (t + math.sqrt(t * t + 3 * (outer * outer - r * r))) / 3
    x = points[:, 0] * math.cos(angle) + points[:, 1] * math.sin(angle)
    y = -points[:, 0] * math.sin(angle) + points[:, 1] * math.cos(angle)
    return ((np.abs(x) > t) & ((np.abs(x) - c)**2 + y*y < r*r)
            & (np.sum(points**2, axis=1) < outer*outer))


def optimize_points(points, graph, epsilon, R, seed, sweeps=60):
    rng = np.random.default_rng(seed + 17)
    n = len(points)
    zero = np.zeros(n, dtype=bool)
    degree = np.diff(graph.indptr)
    starts = []
    # Unstructured graph starts, with randomized degree priorities.
    for trial in range(3):
        order = np.argsort(degree + rng.exponential(max(1, degree.mean() * .35), n))
        starts.append(("unstructured", greedy(graph.indptr, graph.indices, order, zero)))
    # Spatial growth starts can discover components without fixing their number.
    for center in [np.array([0., 0.]), *points[rng.choice(n, 4, replace=False)]]:
        order = np.argsort(np.sum((points - center)**2, axis=1))
        starts.append(("spatial_growth", greedy(graph.indptr, graph.indices, order, zero)))
    best_control = zero
    for angle in np.linspace(0, math.pi, 24, endpoint=False):
        initial = shrunken_lobes(points, R, epsilon, angle)
        initial = greedy(graph.indptr, graph.indices, rng.permutation(n), initial)
        if initial.sum() > best_control.sum():
            best_control = initial
    starts.append(("known_lobe_control", best_control))
    unstructured = max(int(s.sum()) for name, s in starts if name != "known_lobe_control")
    # Keep one start from each class plus the second best arbitrary start.
    ordered = sorted(starts, key=lambda item: int(item[1].sum()), reverse=True)
    picked = [ordered[0]]
    for name in ["unstructured", "spatial_growth", "known_lobe_control"]:
        candidate = max((s for s in starts if s[0] == name), key=lambda item: int(item[1].sum()))
        if not any(np.array_equal(candidate[1], old[1]) for old in picked):
            picked.append(candidate)
    outcomes = []
    for trial, (name, initial) in enumerate(picked):
        found = local_search(graph.indptr, graph.indices, initial,
                             seed + trial * 1009, sweeps)
        outcomes.append((name, found))
    name, best = max(outcomes, key=lambda item: int(item[1].sum()))
    return best, {"winning_start": name,
                  "best_unstructured_initial_count": unstructured,
                  "known_control_initial_count": int(best_control.sum()),
                  "final_counts_by_start": [{"start": x, "count": int(s.sum())} for x, s in outcomes]}


def wilson_area(covered, test_n, R):
    p = covered / test_n
    z = 1.959963984540054
    denominator = 1 + z*z/test_n
    midpoint = (p + z*z/(2*test_n)) / denominator
    halfwidth = z * math.sqrt(p*(1-p)/test_n + z*z/(4*test_n**2)) / denominator
    disk_area = math.pi * R * R
    return {"test_points": test_n, "hits": covered, "area": disk_area*p,
            "wilson_95_interval": [disk_area*(midpoint-halfwidth), disk_area*(midpoint+halfwidth)],
            "note": "conditional interval for this fixed reconstructed set, not for M(R)"}


def measure_disk_union(centers, R, epsilon, radii, seed, test_n):
    rng = np.random.default_rng(seed)
    heldout = uniform_disk(test_n, R, rng)
    distance, _ = cKDTree(centers).query(heldout, workers=-1)
    covered = int(np.count_nonzero(distance < epsilon / 2))
    fixed = wilson_area(covered, test_n, R)
    # r_i = min(1/2, min_j gap(i,j)/2). Thus r_i+r_j <= gap(i,j),
    # and the triangle inequality certifies the entire variable-radius union.
    tree = cKDTree(heldout)
    hit = np.zeros(test_n, dtype=bool)
    for start in range(0, len(centers), 128):
        groups = tree.query_ball_point(centers[start:start+128], radii[start:start+128], workers=-1)
        for group in groups:
            if len(group):
                hit[group] = True
    adaptive = wilson_area(int(hit.sum()), test_n, R)
    adaptive["minimum_ball_radius"] = float(radii.min())
    adaptive["maximum_ball_radius"] = float(radii.max())
    return fixed, adaptive


def polygon_candidates(centers, R, radii=None):
    """Recover spatial components, retaining only diameter < 1 convex hulls."""
    candidates = []
    boundary = None
    if radii is not None:
        angles = np.linspace(0, 2*math.pi, 32, endpoint=False)
        directions = np.column_stack((np.cos(angles), np.sin(angles)))
        dot = centers @ directions.T
        # Clip each ray inside the outer disk, keeping a margin for rationalization.
        to_disk = -dot + np.sqrt(dot*dot + R*R - np.sum(centers**2, axis=1)[:, None])
        radius = np.minimum(radii[:, None], to_disk) - 2e-8
        radius = np.maximum(radius, 0)
        boundary = centers[:, None, :] + radius[:, :, None]*directions[None, :, :]
    for cutoff in [.07, .12, .20, .30]:
        pair = cKDTree(centers).query_pairs(cutoff, output_type="ndarray")
        graph = coo_matrix((np.ones(2*len(pair)),
                            (np.r_[pair[:, 0], pair[:, 1]], np.r_[pair[:, 1], pair[:, 0]])),
                           shape=(len(centers), len(centers))).tocsr()
        count, labels = connected_components(graph, directed=False)
        for expansion in ([0., .5, 1.] if boundary is not None else [0.]):
            hulls = []
            for label in range(count):
                keep = labels == label
                group = centers[keep]
                if len(group) < 4:
                    continue
                if expansion:
                    expanded = centers[keep, None, :] + expansion*(boundary[keep]-centers[keep, None, :])
                    group = expanded.reshape(-1, 2)
                try:
                    hull = ConvexHull(group)
                except Exception:
                    continue
                vertices = group[hull.vertices]
                if cdist(vertices, vertices).max() >= 1 - 1e-9:
                    continue
                if hull.volume < 1e-5:
                    continue
                hulls.append(vertices)
            candidates.append(((cutoff, expansion), hulls))
    return candidates


def exact_polygon_reconstruction(centers, R, radii=None):
    from verify_953_random_polygons import compatible, polygon_area_twice, verify_certificate
    denominator = 100_000_000
    best_area = 0.
    best_data = None
    for (cutoff, expansion), hulls in polygon_candidates(centers, R, radii):
        polys = [np.rint(p * denominator).astype(np.int64).tolist() for p in hulls]
        polys.sort(key=lambda p: polygon_area_twice(p), reverse=True)
        chosen = []
        for polygon in polys:
            if all(compatible(polygon, old, denominator)[0] for old in chosen):
                chosen.append(polygon)
        data = {"coordinate_denominator": denominator, "radius_numerator": int(round(2*R)),
                "radius_denominator": 2, "polygons": chosen,
                "topology_cutoff": cutoff, "ball_expansion_fraction": expansion,
                "forbidden_distances": "all positive integers"}
        if not chosen:
            continue
        try:
            result = verify_certificate(data)
        except AssertionError:
            continue
        area = float(result["area_fraction_value"])
        if area > best_area:
            best_area, best_data = area, data
    return best_area, best_data


def solve_small_milp(points, epsilon, forbidden, seconds):
    graph, row, col = conflict_graph(points, epsilon, forbidden)
    n = len(points)
    matrix = coo_matrix((np.ones(2*len(row)),
                         (np.repeat(np.arange(len(row)), 2), np.column_stack((row, col)).ravel())),
                        shape=(len(row), n)).tocsr()
    solved = milp(-np.ones(n), integrality=np.ones(n), bounds=Bounds(0, 1),
                  constraints=LinearConstraint(matrix, -np.inf, 1),
                  options={"time_limit": seconds, "mip_rel_gap": 0.0})
    chosen = solved.x > .5 if solved.x is not None else np.zeros(n, dtype=bool)
    assert not np.any(chosen[row] & chosen[col])
    return {"sample_points": n, "epsilon": epsilon, "edges": len(row),
            "selected": int(chosen.sum()), "finite_graph_optimal": bool(solved.status == 0),
            "finite_graph_upper_bound": float(-solved.mip_dual_bound) if hasattr(solved, "mip_dual_bound") else None,
            "mip_gap": float(solved.mip_gap) if hasattr(solved, "mip_gap") else None,
            "solver_message": solved.message,
            "note": "even an exactly solved finite graph does not certify an area optimum"}


def run_case(R, n, epsilon, seed, test_n, sweeps):
    begin = time.perf_counter()
    points = uniform_disk(n, R, np.random.default_rng(seed))
    forbidden = list(range(1, int(math.ceil(2*R)) + 1))
    graph, row, col = conflict_graph(points, epsilon, forbidden)
    selected, search = optimize_points(points, graph, epsilon, R, seed, sweeps)
    assert not np.any(selected[row] & selected[col]), "conflicting selected pair"
    centers = points[selected]
    # Full all-pairs audit on the final independent set, independent of CSR graph.
    clearance = np.full(len(centers), 1.)
    for start in range(0, len(centers), 128):
        stop = min(start + 128, len(centers))
        dist = cdist(centers[start:stop], centers)
        dist[np.arange(stop-start), np.arange(start, stop)] = np.inf
        for k in forbidden:
            clearance[start:stop] = np.minimum(clearance[start:stop], np.min(np.abs(dist-k), axis=1))
    separation = float(clearance.min())
    assert separation > epsilon
    radii = .5 * clearance * (1 - 1e-12)
    union, adaptive = measure_disk_union(centers, R, epsilon, radii, seed + 9_000_001, test_n)
    polygon_area, certificate = exact_polygon_reconstruction(centers, R, radii)
    case_id = f"R{R:g}-N{n}-eps{epsilon:g}-seed{seed}"
    if certificate:
        certificate["experiment"] = case_id
        filename = HERE / f"erdos953-random-polygons-{case_id}.json"
        filename.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    else:
        filename = None
    data = {"case": case_id, "R": R, "N": n, "epsilon": epsilon, "seed": seed,
            "sweeps_per_temperature": sweeps,
            "forbidden_distances_in_graph": forbidden, "edges": len(row),
            "selected_count": len(centers), "selected_fraction": len(centers)/n,
            "training_fraction_area_proxy": math.pi*R*R*len(centers)/n,
            "minimum_forbidden_distance_gap": separation,
            "graph_independent_set_all_pairs_audited": True,
            "graph_pair_audit_arithmetic": "float64 (continuous certificates use exact integers)",
            "search": search, "continuous_disk_union": union,
            "adaptive_disk_union": adaptive,
            "exact_rational_polygon_area": polygon_area,
            "polygon_certificate": filename.name if filename else None,
            "seconds": time.perf_counter() - begin}
    np.savez_compressed(HERE / f"erdos953-random-points-{case_id}.npz",
                        points=points, selected=selected, R=R, epsilon=epsilon, ball_radii=radii)
    print(json.dumps(data), flush=True)
    return data


def plot_results(results):
    radii = sorted({r["R"] for r in results})
    def certified_area(result):
        return max(result["exact_rational_polygon_area"], result.get("exact_ball_grid_area", 0.))
    best = [max((r for r in results if r["R"] == R),
                key=certified_area) for R in radii]
    fig, axes = plt.subplots(1, len(best), figsize=(4.3*len(best), 4.8), constrained_layout=True,
                             squeeze=False)
    for ax, result in zip(axes[0], best):
        stored = np.load(HERE / f"erdos953-random-points-{result['case']}.npz")
        points, chosen = stored["points"], stored["selected"]
        R = result["R"]
        ax.add_patch(Circle((0, 0), R, fill=False, color="#566678", lw=1.3))
        ax.scatter(points[~chosen, 0], points[~chosen, 1], s=.35, color="#bbc2c9", alpha=.20, rasterized=True)
        ax.scatter(points[chosen, 0], points[chosen, 1], s=1.5, color="#137dae", alpha=.60, rasterized=True)
        if result.get("exact_ball_grid_area", 0.) > result["exact_rational_polygon_area"]:
            data = json.loads((HERE/result["ball_grid_certificate"]).read_text(encoding="utf-8"))
            side = int(round(2*R*data["grid_cell_denominator"]))
            mask = np.zeros((side, side), dtype=np.uint8)
            for row, start, end, witness in data["rectangle_runs"]:
                mask[row, start:end+1] = 1
            ax.imshow(np.ma.masked_where(mask == 0, mask), origin="lower", extent=(-R, R, -R, R),
                      cmap=matplotlib.colors.ListedColormap(["#e57320"]), alpha=.35, zorder=1,
                      interpolation="nearest")
        elif result["polygon_certificate"]:
            data = json.loads((HERE/result["polygon_certificate"]).read_text(encoding="utf-8"))
            for polygon in data["polygons"]:
                vertices = np.array(polygon)/data["coordinate_denominator"]
                ax.add_patch(Polygon(vertices, facecolor="#e57320", alpha=.22, edgecolor="#e57320", lw=1.3))
        ax.set_aspect("equal")
        ax.set(xlim=(-1.08*R, 1.08*R), ylim=(-1.08*R, 1.08*R), xlabel="x", ylabel="y")
        ax.set_title(f"R={R:g}, N={result['N']}, epsilon={result['epsilon']:g}\n"
                     f"point-fraction proxy: {result['training_fraction_area_proxy']:.6f}\n"
                     f"exact constructed area: {certified_area(result):.6f}", fontsize=10)
    fig.suptitle("Random-point search: blue selected points; orange exactly verified continuous sets", fontsize=12)
    fig.savefig(HERE / f"erdos953-random-point-shapes-{STAMP}.png", dpi=185)
    plt.close(fig)

    fig, axes = plt.subplots(1, len(radii), figsize=(4.4*len(radii), 4.1), constrained_layout=True,
                             squeeze=False)
    known = {1.: .8950191291901026, 1.5: .9176478349623267, 2.: .928030414065414}
    for ax, R in zip(axes[0], radii):
        subset = sorted([r for r in results if r["R"] == R], key=lambda r: (r["epsilon"], r["N"]))
        x = np.arange(len(subset))
        ax.plot(x, [r["training_fraction_area_proxy"] for r in subset], "o-", color="#7b53b2", label="optimized training fraction")
        ax.plot(x, [certified_area(r) for r in subset], "s-", color="#e57320", label="exact reconstructed area")
        if all("adaptive_disk_union" in r for r in subset):
            ax.plot(x, [r["adaptive_disk_union"]["area"] for r in subset], "d-", color="#147dae", label="adaptive balls, held-out sample")
        union = [r["continuous_disk_union"] for r in subset]
        means = np.array([u["area"] for u in union])
        low = np.array([u["wilson_95_interval"][0] for u in union])
        high = np.array([u["wilson_95_interval"][1] for u in union])
        ax.errorbar(x, means, yerr=np.array([means-low, high-means]), fmt="^-", color="#128875", label="disk union, held-out 95% CI")
        ax.axhline(known[R], color="#253a4b", ls="--", label="previous exact construction")
        ax.set_xticks(x, [f"{r['N']//1000}k\ne={r['epsilon']:g}" for r in subset], fontsize=8)
        ax.set(title=f"R={R:g}", ylabel="area", xlabel="sample size and tolerance")
        ax.grid(alpha=.15)
    axes[0, 0].legend(fontsize=7)
    fig.suptitle("Training fraction, continuous reconstructions, and the known lower bound")
    fig.savefig(HERE / f"erdos953-random-point-comparison-{STAMP}.png", dpi=185)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", nargs="+", default=["1:4000:.03:95301"],
                        help="R:N:epsilon:seed")
    parser.add_argument("--test-n", type=int, default=300000)
    parser.add_argument("--sweeps", type=int, default=60)
    parser.add_argument("--small-milp", action="store_true")
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--reconstruct-only", action="store_true",
                        help="improve continuous polygons from all previously saved point sets")
    args = parser.parse_args()
    output = HERE / f"erdos953-random-point-results-{STAMP}.json"
    if (args.append or args.reconstruct_only) and output.exists():
        report = json.loads(output.read_text(encoding="utf-8"))
    else:
        report = {"method": "uniform disk sampling and multi-start independent-set local search",
                  "point_fraction_is_not_an_area_certificate": True,
                  "continuous_disk_union_lemma": "union of open epsilon/2 balls, intersected with D_R; triangle inequality excludes integers",
                  "confidence_intervals_are_conditional_and_not_optimality_bounds": True,
                  "results": [], "small_finite_graph_calibration": []}
    if args.reconstruct_only:
        for result in report["results"]:
            saved = np.load(HERE / f"erdos953-random-points-{result['case']}.npz")
            if "ball_radii" not in saved:
                continue
            area, certificate = exact_polygon_reconstruction(saved["points"][saved["selected"]],
                                                               result["R"], saved["ball_radii"])
            if certificate:
                filename = HERE / f"erdos953-random-polygons-{result['case']}.json"
                certificate["experiment"] = result["case"]
                filename.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
                result["exact_rational_polygon_area"] = area
                result["polygon_certificate"] = filename.name
            print(json.dumps({"reconstructed": result["case"], "exact_polygon_area": area}), flush=True)
            output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        plot_results(report["results"])
        return
    for case in args.cases:
        rr, nn, ee, ss = case.split(":")
        result = run_case(float(rr), int(nn), float(ee), int(ss), args.test_n, args.sweeps)
        report["results"] = [old for old in report["results"] if old["case"] != result["case"]]
        report["results"].append(result)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if args.small_milp:
        for R in [1., 1.5, 2.]:
            points = uniform_disk(240, R, np.random.default_rng(19953))
            result = solve_small_milp(points, .04, list(range(1, int(2*R)+1)), 12)
            result["R"] = R
            report["small_finite_graph_calibration"].append(result)
            print(json.dumps({"small_milp": result}), flush=True)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    plot_results(report["results"])


if __name__ == "__main__":
    main()
