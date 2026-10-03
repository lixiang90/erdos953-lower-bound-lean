"""Weighted independent-set search on triangles clipped to the exact disk.

Boundary cells retain circular arcs. Conflict intervals use clipped straight
segments for minima, and vertices/antipodes on arcs for maxima. Numerical
comparisons include a conservative tolerance. A separate rational inner-polygon
certificate gives an exactly checkable continuous area lower bound.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np
from numba import njit, prange, set_num_threads
from scipy.sparse import coo_matrix
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.spatial import cKDTree
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.patches import Circle

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
TAU = 2*math.pi
TOL = 2e-10
set_num_threads(8)


def cross(a, b, c):
    u, v = b-a, c-a
    return float(u[0]*v[1]-u[1]*v[0])


def triangle_contains(point, triangle, tolerance=1e-11):
    return all(cross(a, b, point) >= -tolerance
               for a, b in zip(triangle, np.roll(triangle, -1, axis=0)))


def clip_triangle(triangle, R):
    """Exact analytic intersection with a disk; no polygonized circle."""
    vertices, segments, circle_points = [], [], []
    for point in triangle:
        if float(point @ point) <= R*R+1e-13:
            vertices.append(point)
    for a, b in zip(triangle, np.roll(triangle, -1, axis=0)):
        d = b-a
        aa, bb, cc = float(d @ d), 2*float(a @ d), float(a @ a)-R*R
        discriminant = bb*bb-4*aa*cc
        if discriminant < -1e-13:
            continue
        root = math.sqrt(max(0., discriminant))
        lo, hi = (-bb-root)/(2*aa), (-bb+root)/(2*aa)
        if lo >= 0 and lo <= 1:
            point = a+lo*d
            vertices.append(point)
            circle_points.append(point)
        if hi >= 0 and hi <= 1:
            point = a+hi*d
            vertices.append(point)
            circle_points.append(point)
        left, right = max(0., lo), min(1., hi)
        if right-left > 1e-13:
            segments.append([a+left*d, a+right*d])
    unique = []
    for point in vertices:
        if not any(np.linalg.norm(point-old) < 1e-11 for old in unique):
            unique.append(point)
    if len(unique) < 2:
        return None
    vertices = np.array(unique)
    center = vertices.mean(axis=0)
    vertices = vertices[np.argsort(np.arctan2(vertices[:, 1]-center[1], vertices[:, 0]-center[0]))]
    arcs = []
    if len(circle_points) >= 2:
        angles = sorted({round(math.atan2(p[1], p[0]) % TAU, 13) for p in circle_points})
        for i, start in enumerate(angles):
            end = angles[(i+1) % len(angles)]
            if end <= start:
                end += TAU
            if end-start < 1e-11:
                continue
            mid = (start+end)/2
            point = R*np.array([math.cos(mid), math.sin(mid)])
            if triangle_contains(point, triangle):
                arcs.append([start, end-start])
    shoelace = float(np.sum(vertices[:, 0]*np.roll(vertices[:, 1], -1)
                             -vertices[:, 1]*np.roll(vertices[:, 0], -1)))/2
    area = shoelace+sum(R*R*(span-math.sin(span))/2 for start, span in arcs)
    if area < 1e-14:
        return None
    return {"triangle": triangle, "vertices": vertices, "segments": np.array(segments),
            "arcs": np.array(arcs).reshape(-1, 2), "area": area,
            "representative": vertices.mean(axis=0)}


def make_partition(R, n):
    h = R/n
    cells = []
    for i in range(-n, n):
        for j in range(-n, n):
            a, b, c, d = np.array([[i, j], [i+1, j], [i+1, j+1], [i, j+1]], float)*h
            triangles = [[a, b, c], [a, c, d]] if (i+j) % 2 == 0 else [[a, b, d], [b, c, d]]
            for local, tri in enumerate(triangles):
                cell = clip_triangle(np.array(tri), R)
                if cell:
                    cell["grid_id"] = [i, j, local]
                    cells.append(cell)
    count = len(cells)
    vertices = np.zeros((count, 8, 2))
    segments = np.zeros((count, 3, 2, 2))
    arcs = np.zeros((count, 4, 2))
    nv, ns, na = (np.zeros(count, dtype=np.int32) for _ in range(3))
    triangles = np.array([c["triangle"] for c in cells])
    for i, cell in enumerate(cells):
        nv[i], ns[i], na[i] = len(cell["vertices"]), len(cell["segments"]), len(cell["arcs"])
        vertices[i, :nv[i]] = cell["vertices"]
        segments[i, :ns[i]] = cell["segments"]
        arcs[i, :na[i]] = cell["arcs"]
    total = sum(c["area"] for c in cells)
    assert abs(total-math.pi*R*R) < 2e-9, (total, math.pi*R*R)
    assert math.sqrt(2)*h < 1-TOL, "a cell must not have an internal integer distance"
    return cells, {"vertices": vertices, "segments": segments, "arcs": arcs,
                   "nv": nv, "ns": ns, "na": na, "triangles": triangles,
                   "centers": triangles.mean(axis=1),
                   "enclosing_radii": np.max(np.linalg.norm(triangles-triangles.mean(axis=1)[:, None, :], axis=2), axis=1),
                   "weights": np.array([c["area"] for c in cells]),
                   "representatives": np.array([c["representative"] for c in cells])}


@njit(cache=True)
def angle_in(phi, start, span):
    return (phi-start) % (2*np.pi) <= span+2e-12


@njit(cache=True)
def point_segment_squared(px, py, ax, ay, bx, by):
    dx, dy = bx-ax, by-ay
    length = dx*dx+dy*dy
    t = ((px-ax)*dx+(py-ay)*dy)/length if length > 0 else 0.
    t = min(1., max(0., t))
    return (px-ax-t*dx)**2+(py-ay-t*dy)**2


@njit(cache=True)
def vertex_bounds(i, j, vertices, nv):
    smallest, largest = np.inf, 0.
    for a in range(nv[i]):
        for b in range(nv[j]):
            dx = vertices[i, a, 0]-vertices[j, b, 0]
            dy = vertices[i, a, 1]-vertices[j, b, 1]
            squared = dx*dx+dy*dy
            smallest = min(smallest, squared)
            largest = max(largest, squared)
    return smallest, largest


@njit(cache=True)
def curved_maximum_squared(i, j, vertices, nv, arcs, na, R, maximum):
    for flip in range(2):
        a, b = (i, j) if flip == 0 else (j, i)
        for t in range(na[a]):
            start, span = arcs[a, t, 0], arcs[a, t, 1]
            for v in range(nv[b]):
                x, y = vertices[b, v, 0], vertices[b, v, 1]
                phi = math.atan2(-y, -x)
                if angle_in(phi, start, span):
                    maximum = max(maximum, (R+math.sqrt(x*x+y*y))**2)
    for a in range(na[i]):
        for b in range(na[j]):
            delta = (arcs[j, b, 0]+np.pi-arcs[i, a, 0]) % (2*np.pi)
            if delta <= arcs[i, a, 1]+2e-12 or 2*np.pi-delta <= arcs[j, b, 1]+2e-12:
                maximum = 4*R*R
    return maximum


@njit(cache=True)
def minimum_squared(i, j, vertices, nv, segments, ns, initial):
    # An interior outer-circle point cannot minimize distance to another point
    # in D_R: a small inward radial displacement decreases the distance.
    result = initial
    for flip in range(2):
        a, b = (i, j) if flip == 0 else (j, i)
        for v in range(nv[a]):
            for e in range(ns[b]):
                result = min(result, point_segment_squared(
                    vertices[a, v, 0], vertices[a, v, 1],
                    segments[b, e, 0, 0], segments[b, e, 0, 1],
                    segments[b, e, 1, 0], segments[b, e, 1, 1]))
    return result


@njit(cache=True)
def cells_conflict(i, j, vertices, nv, segments, ns, arcs, na, R, kmax, tolerance):
    smallest, largest = vertex_bounds(i, j, vertices, nv)
    if na[i] or na[j]:
        largest = curved_maximum_squared(i, j, vertices, nv, arcs, na, R, largest)
    minimum_computed = False
    for k in range(1, kmax+1):
        if largest < k*k-tolerance:
            continue
        if smallest <= k*k+tolerance:
            return True
        if not minimum_computed:
            smallest = minimum_squared(i, j, vertices, nv, segments, ns, smallest)
            minimum_computed = True
        if smallest <= k*k+tolerance:
            return True
    return False


@njit(cache=True, parallel=True)
def graph_flags(centers, radii, vertices, nv, segments, ns, arcs, na, R, kmax, tolerance):
    n = len(centers)
    flags = np.zeros((n, n), dtype=np.uint8)
    for ii in prange(n):
        i = np.int64(ii)
        for j in range(i+1, n):
            dx, dy = centers[i, 0]-centers[j, 0], centers[i, 1]-centers[j, 1]
            center_d2 = dx*dx+dy*dy
            radius_sum = radii[i]+radii[j]+tolerance
            near_integer = False
            for k in range(1, kmax+1):
                if center_d2 >= (k-radius_sum)**2 and center_d2 <= (k+radius_sum)**2:
                    near_integer = True
                    break
            if near_integer and cells_conflict(i, j, vertices, nv, segments, ns, arcs, na, R, kmax, tolerance):
                flags[i, j] = 1
    return flags


def build_graph(data, R):
    flags = graph_flags(data["centers"], data["enclosing_radii"], data["vertices"], data["nv"],
                        data["segments"], data["ns"], data["arcs"], data["na"], R,
                        int(math.ceil(2*R)), TOL)
    row, col = np.nonzero(flags)
    row, col = row.astype(np.int32), col.astype(np.int32)
    del flags
    n = len(data["weights"])
    graph = coo_matrix((np.ones(2*len(row), dtype=np.int8),
                       (np.r_[row, col], np.r_[col, row])), shape=(n, n)).tocsr()
    graph.sort_indices()
    return graph, row, col


@njit(cache=True, parallel=True)
def audit_selected_cells(ids, vertices, nv, segments, ns, arcs, na, R, kmax, tolerance):
    conflicts = np.zeros(len(ids), dtype=np.int64)
    for position in prange(len(ids)):
        i = ids[position]
        for later in range(position+1, len(ids)):
            j = ids[later]
            if cells_conflict(i, j, vertices, nv, segments, ns, arcs, na, R, kmax, tolerance):
                conflicts[position] += 1
    return np.sum(conflicts)


@njit(cache=True)
def weighted_greedy(indptr, indices, order, initial):
    chosen = initial.copy()
    blocked = np.zeros(len(chosen), dtype=np.int32)
    for v in range(len(chosen)):
        if chosen[v]:
            for e in range(indptr[v], indptr[v+1]):
                blocked[indices[e]] += 1
    for v in order:
        if not chosen[v] and blocked[v] == 0:
            chosen[v] = True
            for e in range(indptr[v], indptr[v+1]):
                blocked[indices[e]] += 1
    return chosen


@njit(cache=True)
def weighted_local(indptr, indices, weights, initial, seed, sweeps):
    np.random.seed(seed)
    chosen = initial.copy()
    n = len(chosen)
    blocked = np.zeros(n, dtype=np.int32)
    for v in range(n):
        if chosen[v]:
            for e in range(indptr[v], indptr[v+1]):
                blocked[indices[e]] += 1
    value = np.sum(weights*chosen)
    best_value, best = value, chosen.copy()
    for temperature in (.8, .3, .1, .03, 0.):
        for step in range(n*sweeps):
            v = np.random.randint(n)
            if chosen[v] or blocked[v] > 5:
                continue
            removed_weight = 0.
            for e in range(indptr[v], indptr[v+1]):
                u = indices[e]
                if chosen[u]:
                    removed_weight += weights[u]
            gain = weights[v]-removed_weight
            accept = gain >= -1e-12
            if not accept and temperature > 0:
                accept = np.random.random() < np.exp(gain/temperature)
            if accept:
                for e in range(indptr[v], indptr[v+1]):
                    u = indices[e]
                    if chosen[u]:
                        chosen[u] = False
                        for ee in range(indptr[u], indptr[u+1]):
                            blocked[indices[ee]] -= 1
                chosen[v] = True
                for e in range(indptr[v], indptr[v+1]):
                    blocked[indices[e]] += 1
                value += gain
                if value > best_value+1e-10:
                    best_value, best = value, chosen.copy()
        chosen = best.copy()
        value = best_value
        blocked[:] = 0
        for v in range(n):
            if chosen[v]:
                for e in range(indptr[v], indptr[v+1]):
                    blocked[indices[e]] += 1
    return weighted_greedy(indptr, indices, np.random.permutation(n), best)


@njit(cache=True)
def weighted_patch_local(indptr, indices, weights, patch_ptr, patch_indices, initial, seed):
    """Replace a spatial cluster by removing ALL its selected conflicts."""
    np.random.seed(seed)
    chosen = initial.copy()
    n = len(chosen)
    value = np.sum(weights*chosen)
    best_value, best = value, chosen.copy()
    marks = np.zeros(n, dtype=np.int32)
    removed = np.empty(n, dtype=np.int32)
    added = np.empty(n, dtype=np.int32)
    stamp = 0
    for temperature in (2., 1., .3, 0.):
        order = np.random.permutation(len(patch_ptr)-1)
        for patch in order:
            stamp += 1
            add_count, remove_count = 0, 0
            add_weight, remove_weight = 0., 0.
            for offset in range(patch_ptr[patch], patch_ptr[patch+1]):
                v = patch_indices[offset]
                if chosen[v]:
                    continue
                added[add_count] = v
                add_count += 1
                add_weight += weights[v]
                for edge in range(indptr[v], indptr[v+1]):
                    u = indices[edge]
                    if chosen[u] and marks[u] != stamp:
                        marks[u] = stamp
                        removed[remove_count] = u
                        remove_count += 1
                        remove_weight += weights[u]
            gain = add_weight-remove_weight
            if add_count == 0:
                continue
            accept = gain >= -1e-12
            if not accept and temperature > 0:
                accept = np.random.random() < np.exp(gain/temperature)
            if accept:
                for position in range(remove_count):
                    chosen[removed[position]] = False
                for position in range(add_count):
                    chosen[added[position]] = True
                value += gain
                if value > best_value+1e-10:
                    best_value, best = value, chosen.copy()
        completed = weighted_greedy(indptr, indices, np.random.permutation(n), best)
        completed_value = np.sum(weights*completed)
        if completed_value > best_value:
            best_value, best = completed_value, completed.copy()
        chosen, value = best.copy(), best_value
    return best


def improve_by_patches(graph, data, R, n, selected, seed, patches):
    rng = np.random.default_rng(seed+333333)
    representatives = data["representatives"]
    h = R/n
    max_radius = min(.16, (1-2*math.sqrt(2)*h)/3)
    assert 2*max_radius+2*math.sqrt(2)*h < 1-1e-8
    initial_ids = np.flatnonzero(selected)
    center_ids = rng.integers(len(selected), size=patches)
    if len(initial_ids):
        center_ids[:patches//2] = rng.choice(initial_ids, patches//2)
    radii = rng.uniform(max_radius*.12, max_radius, patches)
    groups = cKDTree(representatives).query_ball_point(representatives[center_ids], radii)
    lengths = np.array([len(group) for group in groups], dtype=np.int64)
    pointer = np.r_[0, np.cumsum(lengths)]
    indices = np.array([v for group in groups for v in group], dtype=np.int32)
    weights = data["weights"]/data["weights"].max()
    improved = weighted_patch_local(graph.indptr, graph.indices, weights, pointer, indices, selected, seed+333333)
    # Finish by fine local swaps; do not discard the larger-area patch solution.
    alternative = weighted_local(graph.indptr, graph.indices, weights, improved, seed+777777, 160)
    if data["weights"] @ alternative > data["weights"] @ improved:
        improved = alternative
    return improved, {"spatial_patches_per_temperature": patches,
                      "maximum_patch_radius": max_radius,
                      "before_area": float(data["weights"] @ selected),
                      "after_area": float(data["weights"] @ improved)}


@njit(cache=True)
def triangles_inside_balls(triangles, centers, radii):
    chosen = np.zeros(len(triangles), dtype=np.bool_)
    for i in range(len(triangles)):
        for j in range(len(centers)):
            good = True
            for v in range(3):
                dx, dy = triangles[i, v, 0]-centers[j, 0], triangles[i, v, 1]-centers[j, 1]
                if dx*dx+dy*dy >= radii[j]*radii[j]-1e-12:
                    good = False
                    break
            if good:
                chosen[i] = True
                break
    return chosen


def control_mask(data, R):
    triangles = data["triangles"]
    if R == 1:
        t, c = .5, (1+math.sqrt(10))/6
        x, y = triangles[:, :, 0], triangles[:, :, 1]
        return ((np.all(x > t+1e-8, axis=1) | np.all(x < -t-1e-8, axis=1))
                & np.all((np.abs(x)-c)**2+y*y < .25-1e-8, axis=1)
                & np.all(x*x+y*y < R*R-1e-8, axis=1))
    summary = json.loads((HERE/f"erdos953-random-search-summary-{STAMP}.json").read_text(encoding="utf-8"))
    best = next(item for item in summary["radii"] if item["R"] == R)
    certificate = json.loads((HERE/best["best_random_certificate"]).read_text(encoding="utf-8"))
    if "balls" in certificate:
        balls = np.array(certificate["balls"], dtype=float)/certificate["coordinate_denominator"]
        return triangles_inside_balls(triangles, balls[:, :2], balls[:, 2])
    chosen = np.zeros(len(triangles), dtype=bool)
    for polygon in certificate["polygons"]:
        polygon = np.array(polygon, dtype=float)/certificate["coordinate_denominator"]
        good = np.ones(len(triangles), dtype=bool)
        for a, b in zip(polygon, np.roll(polygon, -1, axis=0)):
            edge = b-a
            determinant = edge[0]*(triangles[:, :, 1]-a[1])-edge[1]*(triangles[:, :, 0]-a[0])
            good &= np.all(determinant > 1e-10, axis=1)
        chosen |= good
    return chosen


def optimize(graph, data, R, seed, sweeps):
    rng = np.random.default_rng(seed)
    n = len(data["weights"])
    zero = np.zeros(n, dtype=bool)
    weights = data["weights"]/data["weights"].max()
    degree = np.diff(graph.indptr)
    starts = []
    for trial in range(2):
        priority = degree/np.maximum(weights, 1e-5)+rng.exponential(max(1, degree.mean()*.3), n)
        starts.append(("unstructured", weighted_greedy(graph.indptr, graph.indices, np.argsort(priority), zero)))
    reps = data["representatives"]
    for center in [np.array([0., 0.]), reps[rng.integers(n)], reps[rng.integers(n)]]:
        order = np.argsort(np.sum((reps-center)**2, axis=1)/np.maximum(weights, 1e-5))
        starts.append(("spatial_growth", weighted_greedy(graph.indptr, graph.indices, order, zero)))
    mask = control_mask(data, R)
    # Greedy initialization rechecks even the geometric controls against this
    # partition's closed-cell conflicts, including the outer integer 2R.
    order = np.r_[np.flatnonzero(mask), rng.permutation(np.flatnonzero(~mask))]
    starts.append(("previous_construction_control", weighted_greedy(graph.indptr, graph.indices, order, zero)))
    picked = []
    for name in ["unstructured", "spatial_growth", "previous_construction_control"]:
        picked.append(max((x for x in starts if x[0] == name), key=lambda x: float(data["weights"] @ x[1])))
    outcomes = []
    for trial, (name, initial) in enumerate(picked):
        found = weighted_local(graph.indptr, graph.indices, weights, initial, seed+trial*1013, sweeps)
        outcomes.append((name, found))
    name, found = max(outcomes, key=lambda x: float(data["weights"] @ x[1]))
    return found, {"winning_start": name,
                   "initial_areas": [{"start": name, "area": float(data["weights"] @ mask)} for name, mask in starts],
                   "final_areas": [{"start": name, "area": float(data["weights"] @ mask)} for name, mask in outcomes]}


def small_milp(graph, row, col, weights, seconds):
    matrix = coo_matrix((np.ones(2*len(row)),
                        (np.repeat(np.arange(len(row)), 2), np.column_stack((row, col)).ravel())),
                       shape=(len(row), len(weights))).tocsr()
    solved = milp(-weights, integrality=np.ones(len(weights)), bounds=Bounds(0, 1),
                  constraints=LinearConstraint(matrix, -np.inf, 1),
                  options={"time_limit": seconds, "mip_rel_gap": 0.0})
    selected = solved.x > .5 if solved.x is not None else np.zeros(len(weights), dtype=bool)
    assert not np.any(selected[row] & selected[col])
    return selected, {"partition_optimal": bool(solved.status == 0),
                      "partition_upper_bound": float(-solved.mip_dual_bound) if hasattr(solved, "mip_dual_bound") else None,
                      "mip_gap": float(solved.mip_gap) if hasattr(solved, "mip_gap") else None,
                      "message": solved.message}


def make_inner_certificate(cells, selected, R, n):
    # Every original grid vertex has denominator Q, exactly. Boundary polygons
    # are slightly contracted towards their centroid before rationalization.
    Q = 2*n*1_000_000
    pieces = []
    for cell, keep in zip(cells, selected):
        if not keep:
            continue
        vertices = cell["vertices"]
        if len(cell["arcs"]):
            sampled = [p for p in vertices]
            for start, span in cell["arcs"]:
                for angle in np.linspace(start, start+span, 9)[1:-1]:
                    sampled.append(R*np.array([math.cos(angle), math.sin(angle)]))
            vertices = np.array(sampled)
        center = vertices.mean(axis=0)
        triangle = np.rint(cell["triangle"]*Q).astype(np.int64).tolist()
        from verify_953_triangle_partition import cross as integer_cross
        def integer_hull(points):
            points = sorted(set(map(tuple, points)))
            lower, upper = [], []
            for p in points:
                while len(lower) >= 2 and integer_cross(lower[-2], lower[-1], p) <= 0:
                    lower.pop()
                lower.append(p)
            for p in reversed(points):
                while len(upper) >= 2 and integer_cross(upper[-2], upper[-1], p) <= 0:
                    upper.pop()
                upper.append(p)
            return [list(p) for p in lower[:-1]+upper[:-1]]
        polygon = None
        near_circle = np.any(np.sum(vertices**2, axis=1) >= R*R-1e-11)
        attempts = [1e-5, 1e-4, .001, .01, .1] if near_circle else [0., 1e-5, 1e-4, .001]
        for contraction in attempts:
            candidate = integer_hull(np.rint((center+(1-contraction)*(vertices-center))*Q).astype(np.int64).tolist())
            if len(candidate) < 3:
                continue
            good = True
            for x, y in candidate:
                if 4*(x*x+y*y) > int(round(2*R))**2*Q*Q:
                    good = False
                if not all(integer_cross(a, b, [x, y]) >= 0 for a, b in zip(triangle, triangle[1:]+triangle[:1])):
                    good = False
            if good:
                polygon = candidate
                break
        if polygon is None:
            # An extremely thin boundary sliver can have no lattice polygon at Q.
            # Omitting it only lowers the certified area; optimization is unchanged.
            continue
        pieces.append({"grid_id": cell["grid_id"], "triangle": triangle, "polygon": polygon})
    return {"coordinate_denominator": Q, "radius_numerator": int(round(2*R)),
            "radius_denominator": 2, "grid_n": n, "pieces": pieces,
            "construction": "union of open interiors of rational polygons inside distinct grid triangles",
            "boundary_policy": "optimization preserves arcs; this exact area certificate inscribes chords"}


def drawn_cell(cell, R):
    points = [p for p in cell["vertices"]]
    for start, span in cell["arcs"]:
        angles = np.linspace(start, start+span, 9)
        points.extend(R*np.column_stack((np.cos(angles), np.sin(angles))))
    points = np.array(points)
    center = points.mean(axis=0)
    return points[np.argsort(np.arctan2(points[:, 1]-center[1], points[:, 0]-center[0]))]


def run_case(R, n, seed, sweeps, mip_seconds=0, patches=0):
    begin = time.perf_counter()
    cells, data = make_partition(R, n)
    made = time.perf_counter()
    graph, row, col = build_graph(data, R)
    graphed = time.perf_counter()
    selected, search = optimize(graph, data, R, seed, sweeps)
    if patches:
        selected, patch_info = improve_by_patches(graph, data, R, n, selected, seed, patches)
        search["patch_improvement"] = patch_info
    mip = None
    if mip_seconds:
        alternative, mip = small_milp(graph, row, col, data["weights"], mip_seconds)
        if data["weights"] @ alternative > data["weights"] @ selected:
            selected = alternative
            search["winning_start"] = "MILP"
    assert not np.any(selected[row] & selected[col])
    selected_ids = np.flatnonzero(selected)
    # Exhaustive recheck without the graph's enclosing-ball pruning.
    assert audit_selected_cells(selected_ids, data["vertices"], data["nv"], data["segments"],
                                data["ns"], data["arcs"], data["na"], R, int(math.ceil(2*R)), TOL) == 0
    certificate = make_inner_certificate(cells, selected, R, n)
    from verify_953_triangle_partition import verify_certificate
    audit = verify_certificate(certificate, fast=True)
    case = f"R{R:g}-n{n}-seed{seed}"+(f"-patch{patches}" if patches else "")
    filename = HERE/f"erdos953-triangle-certificate-{case}.json"
    certificate["experiment"] = case
    filename.write_text(json.dumps(certificate, separators=(",", ":"))+"\n", encoding="utf-8")
    np.savez_compressed(HERE/f"erdos953-triangle-mesh-{case}.npz", triangles=data["triangles"],
                        selected=selected, vertices=data["vertices"], nv=data["nv"], arcs=data["arcs"], na=data["na"],
                        R=R, n=n, areas=data["weights"])
    area = float(data["weights"] @ selected)
    from fractions import Fraction
    result = {"case": case, "R": R, "n": n, "seed": seed, "sweeps_per_temperature": sweeps,
              "patches_per_temperature": patches, "grid_spacing": R/n, "cells": len(cells),
              "curved_boundary_cells": int(np.count_nonzero(data["na"])), "edges": len(row),
              "selected_cells": int(selected.sum()), "selected_curved_cells": int(np.count_nonzero(selected & (data["na"] > 0))),
              "partition_total_area": float(data["weights"].sum()), "disk_area": math.pi*R*R,
              "selected_curved_area": area, "exact_inner_area_fraction": audit["area_fraction"],
              "exact_inner_area_decimal": float(Fraction(audit["area_fraction"])),
              "arc_chord_and_rounding_loss": area-float(Fraction(audit["area_fraction"])),
              "certificate": filename.name, "certificate_audit": audit, "search": search, "MILP": mip,
              "conflict_arithmetic": "analytic extrema, float64 with conservative 2e-10 squared-distance tolerance",
              "boundary_is_actual_circle": True, "global_M_optimality_proved": False,
              "times_seconds": {"mesh": made-begin, "graph": graphed-made, "total": time.perf_counter()-begin}}
    print(json.dumps(result), flush=True)
    return result


def plot_report(results):
    radii = sorted({r["R"] for r in results})
    best = [max((r for r in results if r["R"] == R), key=lambda r: r["exact_inner_area_decimal"]) for R in radii]
    fig, axes = plt.subplots(1, len(best), figsize=(4.5*len(best), 4.8), constrained_layout=True, squeeze=False)
    for ax, result in zip(axes[0], best):
        with np.load(HERE/f"erdos953-triangle-mesh-{result['case']}.npz") as compressed:
            stored = {key: compressed[key] for key in compressed.files}
        polygons, chosen_polygons = [], []
        for i in range(len(stored["selected"])):
            cell = {"vertices": stored["vertices"][i, :stored["nv"][i]],
                    "arcs": stored["arcs"][i, :stored["na"][i]]}
            poly = drawn_cell(cell, result["R"])
            polygons.append(poly)
            if stored["selected"][i]:
                chosen_polygons.append(poly)
        ax.add_collection(PolyCollection(polygons, facecolor="#f4f6f8", edgecolor="#b9c3cb", linewidth=.13))
        ax.add_collection(PolyCollection(chosen_polygons, facecolor="#197fa8", edgecolor="#0d5776", linewidth=.25))
        R = result["R"]
        ax.add_patch(Circle((0, 0), R, fill=False, edgecolor="#344d60", lw=1.2))
        ax.set_aspect("equal")
        ax.set(xlim=(-1.04*R, 1.04*R), ylim=(-1.04*R, 1.04*R), xlabel="x", ylabel="y")
        ax.set_title(f"R={R:g}, {result['cells']} cells\ncurved area={result['selected_curved_area']:.6f}\n"
                     f"exact inner area={result['exact_inner_area_decimal']:.6f}", fontsize=10)
    fig.suptitle("Whole-cell selection on a triangular partition with circular boundary cells")
    fig.savefig(HERE/f"erdos953-triangle-partition-shapes-{STAMP}.png", dpi=190)
    plt.close(fig)
    fig, ax = plt.subplots(figsize=(8.5, 4.8), constrained_layout=True)
    previous = {1.: .8950191291901026, 1.5: 1.0192810180167344, 2.: 1.039132}
    colors = ["#167caa", "#d87520", "#209a6a"]
    for R, color in zip(radii, colors):
        resolutions = sorted({r["n"] for r in results if r["R"] == R})
        subset = [max((r for r in results if r["R"] == R and r["n"] == n),
                      key=lambda r:r["exact_inner_area_decimal"]) for n in resolutions]
        ax.plot([r["cells"] for r in subset], [r["exact_inner_area_decimal"] for r in subset], "o-", color=color, label=f"R={R:g}, partition")
        ax.axhline(previous[R], color=color, ls="--", alpha=.6, label=f"R={R:g}, previous verified lower bound")
    ax.set(xlabel="number of partition cells", ylabel="exactly certified area", title="Refinement changes the whole-cell optimization problem")
    ax.grid(alpha=.2)
    ax.legend(fontsize=8)
    fig.savefig(HERE/f"erdos953-triangle-partition-refinement-{STAMP}.png", dpi=190)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", nargs="+", default=["1:12:79312"], help="R:n:seed")
    parser.add_argument("--sweeps", type=int, default=100)
    parser.add_argument("--mip-seconds", type=float, default=0)
    parser.add_argument("--patches", type=int, default=0)
    parser.add_argument("--append", action="store_true")
    parser.add_argument("--plot-only", action="store_true")
    args = parser.parse_args()
    output = HERE/f"erdos953-triangle-partition-results-{STAMP}.json"
    if (args.append or args.plot_only) and output.exists():
        report = json.loads(output.read_text(encoding="utf-8"))
    else:
        report = {"method": "weighted independent set of closed triangles intersected with the exact disk",
                  "objective": "sum of retained cell areas; whole cells only",
                  "boundary_policy": "actual circle arcs in optimization, rational inner chords only for independent certification",
                  "finite_partition_optimum_is_not_global_M": True, "results": []}
    if not args.plot_only:
        for specification in args.cases:
            rr, nn, seed = specification.split(":")
            result = run_case(float(rr), int(nn), int(seed), args.sweeps, args.mip_seconds, args.patches)
            report["results"] = [r for r in report["results"] if r["case"] != result["case"]]+[result]
            output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    plot_report(report["results"])


if __name__ == "__main__":
    main()
