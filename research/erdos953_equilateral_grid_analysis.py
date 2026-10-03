"""Exact integer-distance graphs on an equilateral lattice and its triangles.

Axial coordinates (a,b) mean h*(a+b/2, sqrt(3)*b/2). With h=1/q,
all conflict predicates use integer arithmetic, including vertex-to-edge
minima for full triangles. Finite independent sets are heuristic lower
bounds unless they reach the proved horizontal-row upper bound.
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
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

from erdos953_triangle_partition_search import weighted_greedy, weighted_local

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
set_num_threads(8)
TYPES = np.array([[[0,0],[1,0],[0,1]], [[1,0],[1,1],[0,1]]], dtype=np.int64)


def norm(a, b):
    return a*a+a*b+b*b


def triangle_minmax_python(first, second):
    """Independent pure-integer audit: returns (4*minimum^2, maximum^2)."""
    maximum = max(norm(int(a[0])-int(b[0]), int(a[1])-int(b[1]))
                  for a in first for b in second)
    minimum4 = 4*maximum
    for vertices, edges in ((first, second), (second, first)):
        for p in vertices:
            for index, a in enumerate(edges):
                b = edges[(index+1) % 3]
                wa, wb = int(p[0])-int(a[0]), int(p[1])-int(a[1])
                va, vb = int(b[0])-int(a[0]), int(b[1])-int(a[1])
                assert norm(va, vb) == 1
                dot2 = 2*wa*va+wa*vb+wb*va+2*wb*vb
                if dot2 <= 0:
                    value = 4*norm(wa, wb)
                elif dot2 >= 2:
                    value = 4*norm(wa-va, wb-vb)
                else:
                    assert dot2 == 1
                    value = 4*norm(wa, wb)-1
                minimum4 = min(minimum4, value)
    return minimum4, maximum


def audit_cells(labels, q, R):
    triangles = [[tuple(map(int, v)) for v in TYPES[t]+np.array([a,b])]
                 for a,b,t in labels]
    assert len({tuple(map(int, x)) for x in labels}) == len(labels)
    radius2 = (q*R)**2
    for triangle in triangles:
        assert all(norm(a,b) < radius2 for a,b in triangle)
    pairs = 0
    for i, first in enumerate(triangles):
        for second in triangles[i+1:]:
            minimum4, maximum = triangle_minmax_python(first, second)
            k = math.isqrt(maximum)//q
            assert k < 1 or minimum4 > 4*(q*k)**2
            pairs += 1
    return pairs


@njit(cache=True)
def minmax(first, second):
    maximum, minimum4 = 0, np.int64(2**60)
    for i in range(3):
        for j in range(3):
            a, b = first[i,0]-second[j,0], first[i,1]-second[j,1]
            maximum = max(maximum, a*a+a*b+b*b)
    for reverse in range(2):
        vertices = first if reverse == 0 else second
        edges = second if reverse == 0 else first
        for i in range(3):
            for j in range(3):
                wa, wb = vertices[i,0]-edges[j,0], vertices[i,1]-edges[j,1]
                va = edges[(j+1)%3,0]-edges[j,0]
                vb = edges[(j+1)%3,1]-edges[j,1]
                dot2 = 2*wa*va+wa*vb+wb*va+2*wb*vb
                if dot2 <= 0:
                    value = 4*(wa*wa+wa*wb+wb*wb)
                elif dot2 >= 2:
                    wa, wb = wa-va, wb-vb
                    value = 4*(wa*wa+wa*wb+wb*wb)
                else:
                    value = 4*(wa*wa+wa*wb+wb*wb)-1
                minimum4 = min(minimum4, value)
    return minimum4, maximum


@njit(cache=True, parallel=True)
def conflict_mask(q, extent, types):
    width = 2*extent+1
    result = np.zeros((2,2,width,width), dtype=np.uint8)
    for ii in prange(4*width*width):
        i = np.int64(ii)
        x, y = (i//width)%width, i%width
        t, u = i//(width*width)//2, i//(width*width)%2
        second = types[u].copy()
        second[:,0] += x-extent
        second[:,1] += y-extent
        lo4, hi = minmax(types[t], second)
        root = int(math.sqrt(hi))
        while (root+1)**2 <= hi:
            root += 1
        while root*root > hi:
            root -= 1
        k = root//q
        if k >= 1 and lo4 <= 4*(k*q)**2:
            result[t,u,x,y] = 1
    return result


@njit(cache=True, parallel=True)
def flags_vertices(points):
    n = len(points)
    flags = np.zeros((n,n), dtype=np.uint8)
    for ii in prange(n):
        i = np.int64(ii)
        for j in range(i+1,n):
            a,b = points[j,0]-points[i,0], points[j,1]-points[i,1]
            value = a*a+a*b+b*b
            k = int(math.sqrt(value))
            if k*k == value:
                flags[i,j] = 1
    return flags


@njit(cache=True, parallel=True)
def flags_cells(labels, mask, extent):
    n = len(labels)
    flags = np.zeros((n,n), dtype=np.uint8)
    for ii in prange(n):
        i = np.int64(ii)
        for j in range(i+1,n):
            a = labels[j,0]-labels[i,0]+extent
            b = labels[j,1]-labels[i,1]+extent
            flags[i,j] = mask[labels[i,2],labels[j,2],a,b]
    return flags


def to_graph(flags):
    row,col = np.nonzero(flags)
    row,col = row.astype(np.int32),col.astype(np.int32)
    graph = coo_matrix((np.ones(2*len(row), dtype=np.int8),
                       (np.r_[row,col],np.r_[col,row])), shape=flags.shape).tocsr()
    graph.sort_indices()
    return graph,row,col


def optimize(graph, xy, initial, seed, sweeps):
    rng = np.random.default_rng(seed)
    n = len(initial)
    weights = np.ones(n)
    best = initial.copy()
    starts = [initial]
    degrees = np.diff(graph.indptr)
    for trial in range(12):
        if trial < 4:
            order = np.argsort(degrees+rng.random(n)*max(1,degrees.mean())*.1)
        elif trial < 8:
            center = xy[rng.integers(n)]
            order = np.argsort(np.linalg.norm(xy-center,axis=1))
        else:
            order = rng.permutation(n)
        selected = weighted_greedy(graph.indptr,graph.indices,order,np.zeros(n,dtype=np.bool_))
        if selected.sum() > best.sum():
            best = selected
    starts.extend([best])
    for trial, start in enumerate(starts):
        selected = weighted_local(graph.indptr,graph.indices,weights,start,seed+trial,sweeps)
        if selected.sum() > best.sum():
            best = selected
    return best


def planar(points,q=1):
    return np.column_stack(((points[:,0]+points[:,1]/2)/q, math.sqrt(3)*points[:,1]/(2*q)))


def vertex_case(R, sweeps, mip_seconds):
    started = time.perf_counter()
    extent = math.ceil(2*R/math.sqrt(3))
    points = np.array([(a,b) for a in range(-extent,extent+1)
                       for b in range(-extent,extent+1) if norm(a,b) <= R*R], dtype=np.int64)
    flags = flags_vertices(points)
    graph,row,col = to_graph(flags)
    del flags
    initial = points[:,0] == points[:,1]
    best = optimize(graph,planar(points),initial,953000+R,sweeps)
    row_upper = len(np.unique(points[:,1]))
    solver = None
    if mip_seconds and R <= 8 and best.sum() < row_upper:
        # The three families of lattice-direction cliques strengthen the LP.
        er,ec = list(np.repeat(np.arange(len(row)),2)),list(np.column_stack((row,col)).ravel())
        constraint_count = len(row)
        for values in (points[:,0],points[:,1],points[:,0]+points[:,1]):
            for value in np.unique(values):
                ids = np.flatnonzero(values == value)
                er.extend([constraint_count]*len(ids))
                ec.extend(ids.tolist())
                constraint_count += 1
        matrix = coo_matrix((np.ones(len(er)),(er,ec)),shape=(constraint_count,len(points))).tocsc()
        result = milp(-np.ones(len(points)),integrality=np.ones(len(points)),
                      bounds=Bounds(0,1),constraints=LinearConstraint(matrix,-np.inf,1),
                      options={"time_limit":mip_seconds,"mip_rel_gap":0.})
        solver = {"status":int(result.status),"message":result.message,
                  "dual_bound":float(-result.mip_dual_bound) if result.mip_dual_bound is not None else None}
        if result.x is not None:
            candidate = result.x > .5
            assert not np.any(candidate[row] & candidate[col])
            if candidate.sum() > best.sum():
                best = candidate
    ids = np.flatnonzero(best)
    minimum_gap = math.inf
    minimum_gap_pair = None
    for position,i in enumerate(ids):
        for j in ids[position+1:]:
            a,b = map(int,points[i]-points[j])
            value = norm(a,b)
            root = math.isqrt(value)
            assert value != root*root
            distance = math.sqrt(value)
            gap = min(distance-root,root+1-distance)
            if gap < minimum_gap:
                minimum_gap,minimum_gap_pair = gap,[value,root]
    assert best.sum() <= row_upper
    return {"model":"vertices_h1","R":R,"nodes":len(points),"edges":len(row),
            "line_lower":int(initial.sum()),"heuristic_lower":int(best.sum()),
            "proved_row_upper":row_upper,"optimal_by_row_bound":bool(best.sum()==row_upper),
            "minimum_integer_gap_float":minimum_gap,"gap_squared_norm_and_floor":minimum_gap_pair,
            "solver":solver,"selected_axial_points":points[best].tolist(),
            "seconds":time.perf_counter()-started}


def cell_case(R,q,sweeps):
    started = time.perf_counter()
    extent = math.ceil(2*q*R/math.sqrt(3))+2
    labels = []
    for a in range(-extent,extent+1):
        for b in range(-extent,extent+1):
            for t in range(2):
                triangle = TYPES[t]+np.array([a,b])
                if all(norm(int(v[0]),int(v[1])) < (q*R)**2 for v in triangle):
                    labels.append((a,b,t))
    labels = np.array(labels,dtype=np.int64)
    mask_extent = int(max(np.ptp(labels[:,0]),np.ptp(labels[:,1])))
    mask = conflict_mask(q,mask_extent,TYPES)
    flags = flags_cells(labels,mask,mask_extent)
    graph,row,col = to_graph(flags)
    del flags,mask
    triangles = TYPES[labels[:,2]]+labels[:,:2,None].transpose(0,2,1)
    xy = planar(triangles.mean(axis=1),q)
    initial = np.array([all(norm(int(a),int(b))*4 < q*q for a,b in tri)
                        for tri in triangles],dtype=np.bool_)
    assert not np.any(initial[row] & initial[col])
    best = optimize(graph,xy,initial,953100+q*100+R,sweeps)
    assert not np.any(best[row] & best[col])
    pairs = audit_cells(labels[best],q,R)
    count = int(best.sum())
    return {"model":"whole_triangles","R":R,"q":q,"h":1/q,"nodes":len(labels),
            "edges":len(row),"heuristic_lower":count,
            "area_sqrt3_coefficient_numerator":count,"area_sqrt3_coefficient_denominator":4*q*q,
            "area_lower":count*math.sqrt(3)/(4*q*q),"exact_pair_audit":pairs,
            "selected_axial_triangles":labels[best].tolist(),"seconds":time.perf_counter()-started}


def check_predicates():
    rng = np.random.default_rng(953)
    for _ in range(1200):
        t,u = rng.integers(0,2,size=2)
        shift = rng.integers(-100,101,size=2)
        first,second = TYPES[t],TYPES[u]+shift
        expected = triangle_minmax_python(first,second)
        actual = tuple(map(int,minmax(first,second)))
        assert actual == expected
    for a in range(-80,81):
        for b in range(-80,81):
            value = 2*norm(a,b)
            assert value == 0 or math.isqrt(value)**2 != value
    # Same-centroid unit-distance test and an adjacent-cell shared-boundary test.
    assert triangle_minmax_python(TYPES[0],TYPES[0]+np.array([4,0]))[0] <= 4*4**2
    return {"random_minmax_comparisons":1200,"sqrt2_scaled_difference_vectors":161**2,
            "integer_arithmetic_predicates":"passed"}


def plot(results):
    vertices = [r for r in results if r["model"] == "vertices_h1"]
    cells = [r for r in results if r["model"] == "whole_triangles"]
    fig,axes = plt.subplots(1,3,figsize=(15,4.5))
    r = vertices[-1]
    xy = planar(np.array(r["selected_axial_points"]))
    axes[0].scatter(xy[:,0],xy[:,1],s=12)
    axes[0].add_patch(plt.Circle((0,0),r["R"],fill=False,color="black",lw=1))
    axes[0].set_title(f"Exact-distance vertices: R={r['R']}, K={len(xy)}")
    axes[0].set_aspect("equal")
    x = np.array([r["R"] for r in vertices])
    axes[1].loglog(x,[r["heuristic_lower"] for r in vertices],"o-",label="Verified independent set")
    axes[1].loglog(x,[r["proved_row_upper"] for r in vertices],"--",label="Proved row upper bound")
    axes[1].loglog(x,[r["line_lower"] for r in vertices],":",label="Explicit 30 degree line")
    axes[1].set_xlabel("Physical radius R")
    axes[1].set_ylabel("Vertex count")
    axes[1].legend(fontsize=8)
    axes[1].grid(alpha=.2)
    r = next((r for r in cells if r["R"]==4 and r["q"]==8),cells[-1])
    labels = np.array(r["selected_axial_triangles"],dtype=np.int64)
    triangles = TYPES[labels[:,2]]+labels[:,:2,None].transpose(0,2,1)
    polygons = [planar(t,r["q"]) for t in triangles]
    axes[2].add_collection(PolyCollection(polygons,facecolors="#246fba",edgecolors="#eeeeee",lw=.25))
    axes[2].add_patch(plt.Circle((0,0),r["R"],fill=False,color="black",lw=1))
    axes[2].set_xlim(-r["R"]*1.05,r["R"]*1.05)
    axes[2].set_ylim(-r["R"]*1.05,r["R"]*1.05)
    axes[2].set_aspect("equal")
    axes[2].set_title(f"Whole cells: R={r['R']}, h=1/{r['q']}\nCertified area = {r['area_lower']:.6f}")
    fig.tight_layout()
    path = HERE/f"erdos953-equilateral-grid-analysis-{STAMP}.png"
    fig.savefig(path,dpi=180)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sweeps",type=int,default=30)
    parser.add_argument("--mip-seconds",type=float,default=3)
    args = parser.parse_args()
    audit = check_predicates()
    results = []
    destination = HERE/f"erdos953-equilateral-grid-results-{STAMP}.json"
    cases = [("vertex",R,1) for R in (1,2,3,4,6,8,12,16,24,32,48,64)]
    cases += [("cell",R,q) for q, radii in ((4,(1,2,4,8)),(8,(1,2,4))) for R in radii]
    for mode,R,q in cases:
        result = vertex_case(R,args.sweeps,args.mip_seconds) if mode=="vertex" else cell_case(R,q,args.sweeps)
        results.append(result)
        destination.write_text(json.dumps({"predicate_audit":audit,"results":results},indent=2),encoding="utf-8")
        print(json.dumps({k:v for k,v in result.items() if not k.startswith("selected_")}),flush=True)
    plot(results)


if __name__ == "__main__":
    main()
