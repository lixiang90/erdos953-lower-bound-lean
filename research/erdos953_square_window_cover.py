"""Exact certificates for the MN by MN cell graph in a square of side M.

The window has ordinary boundaries. Fourier periodicity parametrizes a PSD
kernel; it does not add wraparound edges. Finite-N upper bounds are not
continuous upper bounds at that N. See the accompanying research note.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import argparse
import json
import random
import time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from erdos953_square_grid_upper import edge, cosines, exact_kernel_bound, WEIGHT_Q
from erdos953_square_clique_upper import adjacency, partition

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
Q = 10**6


def square_data(M, N):
    assert isinstance(M, int) and M >= 1 and N >= 2
    L = M*N
    vs = [(i, j) for i in range(L) for j in range(L)]
    ds = [(u, v) for u in range(L) for v in range(u+1)
          if (u or v) and not edge(N, u, v)]
    return vs, ds


def common(M, N):
    L = M*N
    return {"M": M, "N": N, "side_in_cells": L, "vertices": L*L,
            "window": "closed square [0,M]^2 with ordinary boundaries",
            "whole_closed_cells": True, "row_clique_cover_weight": M*N*N,
            "row_independence_upper": L*(N-1),
            "finite_grid_upper_only": True,
            "is_continuous_upper_at_this_N": False, "lean_formalized": False}


def save(cert, started):
    filename = f"erdos953-square-window-{cert['kind']}-M{cert['M']}-N{cert['N']}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert, separators=(",", ":")), encoding="utf-8")
    row = {k: v for k, v in cert.items() if k not in ("weights", "weighted_cliques", "independent_cells")}
    row.update(certificate=filename, seconds=time.perf_counter()-started)
    print(json.dumps(row), flush=True)
    return row


def kernel(M, N):
    started = time.perf_counter()
    vs, ds = square_data(M, N)
    base = common(M, N)
    row_upper = base["row_independence_upper"]
    if not ds:
        return save({**base, "kind": "complete", "integer_upper": 1,
                     "area_upper_fraction": str(F(1, N*N)),
                     "nonedge_displacements": 0}, started)
    # T is divisible by 4 and strictly exceeds twice the coordinate span.
    T = 4*((M*N+1)//2)+4
    features = np.array([(a, b) for a in range(T//2+1) for b in range(a+1)
                         if a or b], dtype=np.int32)
    table, cosfile = cosines(T)
    a, b = features.T
    u, v = np.array(ds, dtype=np.int32).T
    C = np.cos(2*np.pi*u[:, None]*a/T)*np.cos(2*np.pi*v[:, None]*b/T)
    C += np.cos(2*np.pi*u[:, None]*b/T)*np.cos(2*np.pi*v[:, None]*a/T)
    C *= .5
    result = linprog(np.ones(len(features)), A_ub=C, b_ub=-np.ones(len(ds)),
                     bounds=(0, None), method="highs-ipm",
                     options={"primal_feasibility_tolerance": 1e-9, "time_limit": 55})
    # Only feasibility is needed for an upper certificate; rational interval
    # verification below is authoritative even if optimization stopped early.
    assert result.x is not None, result.message
    units = np.maximum(np.rint(result.x*WEIGHT_Q), 0).astype(np.int64)
    keep = units > 0
    features, units = features[keep], units[keep]
    bound, worst, delta = exact_kernel_bound(ds, features, units, table)
    upper = min(bound.__floor__(), row_upper)
    cert = {**base, "kind": "kernel", "T": T, "cosine_certificate": cosfile,
            "weight_denominator": WEIGHT_Q,
            "weights": [[int(a), int(b), int(w)] for (a, b), w in zip(features, units)],
            "nonedge_displacements": len(ds), "frequencies_used": len(units),
            "negative_upper_numerator": str(worst),
            "negative_upper_denominator": str(2*(2**24)**2*WEIGHT_Q),
            "worst_displacement": list(delta), "kernel_alpha_upper_fraction": str(bound),
            "integer_upper": upper, "area_upper_fraction": str(F(upper, N*N)),
            "solver_objective_diagnostic": float(result.fun)}
    return save(cert, started)


def clique(M, N):
    started = time.perf_counter()
    vs, _ = square_data(M, N)
    L = M*N
    adj = adjacency(N, vs)
    rng = random.Random(9531000+100*M+N)
    # Include the exact row-residue and column-residue partitions.
    pool = set()
    for j in range(L):
        for r in range(N):
            pool.add(tuple(i*L+j for i in range(r, L, N)))
    for i in range(L):
        for r in range(N):
            pool.add(tuple(i*L+j for j in range(r, L, N)))
    counts = []
    for _ in range(8):
        parts = partition(adj, rng)
        counts.append(len(parts))
        pool.update(parts)
    pool = sorted(pool)
    rr, cc = [], []
    for c, C in enumerate(pool):
        for v in C:
            rr.append(v)
            cc.append(c)
    A = coo_matrix((-np.ones(len(rr)), (rr, cc)), shape=(len(vs), len(pool))).tocsr()
    result = linprog(np.ones(len(pool)), A_ub=A, b_ub=-np.ones(len(vs)), bounds=(0, None),
                     method="highs", options={"time_limit": 55})
    assert result.success, result.message
    units = np.maximum(np.ceil(result.x*Q), 0).astype(np.int64)
    chosen = [(list(C), int(w)) for C, w in zip(pool, units) if w > 0]
    coverage = [0]*len(vs)
    for C, w in chosen:
        for v in C:
            coverage[v] += w
        for a, b in combinations(C, 2):
            assert edge(N, abs(vs[a][0]-vs[b][0]), abs(vs[a][1]-vs[b][1]))
    for v, w in enumerate(coverage):
        if w < Q:
            chosen.append(([v], Q-w))
    total = sum(w for C, w in chosen)
    cover_upper = total//Q
    upper = min(cover_upper, L*(N-1))
    return save({**common(M, N), "kind": "clique", "weight_denominator": Q,
                 "weighted_cliques": chosen, "total_weight_fraction": str(F(total, Q)),
                 "cover_integer_upper": cover_upper, "integer_upper": upper,
                 "area_upper_fraction": str(F(upper, N*N)),
                 "partition_counts": counts, "cliques_used": len(chosen)}, started)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=("kernel", "clique"), default="kernel")
    parser.add_argument("--M", type=int)
    parser.add_argument("--N", type=int)
    args = parser.parse_args()
    if args.M is not None:
        cases = [(args.M, args.N)]
    elif args.kind == "kernel":
        cases = [(1, N) for N in (4, 8, 12, 16, 24, 32)]
        cases += [(M, 4) for M in (2, 4, 8, 16)]
        cases += [(M, 8) for M in (2, 4, 8)]
        cases += [(2, 12), (2, 16), (4, 12)]
    else:
        cases = [(1, N) for N in (4, 8, 12, 16, 24, 32)]
        cases += [(2, 4), (2, 8), (2, 12), (4, 4), (4, 8), (8, 4)]
    rows = []
    path = HERE/f"erdos953-square-window-{args.kind}-results-{STAMP}.json"
    for M, N in cases:
        cert_path = HERE/f"erdos953-square-window-{args.kind}-M{M}-N{N}-{STAMP}.json"
        if cert_path.exists():
            cert = json.loads(cert_path.read_text(encoding="utf-8"))
            row = {k: v for k, v in cert.items() if k not in ("weights", "weighted_cliques", "independent_cells")}
            row.update(certificate=cert_path.name, recovered_existing_certificate=True)
            rows.append(row)
        else:
            rows.append((kernel if args.kind == "kernel" else clique)(M, N))
        path.write_text(json.dumps({"results": rows, "finite_grid_upper_only": True,
                                  "not_a_uniform_continuous_upper_certificate": True}, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
