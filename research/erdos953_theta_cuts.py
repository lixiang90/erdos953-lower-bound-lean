"""Conditional subgraph/Boolean cuts with exact rational PSD certificates.

All SDP iterates are discovery data only. A certificate has a PSD matrix K,
nonnegative rational multipliers mu_l and elementary valid homogeneous cuts
z^T B_l z <= 0. For S=K-sum(mu_l B_l), S_ij<=-1 on nonedges and
S_ii<=t-1 imply alpha<=t. An independent script checks every integer witness.
"""
import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import time
import math
import numpy as np
from numba import njit
from threadpoolctl import threadpool_limits
from erdos953_theta_graph import graph, simplex

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
Q = 10**8
R = 10**6


def alpha_small(adj, vertices):
    """Exhaustive stable-subset enumeration, at most nine vertices."""
    m = len(vertices)
    best = 0
    forbidden = []
    for i in range(m):
        forbidden.append(sum(1 << j for j in range(m) if adj[vertices[i], vertices[j]]))
    stable = [True]*(1 << m)
    for mask in range(1, 1 << m):
        bit = mask & -mask
        i = bit.bit_length()-1
        rest = mask ^ bit
        stable[mask] = stable[rest] and not (forbidden[i] & rest)
        if stable[mask]:
            best = max(best, mask.bit_count())
    return best


def cut_entries(cut, n):
    if cut["kind"] == "reflection_orbit":
        entries = {}
        for member in cut["members"]:
            for idx, value in cut_entries(member, n).items():
                entries[idx] = entries.get(idx, 0)+value
        return {idx: value for idx, value in entries.items() if value}
    v = cut["anchor"]
    entries = {v*n+v: -2*cut.get("alpha", 1)}
    if cut["kind"] in ("conditional_rank", "spatial_capacity"):
        for u in cut["vertices"]:
            entries[v*n+u] = entries[u*n+v] = 1
    elif cut["kind"] == "boolean_three":
        j, k = cut["vertices"]
        for u in (j, k):
            entries[v*n+u] = entries[u*n+v] = 1
        entries[j*n+k] = entries[k*n+j] = -1
    else:
        raise ValueError(cut["kind"])
    return entries


def reflection_orbit(cut, side):
    members = {}
    for rx in (False, True):
        for ry in (False, True):
            def transform(v):
                x, y = divmod(v, side)
                return (side-1-x if rx else x)*side+(side-1-y if ry else y)
            member = {**cut, "anchor": transform(cut["anchor"]),
                      "vertices": sorted(transform(v) for v in cut["vertices"])}
            members[json.dumps(member, sort_keys=True)] = member
    return {"kind": "reflection_orbit", "base_kind": cut["kind"],
            "members": [members[key] for key in sorted(members)]}


def psd_projection(A):
    n = len(A)
    side = math.isqrt(n)
    if n < 512 or side % 2:
        vals, vecs = np.linalg.eigh(A)
        return (vecs*np.maximum(vals, 0))@vecs.T
    # Four character sectors of the two commuting coordinate reflections.
    # This projects onto PSD intersected with reflection-invariant matrices.
    reps = [[(side-1-x if rx else x)*side+(side-1-y if ry else y)
             for x in range(side//2) for y in range(side//2)]
            for rx, ry in ((0, 0), (0, 1), (1, 0), (1, 1))]
    out = np.zeros_like(A)
    for sx, sy in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        signs = [1, sy, sx, sx*sy]
        block = sum(signs[g]*signs[h]*A[np.ix_(reps[g], reps[h])]
                    for g in range(4) for h in range(4))/4
        vals, vecs = np.linalg.eigh(block)
        positive = (vecs*np.maximum(vals, 0))@vecs.T
        for g in range(4):
            for h in range(4):
                out[np.ix_(reps[g], reps[h])] += signs[g]*signs[h]*positive/4
    return out


def arrays(cuts, n):
    width = max([len(cut_entries(c, n)) for c in cuts]+[1])
    indices = np.zeros((len(cuts), width), dtype=np.int64)
    values = np.zeros((len(cuts), width), dtype=np.float64)
    counts = np.zeros(len(cuts), dtype=np.int64)
    norms = np.zeros(len(cuts))
    for c, cut in enumerate(cuts):
        items = list(cut_entries(cut, n).items())
        counts[c] = len(items)
        for j, (idx, val) in enumerate(items):
            indices[c, j], values[c, j] = idx, val
            norms[c] += val*val
    return indices, values, counts, norms


@njit(cache=True)
def project_halfspaces(target, indices, values, counts, norms, warm, sweeps=300):
    """Dykstra/dual coordinate descent; returns nonnegative normal multipliers."""
    z = target.copy()
    multipliers = warm.copy()
    for c in range(len(counts)):
        for j in range(counts[c]):
            z[indices[c, j]] -= multipliers[c]*values[c, j]
    for sweep in range(sweeps):
        largest = 0.0
        for c in range(len(counts)):
            dot = 0.0
            for j in range(counts[c]):
                dot += z[indices[c, j]]*values[c, j]
            nxt = max(0.0, multipliers[c]+dot/norms[c])
            delta = nxt-multipliers[c]
            multipliers[c] = nxt
            largest = max(largest, abs(delta))
            for j in range(counts[c]):
                z[indices[c, j]] -= delta*values[c, j]
        if largest < 1e-11:
            break
    return z, multipliers, sweep+1


def basic_projection(Z, adj):
    X = np.maximum(Z, 0)
    X[adj] = 0
    np.fill_diagonal(X, simplex(np.diag(Z)))
    return X


def propose(adj, cuts, seconds, initial=None):
    n = len(adj)
    previous = initial if isinstance(initial, dict) else None
    Y = np.eye(n)/n if initial is None else (previous["X"].copy() if previous else initial.copy())
    U = np.zeros_like(Y)
    if not cuts:
        rho = float(n)
        start = time.perf_counter()
        for it in range(10000):
            X = basic_projection(Y-U+1/rho, adj)
            nextY = psd_projection(X+U)
            U += X-nextY
            residual = np.linalg.norm(X-nextY)
            change = rho*np.linalg.norm(nextY-Y)
            Y = nextY
            if (residual < 2e-9 and change < 2e-8) or time.perf_counter()-start > seconds:
                break
        return -rho*U, np.zeros(0), X, {"iterations": it+1,
            "residual_diagnostic": float(residual), "change_diagnostic": float(change),
            "objective_diagnostic": float(X.sum()), "seconds": time.perf_counter()-start}
    ind, val, count, norms = arrays(cuts, n)
    # Warm-up compilation is excluded from the numerical exploration budget.
    project_halfspaces(Y.ravel(), ind, val, count, norms, np.zeros(len(cuts)), 1)
    Z = Y.copy()
    V = np.zeros_like(Y)
    warm = np.zeros(len(cuts))
    rho = n/2.0
    if previous is not None:
        U = -previous["K"]/rho
        warm[:len(previous["mu"])] = previous["mu"]/rho
        for c in range(len(previous["mu"])):
            for j in range(count[c]):
                V.ravel()[ind[c, j]] += warm[c]*val[c, j]
        Z, warm, inner = project_halfspaces((Y+V).ravel(), ind, val, count, norms, warm)
        Z = Z.reshape(n, n)
        V = Y+V-Z
    start = time.perf_counter()
    for it in range(10000):
        X = basic_projection((Y+Z-U-V)/2+1/(2*rho), adj)
        nextY = psd_projection(X+U)
        nextZ, warm, inner = project_halfspaces((X+V).ravel(), ind, val, count, norms, warm)
        nextZ = nextZ.reshape(n, n)
        U += X-nextY
        V = (X+V)-nextZ
        residual = math.hypot(np.linalg.norm(X-nextY), np.linalg.norm(X-nextZ))
        change = rho*math.hypot(np.linalg.norm(nextY-Y), np.linalg.norm(nextZ-Z))
        Y, Z = nextY, nextZ
        if (residual < 2e-9 and change < 2e-8) or time.perf_counter()-start > seconds:
            break
    return -rho*U, rho*warm, X, {"iterations": it+1,
        "residual_diagnostic": float(residual), "change_diagnostic": float(change),
        "objective_diagnostic": float(X.sum()), "projection_last_sweeps": inner,
        "seconds": time.perf_counter()-start}


def separate(adj, X, existing, limit=100, seed=793, M=None, N=None):
    """Search for violated clique/rank and three-point constraints."""
    n = len(adj)
    rng = np.random.default_rng(seed)
    diagonal = np.diag(X)
    known = {json.dumps(c, sort_keys=True) for c in existing}
    candidates = {}
    def offer(cut):
        if n >= 512:
            cut = reflection_orbit(cut, math.isqrt(n))
        key = json.dumps(cut, sort_keys=True)
        if key in known or key in candidates:
            return
        entries = cut_entries(cut, n)
        violation = sum(v*X.ravel()[i] for i, v in entries.items())
        if violation > 2e-7:
            score = violation/math.sqrt(sum(v*v for v in entries.values()))
            candidates[key] = (score, cut)
    # Full row/column residue cliques grow with physical window size M.
    # They are not truncated to a fixed hot-neighbour list.
    if M is not None and M >= 2:
        side = M*N
        for axis in (0, 1):
            for fixed in range(side):
                for residue in range(N):
                    C = [(residue+t*N)*side+fixed if axis == 0
                         else fixed*side+residue+t*N for t in range(M)]
                    violations = X[:, C].sum(axis=1)-diagonal
                    for v in np.flatnonzero(violations > 1e-7):
                        H = sorted(u for u in C if u != v)
                        if len(H) >= 2:
                            offer({"kind": "conditional_rank", "anchor": int(v),
                                   "vertices": H, "alpha": 1})
    # Each anchor gets greedy cliques and five-/seven-/nine-vertex rank cuts.
    for v in range(n):
        eligible = np.flatnonzero(~adj[v] & (np.arange(n) != v))
        if len(eligible) < 2:
            continue
        hot = eligible[np.argsort(-X[v, eligible])[:min(24, len(eligible))]]
        for rep in range(8):
            order = hot if rep == 0 else rng.permutation(hot)
            clique = []
            for u in order:
                if all(adj[u, w] for w in clique):
                    clique.append(int(u))
            if len(clique) >= 2:
                offer({"kind": "conditional_rank", "anchor": v,
                       "vertices": sorted(clique), "alpha": 1})
        for size in (5, 7, 9):
            if len(hot) < size:
                continue
            for rep in range(3):
                H = sorted(int(u) for u in (hot[:size] if rep == 0 else rng.choice(hot, size, replace=False)))
                a = alpha_small(adj, H)
                if a < size:
                    offer({"kind": "conditional_rank", "anchor": v, "vertices": H, "alpha": a})
        # Every ordered anchor represents one of the three Boolean inequalities.
        violation = X[v, :, None]+X[v, None, :]-X-diagonal[v]
        violation[v, :] = violation[:, v] = -np.inf
        np.fill_diagonal(violation, -np.inf)
        for flat in np.argpartition(violation.ravel(), -4)[-4:]:
            j, k = divmod(int(flat), n)
            offer({"kind": "boolean_three", "anchor": v, "vertices": sorted([j, k])})
    chosen = sorted(candidates.values(), key=lambda item: -item[0])[:limit]
    return [c for s, c in chosen], {"violated_candidates": len(candidates),
        "new_cuts": len(chosen), "top_normalized_violation": chosen[0][0] if chosen else 0,
        "conditional_rank": sum(c.get("base_kind", c["kind"]) == "conditional_rank" for s, c in chosen),
        "boolean_three": sum(c.get("base_kind", c["kind"]) == "boolean_three" for s, c in chosen)}


def certify(M, N, adj, K, cuts, multipliers, tag, diagnostics):
    n = len(adj)
    mu = np.maximum(0, np.rint(multipliers*Q)).astype(np.int64)
    correction = np.zeros((n, n), dtype=np.int64)
    active = []
    for cut, weight in zip(cuts, mu):
        if weight:
            for idx, value in cut_entries(cut, n).items():
                correction.ravel()[idx] += int(weight)*value
            active.append({**cut, "multiplier_numerator": int(weight)})
    K = (K+K.T)/2
    units = np.rint(K*Q).astype(np.int64)
    nonedge = ~adj & ~np.eye(n, dtype=bool)
    units[nonedge] = np.minimum(units[nonedge], -Q+correction[nonedge])
    A = units.astype(float)/Q
    shift = max(1e-5, -float(np.linalg.eigvalsh(A)[0])+1e-5)
    L = np.linalg.cholesky(A+shift*np.eye(n))
    lint = np.rint(L*R).astype(np.int64)
    assert n*int(np.max(np.abs(lint)))**2 < 2**62
    factor = R*R//Q
    residual = units*factor-lint@lint.T
    diagonal = np.diag(residual).copy()
    offsum = np.sum(np.abs(residual), axis=1)-np.abs(diagonal)
    gamma = max(0, int(np.max(offsum-diagonal)))+1
    assert np.all(diagonal+gamma >= offsum)
    t = 1+F(int(np.max(np.diag(units-correction))), Q)+F(gamma, R*R)
    upper = min(t.__floor__(), M*N*(N-1))
    cert = {"M": M, "N": N, "vertices": n, "tag": tag,
        "kind": "theta_prime_with_homogeneous_valid_cuts", "cuts": active,
        "multiplier_denominator": Q, "matrix_denominator": Q,
        "matrix_units": units.tolist(), "gram_denominator": R,
        "gram_factor_units": lint.tolist(), "diagonal_shift_numerator": gamma,
        "diagonal_shift_denominator": R*R,
        "alpha_upper_fraction": str(t), "integer_upper": upper,
        "area_upper_fraction": str(F(upper, N*N)), "finite_graph_only": True,
        "theta_optimality_claimed": False, "continuous_upper_proved": False,
        "lean_formalized": False, "diagnostics": diagnostics}
    filename = f"erdos953-theta-cuts-M{M}-N{N}-{tag}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert, separators=(",", ":")), encoding="utf-8")
    brief = {k: v for k, v in cert.items() if k not in ("matrix_units", "gram_factor_units", "cuts")}
    brief.update(certificate=filename, active_cuts=len(active),
        cut_counts={kind: sum(c.get("base_kind", c["kind"]) == kind for c in active)
                    for kind in ("conditional_rank", "boolean_three")},
        normalized_by_sqrt_M=float(F(upper, N*N))/math.sqrt(M))
    print(json.dumps(brief), flush=True)
    return brief


def run(M, N, seconds=15, rounds=2, batch=100, variant=""):
    adj = graph(M, N)
    cuts = []
    rows = []
    K, mu, X, diagnostics = propose(adj, cuts, seconds)
    prefix = variant+"-" if variant else ""
    rows.append(certify(M, N, adj, K, cuts, mu, prefix+"control", diagnostics))
    for round_index in range(1, rounds+1):
        added, separation = separate(adj, X, cuts, batch, seed=793+round_index, M=M, N=N)
        if not added:
            break
        cuts.extend(added)
        K, mu, X, diagnostics = propose(adj, cuts, seconds,
                                       initial={"X": X, "K": K, "mu": mu})
        diagnostics.update(separation=separation, requested_cuts=len(cuts))
        rows.append(certify(M, N, adj, K, cuts, mu, prefix+f"r{round_index}", diagnostics))
    result = {"M": M, "N": N, "results": rows,
              "best_integer_upper": min(row["integer_upper"] for row in rows),
              "scope": "finite square-cell conflict graph only"}
    suffix = "-"+variant if variant else ""
    path = HERE/f"erdos953-theta-cuts-results-M{M}-N{N}{suffix}-{STAMP}.json"
    path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--M", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--seconds", type=float, default=15)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--batch", type=int, default=100)
    parser.add_argument("--variant", default="")
    args = parser.parse_args()
    with threadpool_limits(limits=1):
        run(args.M, args.N, args.seconds, args.rounds, args.batch, args.variant)
