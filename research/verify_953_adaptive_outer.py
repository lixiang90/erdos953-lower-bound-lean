"""Independent exact adaptive robust-point audit; standard library only."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import itertools
import json

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def intervals(box, D):
    x, y, h = box
    return ((F(x, D), F(x+h, D)), (F(y, D), F(y+h, D)))


def distance_bounds(a, b, D):
    lower, upper = F(0), F(0)
    for (lo, hi), (bottom, top) in zip(intervals(a, D), intervals(b, D)):
        differences = (lo-top, lo-bottom, hi-top, hi-bottom)
        closest = 0 if max(lo, bottom) <= min(hi, top) else min(abs(z) for z in differences)
        lower += closest*closest
        upper += max(z*z for z in differences)
    return lower, upper


def replay(d):
    M, D, delta = d["M"], d["coordinate_denominator"], F(d["delta_fraction"])
    assert isinstance(M, int) and M >= 1 and isinstance(D, int) and D > 0
    assert 0 < delta < F(1, 2)
    initial_side = delta*D/2
    assert initial_side.denominator == 1 and M*D % initial_side.numerator == 0
    s = initial_side.numerator
    leaves = {(x, y, s) for x in range(0, M*D, s) for y in range(0, M*D, s)}
    for round_ in d["refinement_history"]:
        refined = [tuple(b) for b in round_["refined_boxes"]]
        assert len(refined) == len(set(refined)) and set(refined) <= leaves
        for x, y, s in refined:
            assert s >= 2 and s % 2 == 0
            leaves.remove((x, y, s))
            leaves.update((x+dx, y+dy, s//2) for dx in (0, s//2) for dy in (0, s//2))
    assert sorted(leaves) == [tuple(b) for b in d["leaves"]]
    assert sum(s*s for x, y, s in leaves) == (M*D)**2
    assert all(F(2*s*s, D*D) < delta*delta for x, y, s in leaves)
    return M, D, delta, sorted(leaves)


def validate_cut(cut, n, edge, leaves, D, delta):
    if cut["kind"] == "reflection_orbit":
        entries, states = {}, 0
        for member in cut["members"]:
            e, s = validate_cut(member, n, edge, leaves, D, delta)
            states += s
            for ij, value in e.items():
                entries[ij] = entries.get(ij, 0)+value
        return entries, states
    v, H = cut["anchor"], cut["vertices"]
    assert isinstance(v, int) and 0 <= v < n and v not in H
    assert H == sorted(set(H)) and all(isinstance(u, int) and 0 <= u < n for u in H)
    if cut["kind"] == "spatial_capacity":
        x, y, w, h = cut["rectangle_units"]
        assert all(isinstance(z, int) for z in (x, y, w, h)) and w > 0 and h > 0
        assert all(x <= leaves[u][0] and leaves[u][0]+leaves[u][2] <= x+w
                   and y <= leaves[u][1] and leaves[u][1]+leaves[u][2] <= y+h for u in H+[v])
        # Machin's identity and alternating-series bounds certify this lower bound for pi.
        pi_lower = F(314159, 100000)
        machin_lower = 16*sum((F((-1)**j, (2*j+1)*5**(2*j+1)) for j in range(12)), F(0))
        machin_lower -= 4*sum((F((-1)**j, (2*j+1)*239**(2*j+1)) for j in range(3)), F(0))
        assert machin_lower > pi_lower
        width, height = F(w, D), F(h, D)
        micro = F(7, 10)*delta
        assert 2*micro*micro < delta*delta
        ceil = lambda q: -((-q.numerator)//q.denominator)
        micro_bound = ceil(width/micro)*ceil(height/micro)
        disk_bound = (1+4*width*height/(pi_lower*delta*delta)+4*(width+height)/(pi_lower*delta)).__floor__()
        capacity = min(micro_bound, disk_bound)
        assert cut["capacity"] == capacity and cut["alpha"] == capacity-1
        a = capacity-1
        entries = {(v, v): -2*a}
        for u in H:
            entries[v, u] = entries[u, v] = 1
        states = 0
    elif cut["kind"] == "conditional_rank":
        a = cut["alpha"]
        assert isinstance(a, int) and 1 <= a < len(H)
        if a == 1:
            assert all(edge(i, j) for i, j in itertools.combinations(H, 2))
            states = len(H)*(len(H)-1)//2
        else:
            assert len(H) <= 9
            maximum = 0
            for mask in range(1 << len(H)):
                selected = [u for j, u in enumerate(H) if mask >> j & 1]
                if all(not edge(i, j) for i, j in itertools.combinations(selected, 2)):
                    maximum = max(maximum, len(selected))
            assert maximum == a
            states = 1 << len(H)
        entries = {(v, v): -2*a}
        for u in H:
            entries[v, u] = entries[u, v] = 1
    elif cut["kind"] == "boolean_three":
        assert len(H) == 2
        j, k = H
        for zv, zj, zk in itertools.product((0, 1), repeat=3):
            assert 2*(zv*zj+zv*zk-zj*zk-zv*zv) <= 0
        entries = {(v, v): -2, (v, j): 1, (j, v): 1, (v, k): 1, (k, v): 1,
                   (j, k): -1, (k, j): -1}
        states = 8
    else:
        raise AssertionError("Unknown cut")
    return entries, states


def audit(path):
    d = json.loads(path.read_text(encoding="utf-8"))
    assert d["kind"] == "adaptive_robust_point_outer_upper"
    M, D, delta, leaves = replay(d)
    n = len(leaves)
    assert d["vertices"] == n

    @lru_cache(maxsize=None)
    def edge(i, j):
        low, high = distance_bounds(leaves[i], leaves[j], D)
        if high < delta*delta:
            return True
        # Any distance in the square is at most sqrt(2)*M < 2*M.
        return any(low > (k-delta)**2 and high < (k+delta)**2 for k in range(1, 2*M+1))

    K, L = d["matrix_units"], d["gram_factor_units"]
    Q, R = d["matrix_denominator"], d["gram_denominator"]
    assert Q == d["multiplier_denominator"] and R*R % Q == 0
    assert len(K) == len(L) == n and all(len(row) == n for row in K+L)
    assert all(isinstance(x, int) for row in K+L for x in row)
    assert all(L[i][j] == 0 for i in range(n) for j in range(i+1, n))
    correction, states = {}, 0
    for cut in d["cuts"]:
        weight = cut["multiplier_numerator"]
        assert isinstance(weight, int) and weight > 0
        entries, local = validate_cut(cut, n, edge, leaves, D, delta)
        states += local
        for ij, value in entries.items():
            correction[ij] = correction.get(ij, 0)+weight*value
    gamma = d["diagonal_shift_numerator"]
    assert isinstance(gamma, int) and gamma >= 0 and d["diagonal_shift_denominator"] == R*R
    factor = R*R//Q
    diagonal, offsum = [], [0]*n
    nonedges = 0
    for i in range(n):
        diagonal.append(K[i][i]*factor+gamma-sum(x*x for x in L[i]))
        for j in range(i):
            assert K[i][j] == K[j][i]
            if not edge(i, j):
                assert K[i][j]-correction.get((i, j), 0) <= -Q
                nonedges += 1
            g = sum(L[i][k]*L[j][k] for k in range(j+1))
            residual = abs(K[i][j]*factor-g)
            offsum[i] += residual
            offsum[j] += residual
    assert all(di >= off for di, off in zip(diagonal, offsum))
    bound = 1+F(max(K[i][i]-correction.get((i, i), 0) for i in range(n)), Q)+F(gamma, R*R)
    assert bound == F(d["alpha_upper_fraction"])
    assert bound.__floor__() == d["robust_point_upper"]
    assert delta*delta*bound.__floor__() == F(d["delta_squared_point_upper_fraction"])
    assert d["finite_delta_point_upper_proved"] and not d["continuous_area_upper_proved"]
    assert not d["uniform_over_delta_proved"] and not d["new_asymptotic_order_proved"]
    return {"certificate": path.name, "M": M, "delta_fraction": str(delta), "vertices": n,
        "tag": d["tag"], "refinement_rounds_verified": len(d["refinement_history"]),
        "cuts_verified": len(d["cuts"]), "local_states_or_clique_pairs_checked": states,
        "nonedge_matrix_entries_checked": nonedges, "psd_residual_rows_checked": n,
        "upper_fraction": str(bound), "robust_point_upper": bound.__floor__(),
        "graph_independence_upper_proved": not any(c["kind"] == "spatial_capacity" for c in d["cuts"]),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "all_passed": True}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--reuse-existing", action="store_true")
    a = p.parse_args()
    outfile = HERE/f"erdos953-adaptive-outer-independent-audit-{STAMP}.json"
    previous = {}
    if a.reuse_existing and outfile.exists():
        old = json.loads(outfile.read_text())
        if old.get("all_passed"):
            previous = {r["sha256"]: r for r in old["results"] if r.get("all_passed")}
    rows = []
    for path in sorted(HERE.glob(f"erdos953-adaptive-outer-M*-*-{STAMP}.json")):
        sha = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append({**previous[sha], "reused_existing_audit": True} if sha in previous else audit(path))
        print(json.dumps(rows[-1]), flush=True)
    assert rows
    outfile.write_text(json.dumps({"results": rows, "all_passed": True,
        "standard_library_only": True, "finite_delta_point_upper_proved": True,
        "continuous_area_upper_proved": False, "new_asymptotic_order_proved": False,
        "lean_formalized": False}, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
