"""Independent exact audit; standard library only, no optimizer imports."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import itertools
import json
import math

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def conflict(N, a, b, side):
    u, v = abs(a//side-b//side), abs(a%side-b%side)
    lower = max(u-1, 0)**2+max(v-1, 0)**2
    upper = (u+1)**2+(v+1)**2
    return any(lower <= N*N*k*k <= upper for k in range(1, math.isqrt(upper)//N+1))


def validate_cut(cut, M, N):
    n, side = (M*N)**2, M*N
    if cut["kind"] == "reflection_orbit":
        assert isinstance(cut["multiplier_numerator"], int) and cut["multiplier_numerator"] > 0
        entries, states = {}, 0
        assert 1 <= len(cut["members"]) <= 4
        for member in cut["members"]:
            assert member["kind"] in ("conditional_rank", "boolean_three")
            e, s = validate_cut({**member, "multiplier_numerator": cut["multiplier_numerator"]}, M, N)
            states += s
            for ij, value in e.items():
                entries[ij] = entries.get(ij, 0)+value
        return entries, states
    v, H = cut["anchor"], cut["vertices"]
    assert isinstance(v, int) and 0 <= v < n
    assert H == sorted(set(H)) and v not in H
    assert all(isinstance(u, int) and 0 <= u < n for u in H)
    assert isinstance(cut["multiplier_numerator"], int) and cut["multiplier_numerator"] > 0
    if cut["kind"] == "conditional_rank":
        a = cut["alpha"]
        assert isinstance(a, int) and 1 <= a < len(H)
        if a == 1:
            assert all(conflict(N, i, j, side) for i, j in itertools.combinations(H, 2))
            states = len(H)*(len(H)-1)//2
        else:
            assert len(H) <= 9
            maximum = 0
            for mask in range(1 << len(H)):
                chosen = [u for j, u in enumerate(H) if mask >> j & 1]
                if all(not conflict(N, i, j, side) for i, j in itertools.combinations(chosen, 2)):
                    maximum = max(maximum, len(chosen))
            assert maximum == a
            states = 1 << len(H)
        entries = {(v, v): -2*a}
        for u in H:
            entries[v, u] = entries[u, v] = 1
    elif cut["kind"] == "boolean_three":
        assert len(H) == 2
        j, k = H
        # Independent truth-table proof, including patterns forbidden by the graph.
        for zv, zj, zk in itertools.product((0, 1), repeat=3):
            assert 2*(zv*zj+zv*zk-zj*zk-zv*zv) <= 0
        entries = {(v, v): -2, (v, j): 1, (j, v): 1,
                   (v, k): 1, (k, v): 1, (j, k): -1, (k, j): -1}
        states = 8
    else:
        raise AssertionError("Unknown cut")
    return entries, states


def audit(path):
    d = json.loads(path.read_text(encoding="utf-8"))
    M, N = d["M"], d["N"]
    assert isinstance(M, int) and M >= 1 and isinstance(N, int) and N >= 2
    n, side = (M*N)**2, M*N
    assert d["vertices"] == n
    K, L = d["matrix_units"], d["gram_factor_units"]
    Q, R = d["matrix_denominator"], d["gram_denominator"]
    assert Q == d["multiplier_denominator"] and R*R % Q == 0
    assert len(K) == len(L) == n and all(len(row) == n for row in K+L)
    assert all(isinstance(x, int) for row in K+L for x in row)
    assert all(L[i][j] == 0 for i in range(n) for j in range(i+1, n))
    correction = {}
    local_states = 0
    for cut in d["cuts"]:
        entries, states = validate_cut(cut, M, N)
        local_states += states
        for ij, value in entries.items():
            correction[ij] = correction.get(ij, 0)+cut["multiplier_numerator"]*value
    gamma = d["diagonal_shift_numerator"]
    assert isinstance(gamma, int) and gamma >= 0 and d["diagonal_shift_denominator"] == R*R
    factor = R*R//Q
    diagonal, offsum = [], [0]*n
    nonedges = 0
    for i in range(n):
        diagonal.append(K[i][i]*factor+gamma-sum(x*x for x in L[i]))
        for j in range(i):
            assert K[i][j] == K[j][i]
            if not conflict(N, i, j, side):
                assert K[i][j]-correction.get((i, j), 0) <= -Q
                nonedges += 1
            g = sum(L[i][k]*L[j][k] for k in range(j+1))
            residual = abs(K[i][j]*factor-g)
            offsum[i] += residual
            offsum[j] += residual
    assert all(di >= off for di, off in zip(diagonal, offsum))
    bound = 1+F(max(K[i][i]-correction.get((i, i), 0) for i in range(n)), Q)+F(gamma, R*R)
    assert bound == F(d["alpha_upper_fraction"])
    upper = min(bound.__floor__(), side*(N-1))
    assert upper == d["integer_upper"] and F(upper, N*N) == F(d["area_upper_fraction"])
    return {"certificate": path.name, "M": M, "N": N, "tag": d["tag"],
        "cuts_verified": len(d["cuts"]), "local_states_or_clique_pairs_checked": local_states,
        "nonedge_matrix_entries_checked": nonedges, "psd_residual_rows_checked": n,
        "alpha_upper_fraction": str(bound), "integer_upper": upper,
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "all_passed": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--M", type=int)
    parser.add_argument("--N", type=int)
    parser.add_argument("--reuse-existing", action="store_true")
    args = parser.parse_args()
    prefix = f"M{args.M}-N{args.N}" if args.M is not None else "M*-N*"
    rows = []
    previously_verified = {}
    if args.reuse_existing:
        for audit_path in HERE.glob(f"erdos953-theta-cuts-independent-audit*-{STAMP}.json"):
            previous = json.loads(audit_path.read_text())
            if previous.get("all_passed"):
                for row in previous.get("results", []):
                    if row.get("all_passed"):
                        previously_verified[row["sha256"]] = row
    for path in sorted(HERE.glob(f"erdos953-theta-cuts-{prefix}-*-{STAMP}.json")):
        if "lower-witness" in path.name:
            continue
        sha = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append({**previously_verified[sha], "reused_existing_audit": True}
                    if sha in previously_verified else audit(path))
        print(json.dumps(rows[-1]), flush=True)
    assert rows
    report = {"results": rows, "all_passed": True, "standard_library_only": True,
              "continuous_upper_proved": False, "new_asymptotic_order_proved": False,
              "lean_formalized": False}
    witness_path = HERE/f"erdos953-theta-cuts-M2-N4-lower-witness-{STAMP}.json"
    if witness_path.exists():
        witness = json.loads(witness_path.read_text())
        chosen = witness["chosen_cell_indices"]
        assert chosen == sorted(set(chosen)) and witness["count"] == len(chosen)
        assert all(0 <= v < 64 for v in chosen)
        assert all(not conflict(4, i, j, 8) for i, j in itertools.combinations(chosen, 2))
        report["lower_witness"] = {"M": 2, "N": 4, "count": len(chosen),
            "all_pair_distances_verified": True, "global_optimality_proved": False,
            "sha256": hashlib.sha256(witness_path.read_bytes()).hexdigest()}
    suffix = f"-M{args.M}-N{args.N}" if args.M is not None else ""
    (HERE/f"erdos953-theta-cuts-independent-audit{suffix}-{STAMP}.json").write_text(json.dumps(report, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
