"""Standard-library-only independent verifier for square-window certificates.

Reconstructs every offset and cell, enumerates integer-distance candidates
directly, checks rational coverage and strict cosine enclosures. No optimizer
and no floating-point PSD test are used. Analytic implications are in the note.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import hashlib
import json
import math
from verify_953_square_grid_upper import check_cosines, coefficient_up

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def conflict(N, u, v):
    low = max(u-1, 0)**2+max(v-1, 0)**2
    high = (u+1)**2+(v+1)**2
    # Deliberately enumerate all candidate integers, rather than importing the
    # generator's largest-candidate shortcut.
    return any(low <= (N*k)**2 <= high for k in range(1, math.isqrt(high)//N+1))


def graph_data(M, N):
    L = M*N
    vs = [(i, j) for i in range(L) for j in range(L)]
    ds = [(u, v) for u in range(L) for v in range(u+1)
          if (u or v) and not conflict(N, u, v)]
    return vs, ds


def check_structural_cover(M, N):
    L = M*N
    # A compressed certificate C_(j,r)={(r+tN,j):0<=t<M}.
    seen = [0]*(L*L)
    pairs = 0
    for j in range(L):
        for r in range(N):
            C = [(r+t*N, j) for t in range(M)]
            for i, jj in C:
                seen[i*L+jj] += 1
            for (i, _), (ii, _) in combinations(C, 2):
                assert conflict(N, abs(i-ii), 0)
                pairs += 1
    assert all(s == 1 for s in seen)
    # Audit the sharper N-1 row assertion with all residue pairs. The
    # general proof, including the minimum-index argument, is in the note.
    assert conflict(N, N-1, 0)
    return {"M": M, "N": N, "vertices_covered_once": L*L,
            "cliques": M*N*N, "clique_pairs_checked": pairs, "all_passed": True}


def main():
    tables = {}
    audited = []
    nonedges, pairs, covered = 0, 0, 0
    for kind in ("kernel", "clique"):
        manifest = HERE/f"erdos953-square-window-{kind}-results-{STAMP}.json"
        rows = json.loads(manifest.read_text(encoding="utf-8"))["results"]
        for row in rows:
            path = HERE/row["certificate"]
            d = json.loads(path.read_text(encoding="utf-8"))
            M, N = d["M"], d["N"]
            assert isinstance(M, int) and M >= 1 and N >= 2
            vs, ds = graph_data(M, N)
            assert d["side_in_cells"] == M*N and d["vertices"] == len(vs)
            assert d["row_independence_upper"] == M*N*(N-1)
            assert d["row_clique_cover_weight"] == M*N*N
            assert d["finite_grid_upper_only"] and not d["is_continuous_upper_at_this_N"]
            detail = {"M": M, "N": N, "kind": d["kind"], "certificate": path.name,
                      "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            if d["kind"] == "complete":
                assert not ds
                upper = 1
            elif kind == "kernel":
                cosfile = d["cosine_certificate"]
                if cosfile not in tables:
                    cp = HERE/cosfile
                    table = check_cosines(cp)
                    tables[cosfile] = {"data": table,
                                      "sha256": hashlib.sha256(cp.read_bytes()).hexdigest()}
                table = tables[cosfile]["data"]
                T, Q = table["T"], table["denominator"]
                assert T == d["T"] and T > 2*(M*N-1)
                assert d["weight_denominator"] == 10**7 and len(ds) == d["nonedge_displacements"]
                weights = d["weights"]
                assert weights and len({(a, b) for a, b, w in weights}) == len(weights)
                for a, b, w in weights:
                    assert all(isinstance(t, int) for t in (a, b, w))
                    assert 0 <= b <= a <= T//2 and (a or b) and w > 0
                worst = max(sum(w*coefficient_up(table["intervals"], T, a, b, u, v)
                                for a, b, w in weights) for u, v in ds)
                assert worst < 0 and worst == int(d["negative_upper_numerator"])
                assert int(d["negative_upper_denominator"]) == 2*Q*Q*10**7
                bound = 1+F(sum(w for a, b, w in weights)*2*Q*Q, -worst)
                assert bound == F(d["kernel_alpha_upper_fraction"])
                upper = min(bound.__floor__(), M*N*(N-1))
                detail["nonedge_displacements_checked"] = len(ds)
                nonedges += len(ds)
            else:
                Q = d["weight_denominator"]
                assert Q == 10**6
                coverage = [0]*len(vs)
                total, count = 0, 0
                for C, w in d["weighted_cliques"]:
                    assert C and len(C) == len(set(C)) and isinstance(w, int) and w > 0
                    for v in C:
                        assert isinstance(v, int) and 0 <= v < len(vs)
                        coverage[v] += w
                    for a, b in combinations(C, 2):
                        assert conflict(N, abs(vs[a][0]-vs[b][0]), abs(vs[a][1]-vs[b][1]))
                        count += 1
                    total += w
                assert min(coverage) >= Q and F(total, Q) == F(d["total_weight_fraction"])
                assert total//Q == d["cover_integer_upper"]
                upper = min(total//Q, M*N*(N-1))
                detail.update(clique_pairs_checked=count, vertices_covered=len(vs))
                pairs += count
                covered += len(vs)
            assert upper == d["integer_upper"]
            assert F(upper, N*N) == F(d["area_upper_fraction"])
            detail.update(integer_upper=upper, grid_area_upper=d["area_upper_fraction"], all_passed=True)
            audited.append(detail)
    structural = [check_structural_cover(M, N) for M, N in ((1, 2), (2, 3), (4, 8), (16, 4), (32, 12))]
    report = {"all_passed": True, "certificates": audited,
              "nonedge_displacements_checked": nonedges, "clique_pairs_checked": pairs,
              "vertices_covered_by_weighted_cliques": covered,
              "cosine_certificates": [{"file": f, "sha256": x["sha256"], "all_passed": True}
                                      for f, x in sorted(tables.items())],
              "structural_row_covers": structural,
              "scope": "finite square-cell graphs; analytic asymptotic statements in research note",
              "lean_formalized": False}
    path = HERE/f"erdos953-square-window-independent-audit-{STAMP}.json"
    path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k not in ("certificates", "cosine_certificates", "structural_row_covers")}))


if __name__ == "__main__":
    main()
