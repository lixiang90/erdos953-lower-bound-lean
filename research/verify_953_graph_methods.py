"""Standard-library independent audit of full PSD and padded spectral bounds."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
from verify_953_square_grid_upper import check_cosines

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def edge(N, u, v):
    lo = max(u-1, 0)**2+max(v-1, 0)**2
    hi = (u+1)**2+(v+1)**2
    return any(lo <= (N*k)**2 <= hi for k in range(1, math.isqrt(hi)//N+1))


def audit_theta(row):
    path = HERE/row["certificate"]
    d = json.loads(path.read_text())
    M, N = d["M"], d["N"]
    side = M*N
    n = side*side
    K, L = d["matrix_units"], d["gram_factor_units"]
    Q, R = d["matrix_denominator"], d["gram_denominator"]
    assert n == d["vertices"] and len(K) == len(L) == n and R*R % Q == 0
    assert all(len(r) == n for r in K+L)
    assert all(isinstance(x, int) for r in K+L for x in r)
    gamma = d["diagonal_shift_numerator"]
    assert isinstance(gamma, int) and gamma >= 0 and d["diagonal_shift_denominator"] == R*R
    assert all(L[i][j] == 0 for i in range(n) for j in range(i+1, n))
    offsum = [0]*n
    diagonal = []
    nonedges = 0
    factor = R*R//Q
    for i in range(n):
        diagonal.append(K[i][i]*factor+gamma-sum(x*x for x in L[i]))
        for j in range(i):
            assert K[i][j] == K[j][i]
            u, v = abs(i//side-j//side), abs(i%side-j%side)
            if not edge(N, u, v):
                assert K[i][j] <= -Q
                nonedges += 1
            # Direct integer Gram calculation; no numpy or proposed eigenvalues.
            g = sum(L[i][k]*L[j][k] for k in range(j+1))
            error = abs(K[i][j]*factor-g)
            offsum[i] += error
            offsum[j] += error
    assert all(di >= off for di, off in zip(diagonal, offsum))
    bound = 1+F(max(K[i][i] for i in range(n)), Q)+F(gamma, R*R)
    assert bound == F(d["alpha_upper_fraction"])
    upper = min(bound.__floor__(), side*(N-1))
    assert upper == d["integer_upper"] and F(upper, N*N) == F(d["area_upper_fraction"])
    return {"M": M, "N": N, "certificate": path.name,
            "vertices": n, "nonedge_matrix_entries_checked": nonedges,
            "psd_residual_rows_checked": n, "integer_upper": upper,
            "area_upper_fraction": d["area_upper_fraction"],
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "all_passed": True}


def multiply_interval(x, y, denominator):
    products = [a*b for a in x for b in y]
    return min(products)//denominator, -((-max(products))//denominator)


def fft_vector(vector, table, rootQ):
    n = len(vector)
    stages = n.bit_length()-1
    order = [int(f"{i:0{stages}b}"[::-1], 2) for i in range(n)]
    out = [vector[i] for i in order]
    for stage in range(1, stages+1):
        width = 2**stage
        for base in range(0, n, width):
            for j in range(width//2):
                phase = j*n//width
                cosine = table[phase]
                sine = table[(n//4-phase)%n]
                ur, ui = out[base+j]
                vr, vi = out[base+j+width//2]
                rc = multiply_interval(vr, cosine, rootQ)
                iss = multiply_interval(vi, sine, rootQ)
                ic = multiply_interval(vi, cosine, rootQ)
                rs = multiply_interval(vr, sine, rootQ)
                tr = rc[0]+iss[0], rc[1]+iss[1]
                ti = ic[0]-rs[1], ic[1]-rs[0]
                out[base+j] = ((ur[0]+tr[0], ur[1]+tr[1]), (ui[0]+ti[0], ui[1]+ti[1]))
                out[base+j+width//2] = ((ur[0]-tr[1], ur[1]-tr[0]), (ui[0]-ti[1], ui[1]-ti[0]))
    return out


def audit_spectral(row, tables):
    path = HERE/row["certificate"]
    d = json.loads(path.read_text())
    M, N, P = d["M"], d["N"], d["P"]
    assert P >= 2*M*N and P & (P-1) == 0 and P % 4 == 0
    assert d["window_vertices"] == (M*N)**2 and d["padded_vertices"] == P*P
    W, Q = d["weight_denominator"], d["interval_fft_denominator"]
    assert W == 10**9 and Q == 2**32
    shells = d["shell_weights"]
    assert len({k for k, w in shells}) == len(shells)
    assert all(isinstance(k, int) and k > 0 and isinstance(w, int) for k, w in shells)
    cf = d["cosine_certificate"]
    if cf not in tables:
        cp = HERE/cf
        tables[cf] = (check_cosines(cp), hashlib.sha256(cp.read_bytes()).hexdigest())
    cosine = tables[cf][0]
    assert cosine["T"] == P
    A = []
    total = 0
    support = 0
    for i in range(P):
        u = min(i, P-i)
        rowA = []
        for j in range(P):
            v = min(j, P-j)
            lo = max(u-1, 0)**2+max(v-1, 0)**2
            hi = (u+1)**2+(v+1)**2
            val = sum(w for k, w in shells if lo <= (N*k)**2 <= hi)
            if val:
                assert edge(N, u, v)
                support += 1
            total += val
            rowA.append(((val*Q//W, -((-val*Q)//W)), (0, 0)))
        A.append(rowA)
    assert A[0][0] == ((0, 0), (0, 0))
    degree = F(total, W)
    assert degree > 0 and degree == F(d["weighted_degree_fraction"])
    transformed = [fft_vector(r, cosine["intervals"], cosine["denominator"]) for r in A]
    lower = None
    for j in range(P):
        col = fft_vector([transformed[i][j] for i in range(P)], cosine["intervals"], cosine["denominator"])
        for real, imag in col:
            assert imag[0] <= 0 <= imag[1]
            lower = real[0] if lower is None else min(lower, real[0])
    assert lower == d["least_eigenvalue_lower_numerator"] and lower < 0
    lam = F(lower, Q)
    bound = P*P*(-lam)/(degree-lam)
    assert bound == F(d["spectral_alpha_upper_fraction"])
    upper = min(bound.__floor__(), M*N*(N-1))
    assert upper == d["integer_upper"] and F(upper, N*N) == F(d["area_upper_fraction"])
    # For every original displacement the padded minimum representative is
    # identical, including its square-cell distance interval.
    assert all(min(u, P-u) == u for u in range(M*N))
    return {"M": M, "N": N, "P": P, "certificate": path.name,
            "weighted_support_displacements_checked": support,
            "character_eigenvalue_intervals_checked": P*P,
            "spectral_alpha_upper_fraction": str(bound), "integer_upper": upper,
            "area_upper_fraction": d["area_upper_fraction"],
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "all_passed": True}


def main():
    theta = json.loads((HERE/f"erdos953-theta-results-{STAMP}.json").read_text())["results"]
    spectral = json.loads((HERE/f"erdos953-graph-spectral-results-{STAMP}.json").read_text())["results"]
    report = {"full_matrix_theta_certificates": [], "spectral_certificates": []}
    tables = {}
    for row in theta:
        report["full_matrix_theta_certificates"].append(audit_theta(row))
        print(f"Exact PSD audit passed: M={row['M']}, N={row['N']}, upper={row['integer_upper']}", flush=True)
    for row in spectral:
        report["spectral_certificates"].append(audit_spectral(row, tables))
        print(f"Interval FFT audit passed: M={row['M']}, N={row['N']}, P={row['P']}", flush=True)
    report.update(all_passed=True, lean_formalized=False,
                  cosine_certificates=[{"file": f, "sha256": h, "all_passed": True} for f, (t, h) in sorted(tables.items())],
                  nonedge_matrix_entries_checked=sum(r["nonedge_matrix_entries_checked"] for r in report["full_matrix_theta_certificates"]),
                  psd_residual_rows_checked=sum(r["psd_residual_rows_checked"] for r in report["full_matrix_theta_certificates"]),
                  character_eigenvalue_intervals_checked=sum(r["character_eigenvalue_intervals_checked"] for r in report["spectral_certificates"]))
    (HERE/f"erdos953-graph-methods-independent-audit-{STAMP}.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if not isinstance(v, list)}), flush=True)


if __name__ == "__main__":
    main()
