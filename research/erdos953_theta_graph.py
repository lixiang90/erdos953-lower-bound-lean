"""Full-matrix theta-prime experiments with exact Gram/DD upper certificates.

ADMM proposes a dual matrix. The bound is certified separately by a rational
Gram matrix plus a diagonally dominant residual; solver convergence is not a
proof and optimal theta values are not claimed.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import time
import numpy as np
from erdos953_square_grid_upper import edge

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
MATRIX_Q = 10**8
GRAM_Q = 10**6


def graph(M, N):
    L = M*N
    vs = [(i, j) for i in range(L) for j in range(L)]
    return np.array([[a != b and edge(N, abs(x-u), abs(y-v))
                      for b, (u, v) in enumerate(vs)] for a, (x, y) in enumerate(vs)], dtype=bool)


def simplex(x):
    u = np.sort(x)[::-1]
    cs = np.cumsum(u)-1
    rho = np.flatnonzero(u-cs/np.arange(1, len(u)+1) > 0)[-1]
    return np.maximum(x-cs[rho]/(rho+1), 0)


def propose(adj, seconds=15):
    n = len(adj)
    Y = np.eye(n)/n
    U = np.zeros((n, n))
    J = np.ones((n, n))
    rho = float(n)
    nonedge = ~adj & ~np.eye(n, dtype=bool)
    start = time.perf_counter()
    diagnostics = {}
    for it in range(5000):
        Z = Y-U+J/rho
        X = np.maximum(Z, 0)
        X[adj] = 0
        np.fill_diagonal(X, simplex(np.diag(Z)))
        vals, vecs = np.linalg.eigh(X+U)
        nextY = (vecs*np.maximum(vals, 0))@vecs.T
        U += X-nextY
        residual = float(np.linalg.norm(X-nextY))
        change = float(np.linalg.norm(nextY-Y))
        Y = nextY
        if it % 100 == 0:
            K = -rho*U
            diagnostics = {"iterations": it+1, "primal_residual_diagnostic": residual,
                           "dual_change_diagnostic": change,
                           "primal_objective_diagnostic": float(X.sum()),
                           "dual_nonedge_violation_diagnostic": float(np.max(K[nonedge]+1)) if nonedge.any() else 0}
        if (residual < 1e-8 and rho*change < 1e-7) or time.perf_counter()-start > seconds:
            break
    return -rho*U, diagnostics


def certify(M, N):
    start = time.perf_counter()
    adj = graph(M, N)
    n = len(adj)
    K, diagnostics = propose(adj)
    K = (K+K.T)/2
    units = np.rint(K*MATRIX_Q).astype(np.int64)
    nonedge = ~adj & ~np.eye(n, dtype=bool)
    units[nonedge] = np.minimum(units[nonedge], -MATRIX_Q)
    A = units.astype(float)/MATRIX_Q
    shift = max(1e-5, -float(np.linalg.eigvalsh(A)[0])+1e-5)
    # Only proposes a Gram witness; exact residual dominance below decides.
    L = np.linalg.cholesky(A+shift*np.eye(n))
    lint = np.rint(L*GRAM_Q).astype(np.int64)
    assert n*int(np.max(np.abs(lint)))**2 < 2**62
    gram = lint@lint.T
    factor = GRAM_Q*GRAM_Q//MATRIX_Q
    residual = units*factor-gram
    diag = np.diag(residual).copy()
    offsum = np.sum(np.abs(residual), axis=1)-np.abs(diag)
    gamma = max(0, int(np.max(offsum-diag)))+1
    assert np.all(diag+gamma >= offsum)
    bound = 1+F(int(np.diag(units).max()), MATRIX_Q)+F(gamma, GRAM_Q*GRAM_Q)
    upper = min(bound.__floor__(), M*N*(N-1))
    cert = {"M": M, "N": N, "vertices": n, "kind": "full_matrix_theta_prime_dual",
            "matrix_denominator": MATRIX_Q, "matrix_units": units.tolist(),
            "gram_denominator": GRAM_Q, "gram_factor_units": lint.tolist(),
            "diagonal_shift_numerator": gamma, "diagonal_shift_denominator": GRAM_Q*GRAM_Q,
            "alpha_upper_fraction": str(bound), "integer_upper": upper,
            "area_upper_fraction": str(F(upper, N*N)),
            "psd_certificate": "rational Gram plus symmetric diagonally dominant nonnegative-diagonal residual",
            "finite_graph_only": True, "theta_optimality_claimed": False,
            "is_continuous_upper_at_this_N": False, "lean_formalized": False, **diagnostics}
    filename = f"erdos953-theta-M{M}-N{N}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert, separators=(",", ":")), encoding="utf-8")
    brief = {k: v for k, v in cert.items() if k not in ("matrix_units", "gram_factor_units")}
    brief.update(certificate=filename, seconds=time.perf_counter()-start)
    print(json.dumps(brief), flush=True)
    return brief


def main():
    rows = []
    for M, N in ((1, 4), (1, 8), (2, 4), (1, 12), (2, 8), (4, 4)):
        rows.append(certify(M, N))
        (HERE/f"erdos953-theta-results-{STAMP}.json").write_text(json.dumps({"results": rows}, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
