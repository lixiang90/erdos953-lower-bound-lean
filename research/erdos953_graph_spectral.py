"""Padded Cayley graph + optimized signed integer-distance-shell ratio bounds.

Embedding uses P >= 2MN, so no two vertices in the original window acquire
wraparound edges. Signed weighted matrices are supported on genuine conflicts.
An integer interval FFT certifies the least eigenvalue, not floating FFT output.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import time
import numpy as np
from scipy.optimize import linprog
from erdos953_square_grid_upper import cosines, COS_Q

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
WEIGHT_Q = 10**9
VALUE_Q = 2**32


def multiply(lo, hi, a, b):
    # Bound before multiplication prevents unnoticed int64 overflow.
    assert int(max(np.max(np.abs(lo)), np.max(np.abs(hi))))*COS_Q < 2**62
    x, y, z, w = lo*a, lo*b, hi*a, hi*b
    low = np.minimum(np.minimum(x, y), np.minimum(z, w))
    high = np.maximum(np.maximum(x, y), np.maximum(z, w))
    return low//COS_Q, -((-high)//COS_Q)


def fft_axis(rl, rh, il, ih, table):
    P = rl.shape[1]
    stages = P.bit_length()-1
    order = np.array([int(f"{i:0{stages}b}"[::-1], 2) for i in range(P)])
    rl, rh, il, ih = [x[:, order].copy() for x in (rl, rh, il, ih)]
    for step in (2**k for k in range(1, stages+1)):
        shape = (P, P//step, step)
        aa, bb, cc, dd = [x.reshape(shape) for x in (rl, rh, il, ih)]
        half = step//2
        ur, Ur, ui, Ui = [x[..., :half].copy() for x in (aa, bb, cc, dd)]
        vr, Vr, vi, Vi = [x[..., half:].copy() for x in (aa, bb, cc, dd)]
        phase = np.arange(half)*(P//step)
        c, C = table[phase].T
        s, S = table[(P//4-phase)%P].T
        rc, Rc = multiply(vr, Vr, c, C)
        iss, Iss = multiply(vi, Vi, s, S)
        ic, Ic = multiply(vi, Vi, c, C)
        rs, Rs = multiply(vr, Vr, s, S)
        tr, Tr, ti, Ti = rc+iss, Rc+Iss, ic-Rs, Ic-rs
        aa[..., :half], bb[..., :half] = ur+tr, Ur+Tr
        cc[..., :half], dd[..., :half] = ui+ti, Ui+Ti
        aa[..., half:], bb[..., half:] = ur-Tr, Ur-tr
        cc[..., half:], dd[..., half:] = ui-Ti, Ui-ti
    return rl, rh, il, ih


def interval_spectrum(A, table):
    assert np.max(np.abs(A))*VALUE_Q < 2**62
    rl = (A*VALUE_Q)//WEIGHT_Q
    rh = -((-A*VALUE_Q)//WEIGHT_Q)
    zeros = np.zeros_like(A)
    out = fft_axis(rl, rh, zeros.copy(), zeros.copy(), table)
    out = fft_axis(*(x.T.copy() for x in out), table)
    assert np.all(out[2] <= 0) and np.all(out[3] >= 0)
    return int(out[0].min())


def solve(M, N):
    start = time.perf_counter()
    L = M*N
    P = 1 << (2*L-1).bit_length()
    pos = np.minimum(np.arange(P), P-np.arange(P))
    u, v = pos[:, None], pos[None, :]
    low = np.maximum(u-1, 0)**2+np.maximum(v-1, 0)**2
    high = (u+1)**2+(v+1)**2
    rings = []
    degrees = []
    eigen = []
    for k in range(1, math.isqrt(int(high.max()))//N+1):
        B = (low <= N*N*k*k)&(N*N*k*k <= high)
        assert not B[0, 0]
        if B.any():
            rings.append((k, B))
            degrees.append(int(B.sum()))
            E = np.fft.fft2(B).real
            eigen.append([E[a, b] for a in range(P//2+1) for b in range(a+1)])
    eigen = np.array(eigen).T
    # min q: each character eigenvalue >= -q, weighted degree equals 1.
    A_ub = np.column_stack((-eigen, -np.ones(len(eigen))))
    equality = np.array([degrees+[0]], dtype=float)
    obj = np.zeros(len(rings)+1)
    obj[-1] = 1
    optimum = linprog(obj, A_ub=A_ub, b_ub=np.zeros(len(eigen)),
                      A_eq=equality, b_eq=[1],
                      bounds=[(None, None)]*len(rings)+[(0, None)], method="highs")
    assert optimum.success, optimum.message
    units = np.rint(optimum.x[:-1]*WEIGHT_Q).astype(np.int64)
    A = sum((int(w)*B.astype(np.int64) for (k, B), w in zip(rings, units)), np.zeros((P, P), dtype=np.int64))
    d = F(sum(int(w)*degree for w, degree in zip(units, degrees)), WEIGHT_Q)
    assert d > 0
    table, cosfile = cosines(P)
    lamnum = interval_spectrum(A, table)
    lam = F(lamnum, VALUE_Q)
    assert lam < 0
    bound = P*P*(-lam)/(d-lam)
    upper = min(bound.__floor__(), L*(N-1))
    cert = {"M": M, "N": N, "P": P, "window_vertices": L*L, "padded_vertices": P*P,
            "kind": "signed_shell_weighted_ratio_bound", "weight_denominator": WEIGHT_Q,
            "shell_weights": [[k, int(w)] for (k, B), w in zip(rings, units)],
            "weighted_degree_fraction": str(d), "cosine_certificate": cosfile,
            "interval_fft_denominator": VALUE_Q, "least_eigenvalue_lower_numerator": lamnum,
            "spectral_alpha_upper_fraction": str(bound), "integer_upper": upper,
            "area_upper_fraction": str(F(upper, N*N)),
            "optimization_q_diagnostic": float(optimum.fun),
            "no_wraparound_edges_inside_original_window": True,
            "finite_grid_only": True, "is_continuous_upper_at_this_N": False,
            "lean_formalized": False}
    filename = f"erdos953-graph-spectral-M{M}-N{N}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert, separators=(",", ":")), encoding="utf-8")
    row = {**cert, "certificate": filename, "seconds": time.perf_counter()-start}
    print(json.dumps(row), flush=True)
    return row


def main():
    rows = []
    for M, N in ((1, 8), (2, 8), (4, 8), (8, 8), (16, 8), (1, 16), (2, 16), (4, 16), (8, 16)):
        rows.append(solve(M, N))
        (HERE/f"erdos953-graph-spectral-results-{STAMP}.json").write_text(json.dumps({"results": rows}, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
