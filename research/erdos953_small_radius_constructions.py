"""Explicit clipped-disk lobes and exact rational polygon certificates.

The decimal integrations are diagnostics. The generated polygon certificates
are checked independently by verify_953_small_radius_certificates.py using
integers only. Neither routine asserts the unrestricted optimum M(R).
"""

from fractions import Fraction
from pathlib import Path
import json
import math

import mpmath as mp
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

HERE = Path(__file__).resolve().parent
mp.mp.dps = 65


def optimal_cap(R, t):
    R, t = mp.mpf(R), mp.mpf(t)
    r = mp.mpf("0.5")
    if R <= t:
        return None, t, mp.mpf(0)
    if R * R - t * t <= r * r:
        area = 2 * (R * R * mp.acos(t / R) - t * mp.sqrt(R * R - t * t))
        return None, t, area
    c = (t + mp.sqrt(t * t + 3 * (R * R - r * r))) / 3
    delta = c - t
    q = 2 * c - t
    # Both lobes: symmetric central disk strip plus two outer-disk caps.
    area = 4 * (delta * mp.sqrt(r * r - delta * delta)
                + r * r * mp.asin(delta / r))
    area += 2 * (R * R * mp.acos(q / R) - q * mp.sqrt(R * R - q * q))
    return c, q, area


def certify_polygon(m: int, intervals: int = 256):
    R, t = m / 2, (m - 1) / 2
    # Rational quadratic knots resolve the square-root endpoint at x=R.
    xden = 2 * intervals**2
    xnums = [(m-1)*intervals**2 + 2*i*intervals - i*i for i in range(intervals+1)]
    xs = np.array(xnums, dtype=float) / xden
    rows, cols, values, rhs = [], [], [], []
    row = 0
    for i in range(intervals + 1):
        for j in range(i + 1, intervals + 1):
            rows.extend([row, row])
            cols.extend([i, j])
            values.extend([1, 1])
            rhs.append(math.sqrt(1 - (xs[i] - xs[j]) ** 2))
            row += 1
    matrix = coo_matrix((values, (rows, cols)), shape=(row, intervals + 1)).tocsr()
    upper = np.minimum(0.5, np.sqrt(np.maximum(0, R * R - xs * xs)))
    weights = np.zeros(intervals + 1)
    widths = np.diff(xs)
    weights[:-1] += widths
    weights[1:] += widths
    solved = linprog(-weights, A_ub=matrix, b_ub=np.array(rhs),
                     bounds=list(zip(np.zeros_like(upper), upper)), method="highs")
    if not solved.success:
        raise RuntimeError(solved.message)
    denominator = 10**10
    # Downward rounding and a fixed small margin remove solver tolerances.
    heights = [max(0, math.floor(float(v) * denominator) - 1000) for v in solved.x]
    data = {"m": m, "intervals": intervals, "height_denominator": denominator,
            "x_denominator": xden, "x_numerators": xnums,
            "height_numerators": heights,
            "construction": "two reflected open regions under the piecewise-linear profile"}
    filename = HERE / f"erdos953-small-radius-R{m}-over-2-certificate.json"
    filename.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    area = Fraction(2 * sum((xnums[i+1]-xnums[i]) * (heights[i]+heights[i+1])
                           for i in range(intervals)), xden * denominator)
    c, q, exact = optimal_cap(str(R), str(t))
    # A diagnostic comparison with the proved cap-family optimum.
    assert float(area) <= float(exact) + 1e-9
    return {"R": str(Fraction(m, 2)), "center": mp.nstr(c, 45),
            "area_closed_form_decimal": mp.nstr(exact, 45),
            "polygon_area_fraction": str(area),
            "polygon_area_decimal": f"{float(area):.12f}",
            "gap_to_cap_optimum": f"{float(exact) - float(area):.12g}",
            "certificate_file": filename.name}


def half_integer_diagnostics(m):
    R, t = mp.mpf(m) / 2, mp.mpf(m - 1) / 2
    c, q, area = optimal_cap(R, t)
    assert t < c < q < R
    assert abs(3 * c**2 - 2 * t * c - (R**2 - mp.mpf("0.25"))) < mp.mpf("1e-60")
    assert abs((q - c)**2 + (R**2 - q**2) - mp.mpf("0.25")) < mp.mpf("1e-60")
    integral = 4 * mp.quad(lambda x: mp.sqrt(mp.mpf("0.25") - (x - c)**2), [t, q])
    integral += 4 * mp.quad(lambda x: mp.sqrt(max(mp.mpf(0), R**2 - x**2)), [q, R])
    assert abs(area - integral) < mp.mpf("1e-55")


def lower_envelope(value):
    R = mp.mpf(value)
    if R <= mp.mpf("0.5"):
        return mp.pi * R * R
    candidates = [mp.pi / 4]
    m = int(mp.ceil(2 * R))
    for old_m in range(2, m):
        candidates.append(optimal_cap(mp.mpf(old_m) / 2, mp.mpf(old_m - 1) / 2)[2])
    candidates.append(optimal_cap(R, mp.mpf(m - 1) / 2)[2])
    return max(candidates)


def plot_constructions():
    plt.rcParams.update({"font.size": 11, "axes.spines.top": False,
                         "axes.spines.right": False, "svg.fonttype": "none"})
    fig, axes = plt.subplots(1, 3, figsize=(12, 4.4), constrained_layout=True)
    for ax, m in zip(axes, [2, 3, 4]):
        R, t = m / 2, (m - 1) / 2
        c_mp, q_mp, area = optimal_cap(str(R), str(t))
        c, q = float(c_mp), float(q_mp)
        xs = np.linspace(t, R, 1500)
        heights = np.sqrt(np.maximum(0, np.minimum(R*R - xs*xs, 0.25 - (xs-c)**2)))
        ax.add_patch(Circle((0, 0), R, edgecolor="#526173", facecolor="#f1f4f8", lw=1.4))
        ax.fill_between(xs, -heights, heights, color="#147baf", alpha=.88)
        ax.fill_between(-xs, -heights, heights, color="#159b77", alpha=.88)
        for sign in [-1, 1]:
            ax.plot([sign*t, sign*t], [-R, R], ls="--", color="#8591a1", lw=.8)
            ax.plot(sign*c, 0, marker="o", ms=3, color="#172536")
        ax.set_title(f"R = {R:g}\nconstructed area = {float(area):.9f}")
        ax.set_aspect("equal")
        ax.set_xlim(-1.12*R, 1.12*R)
        ax.set_ylim(-1.12*R, 1.12*R)
        ax.set_xlabel("x")
        ax.set_ylabel("y")
        ax.text(0, -.79*R, f"cross distances: ({m-1}, {m})", ha="center", fontsize=10)
    fig.suptitle("Explicit open sets avoiding all positive integer distances", fontsize=14)
    fig.savefig(HERE / "erdos953-small-radius-lobes-2026-10-03.png", dpi=190)
    fig.savefig(HERE / "erdos953-small-radius-lobes-2026-10-03.svg")
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(8.2, 4.6), constrained_layout=True)
    radii = np.linspace(0, 2, 601)
    lower = [float(lower_envelope(str(v))) for v in radii]
    ax.plot(radii, lower, color="#147baf", lw=2.2, label="explicit construction lower bound")
    ax.plot(radii, [math.pi*min(v, .5)**2 for v in radii], color="#7e8793", ls="--",
            label="central disk construction")
    ax.axvspan(0, .5, color="#d9f0e7", alpha=.6, label="exact M(R) already proved")
    ax.set(xlabel="R", ylabel="area", xlim=(0, 2), ylim=(0, 1.02),
           title="Constructive lower bounds for 0 ≤ R ≤ 2")
    ax.legend(loc="lower right", fontsize=9)
    ax.grid(alpha=.18)
    fig.savefig(HERE / "erdos953-small-radius-area-envelope-2026-10-03.png", dpi=190)
    fig.savefig(HERE / "erdos953-small-radius-area-envelope-2026-10-03.svg")
    plt.close(fig)


def main():
    for m in [2, 3, 4]:
        half_integer_diagnostics(m)
    certificates = [certify_polygon(m) for m in [2, 3, 4]]
    values = ["0.25", "0.5", "0.75", "0.9", "1", "1.25", "1.5", "1.75", "2"]
    table = [{"R": r, "constructive_lower_bound": mp.nstr(lower_envelope(r), 40),
              "unrestricted_M_exact": mp.mpf(r) <= mp.mpf("0.5")} for r in values]
    output = {"closed_form_and_integral_checks": "passed", "cap_optimum_is_restricted": True,
              "baseline_pi_over_4": mp.nstr(mp.pi/4, 45),
              "half_integer_constructions": certificates, "continuous_range_samples": table}
    (HERE / "erdos953-small-radius-results-2026-10-03.json").write_text(
        json.dumps(output, indent=2) + "\n", encoding="utf-8")
    plot_constructions()
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
