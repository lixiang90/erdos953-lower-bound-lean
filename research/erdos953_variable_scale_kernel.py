"""Numerical diagnostics for the analytically justified variable-scale Gram kernel.

This script is not a rigorous certificate of the infinite kernel inequalities.
Those estimates are proved in the accompanying research note with absolute
constants. Tests here check formulas and detect numerical counterexamples only.
"""
from pathlib import Path
import json
import math
import numpy as np
from scipy.special import j0
from threadpoolctl import threadpool_limits

HERE = Path(__file__).resolve().parent


def direct(t, s, v):
    k = np.arange(1, math.ceil(50/s)+1, dtype=float)
    return float(np.sum(k*(1+2*s*k+v*k*k)*np.exp(-s*k)*j0(2*np.pi*k*t)))


def poisson(t, s, v, terms=4000):
    m = np.arange(terms+1, dtype=float)
    lam = s+2j*np.pi*m
    q = lam*lam+(2*np.pi*t)**2
    base = lam*q**(-1.5)+2*s*(-q**(-1.5)+3*lam*lam*q**(-2.5))
    cubic = v*(-9*lam*q**(-2.5)+15*lam**3*q**(-3.5))
    real = (base+cubic).real
    return float(real[0]+2*real[1:].sum()), float(real.max())


def run():
    samples = []
    for s in (.001, .004, .01):
        for relative_v in (0, .01, .25, 1):
            for t in (.3, .7, 1.3, 2.5, 10.3, 30.7):
                v = relative_v*s*s
                series = direct(t, s, v)
                ps, largest = poisson(t, s, v)
                tau = math.ceil(t)-t
                samples.append({"s": s, "v_over_s_squared": relative_v, "t": t,
                    "direct_series": series, "finite_poisson_sum": ps,
                    "finite_sum_difference": abs(series-ps),
                    "largest_tested_poisson_summand": largest,
                    "phase_scaled_negative_value": -series*math.sqrt(1+t)*tau**1.5})
    rng = np.random.default_rng(953793)
    positions = rng.uniform(0, 3, (24, 2))
    scales = np.exp(rng.uniform(math.log(.001), math.log(.02), 24))
    K = np.zeros((24, 24))
    for i in range(24):
        for j in range(i+1):
            s = (scales[i]+scales[j])/2
            K[i, j] = K[j, i] = direct(float(np.linalg.norm(positions[i]-positions[j])), s, scales[i]*scales[j])
    result = {"samples": samples, "all_sampled_off_diagonals_negative": all(r["direct_series"] < 0 for r in samples),
        "all_tested_poisson_summands_negative": all(r["largest_tested_poisson_summand"] < 0 for r in samples),
        "maximum_finite_poisson_series_difference": max(r["finite_sum_difference"] for r in samples),
        "minimum_sampled_phase_scaled_negative_value": min(r["phase_scaled_negative_value"] for r in samples),
        "random_variable_scale_gram_minimum_eigenvalue": float(np.linalg.eigvalsh(K)[0]),
        "diagonal_times_scale_squared_range": [float(np.min(np.diag(K)*scales**2)), float(np.max(np.diag(K)*scales**2))],
        "diagnostics_only": True, "numerical_data_prove_infinite_inequality": False,
        "new_asymptotic_order_proved": False, "lean_formalized": False}
    (HERE/"erdos953-variable-scale-kernel-diagnostics-2026-10-03.json").write_text(json.dumps(result, indent=2))
    print(json.dumps({k: v for k, v in result.items() if k != "samples"}), flush=True)


if __name__ == "__main__":
    with threadpool_limits(limits=1):
        run()
