"""Exact audits for explicit constants in the Erdos 953 lower bounds.

All mathematical checks use integers and Fraction. Logarithms are enclosed
by a rational atanh series with an explicit remainder, after normalization.
Decimals in the output are for presentation only. The accompanying text
gives the arguments for arbitrary real radii and all remaining parameters.
"""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json
import math

HERE = Path(__file__).resolve().parent
Q = 10**12
TERMS = 32


def integer_root(a: int, p: int) -> int:
    assert a >= 0 and p >= 1
    lo, hi = 0, 1 << ((a.bit_length() + p - 1) // p)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**p <= a:
            lo = mid
        else:
            hi = mid
    return hi if hi**p <= a else lo


def floor_q(x: Fraction) -> Fraction:
    return Fraction(x.numerator * Q // x.denominator, Q)


def ceil_q(x: Fraction) -> Fraction:
    return -floor_q(-x)


@lru_cache(maxsize=None)
def normalized_log_bounds(x: Fraction) -> tuple[Fraction, Fraction]:
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    power = z
    partial = Fraction(0)
    for i in range(TERMS):
        partial += power / (2 * i + 1)
        power *= z * z
    remainder = 2 * power / ((2 * TERMS + 1) * (1 - z * z))
    return 2 * partial, 2 * partial + remainder


def log_bounds(x: Fraction | int) -> tuple[Fraction, Fraction]:
    x = Fraction(x)
    assert x > 0
    m = x.numerator.bit_length() - x.denominator.bit_length()
    scale = Fraction(2**m) if m >= 0 else Fraction(1, 2**(-m))
    y = x / scale
    while y < 1:
        y *= 2
        m -= 1
    while y >= 2:
        y /= 2
        m += 1
    l2, u2 = normalized_log_bounds(Fraction(2))
    yl = normalized_log_bounds(floor_q(y))[0]
    yu = normalized_log_bounds(ceil_q(y))[1]
    if m >= 0:
        low, high = m * l2 + yl, m * u2 + yu
    else:
        low, high = m * u2 + yl, m * l2 + yu
    return floor_q(low), ceil_q(high)


def log_ratio_bounds(r: Fraction | int) -> tuple[Fraction, Fraction]:
    """Enclose log(log(r))/log(r); callers have r >= 2560."""
    tl, tu = log_bounds(r)
    assert tl > 1
    zl = log_bounds(tl)[0]
    zu = log_bounds(tu)[1]
    return zl / tu, zu / tl


def parameters(r: Fraction | int) -> tuple[int, int]:
    r = Fraction(r)
    assert r >= 2560
    n = 2
    while 10 * (2 * (n + 1))**(2 * (n + 1)) <= r:
        n += 1
    k = integer_root(r.numerator // (10 * r.denominator), 2 * n)
    assert 2 * n <= k
    assert 10 * k**(2 * n) <= r < 10 * (k + 1)**(2 * n)
    assert r < 10 * (2 * (n + 1))**(2 * (n + 1))
    return k, n


def block_parameters(j: int) -> tuple[int, int]:
    # The existing unbounded set has capacity 4^j/16.
    return parameters(Fraction(10 * 4**j, 16))


def decimal(x: Fraction, digits: int = 24) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def audit_log_lemma() -> list[dict]:
    """For n=6,...,15, certify k log(T)/T < 2 at its worst k.

For all n>=16, the text proves this by induction and calculus.
"""
    result = []
    for n in range(6, 16):
        h = (2 * (n + 1))**(2 * (n + 1))
        k = integer_root(h - 1, 2 * n)
        l10, u10 = log_bounds(10)
        lk, uk = log_bounds(k)
        tl, tu = l10 + 2 * n * lk, u10 + 2 * n * uk
        log_t_upper = log_bounds(tu)[1]
        assert k * log_t_upper < 2 * tl
        result.append({"n": n, "maximum_possible_k": k,
                       "T_interval": [str(tl), str(tu)],
                       "log_T_upper_fraction": str(log_t_upper),
                       "k_logT_over_T_upper_fraction": str(k * log_t_upper / tl),
                       "k_logT_over_T_upper": decimal(k * log_t_upper / tl),
                       "strict_integer_rational_comparison_passed": True})
    assert 34 * 4**16 < 5**16  # Base of the n>=16 induction.
    return result


def audit_small_digit_cases() -> list[dict]:
    """Entire real-radius intervals for n=2,...,5.

Phi(R)=sqrt(R)*(loglog(R)/log(R))^3 increases for log(R)>=6.
Checking the interval's right endpoint bounds every radius within it.
"""
    result = []
    for n in range(2, 6):
        h = (2 * (n + 1))**(2 * (n + 1))
        kmax = integer_root(h - 1, 2 * n)
        for k in range(2 * n, kmax + 1):
            c = min((k + 1)**(2 * n), h)
            ru = 10 * c
            _, qhi = log_ratio_bounds(ru)
            # area > sqrt(ru/10)*q(ru)^3/32768, squared exactly.
            left = Fraction(1024 * (k - 1)**(2 * n))
            right = c * k**6 * qhi**6
            assert left > right
            result.append({"n": n, "k": k,
                           "radius_interval_closed_left_open_right":
                               [str(10 * k**(2 * n)), str(ru)],
                           "loglogR_over_logR_upper_fraction": str(qhi),
                           "squared_margin_factor_lower_fraction": str(left / right),
                           "squared_margin_factor_lower": decimal(left / right),
                           "strict_integer_rational_comparison_passed": True})
    return result


def audit_early_global_blocks() -> list[dict]:
    result = []
    j = 6
    while True:
        k, n = block_parameters(j)
        if n >= 6:
            assert j == 24
            break
        area = Fraction((k - 1)**n, 1024 * k**3)
        upper_radius = 4**(j + 2)
        _, qhi = log_ratio_bounds(upper_radius)
        right = 2**(j + 2) * qhi**3
        assert area * 524288 > right
        result.append({"j": j, "k": k, "n": n,
                       "block_area": str(area),
                       "radius_interval_closed_left_open_right":
                           [str(4**(j + 1)), str(upper_radius)],
                       "loglogR_over_logR_upper_fraction": str(qhi),
                       "margin_factor_lower_fraction": str(area * 524288 / right),
                       "margin_factor_lower": decimal(area * 524288 / right),
                       "strict_integer_rational_comparison_passed": True})
        j += 1
    return result


def lower_bound_interval(r: Fraction | int) -> tuple[Fraction, Fraction]:
    """Rigorous rational bounds for the displayed finite-set lower bound."""
    r = Fraction(r)
    ql, qu = log_ratio_bounds(r)
    scale = 10**24
    radicand = r / 10
    a = math.isqrt(radicand.numerator * scale**2 // radicand.denominator)
    sl, su = Fraction(a, scale), Fraction(a + 1, scale)
    return sl * ql**3 / 32768, su * qu**3 / 32768


def audit_radius_jumps() -> dict:
    points = set()
    for n in range(2, 41):
        h = (2 * (n + 1))**(2 * (n + 1))
        kmax = integer_root(h - 1, 2 * n)
        for k in range(2 * n, kmax + 1):
            r = Fraction(10 * k**(2 * n))
            points.update((r, r + Fraction(1, 10)))
            if r - Fraction(1, 10) >= 2560:
                points.add(r - Fraction(1, 10))
        end = Fraction(10 * h)
        points.update((end - Fraction(1, 10), end))
    points.update(Fraction(10**p) for p in (4, 6, 8, 12, 18, 24, 50, 100, 1000))
    for r in sorted(points):
        k, n = parameters(r)
        area = Fraction((k - 1)**n, 1024 * k**3)
        _, theory_upper = lower_bound_interval(r)
        assert area > theory_upper
    return {"rational_radii_checked": len(points),
            "includes": "parameter jumps, +/- 1/10, and radii up to 10^1000",
            "all_passed": True,
            "role": "supplementary diagnostics; not the arbitrary-radius proof"}


def main() -> None:
    finite = audit_small_digit_cases()
    logs = audit_log_lemma()
    blocks = audit_early_global_blocks()
    jumps = audit_radius_jumps()
    with localcontext() as ctx:
        ctx.prec = 36
        cm = str(1 / (Decimal(32768) * Decimal(10).sqrt()))
        cinf = str(Decimal(1) / Decimal(524288))
    samples = []
    for p in (4, 8, 12, 18, 24, 50, 100):
        r = 10**p
        k, n = parameters(r)
        low, high = lower_bound_interval(r)
        area = Fraction((k - 1)**n, 1024 * k**3)
        samples.append({"R": f"10^{p}", "k": k, "n": n,
                        "explicit_uniform_bound_rational_lower": str(low),
                        "explicit_uniform_bound_rational_upper": str(high),
                        "explicit_uniform_bound_decimal": decimal(low),
                        "actual_digit_construction_area_fraction": str(area),
                        "actual_digit_construction_area_decimal": decimal(area)})
    small = [
        ("1", "586555002834469/655360000000000", "rational two-lobe polygon"),
        ("3/2", "20385620360334689/20000000000000000", "verified random polygon"),
        ("2", "295605/262144", "1985 closed rational rectangles"),
        ("4", "1203/1024", "verified closed square union"),
        ("8", "153/128", "verified closed square union"),
    ]
    output = {
        "date": "2026-10-03",
        "status": "paper proof plus exact rational audits; full Lean theorem pending",
        "constants": {
            "finite_C": "1/(32768*sqrt(10))", "finite_C_decimal": cm,
            "one_unbounded_set_C": "1/524288", "one_unbounded_set_C_decimal": cinf,
            "logarithms": "natural",
            "finite_constructive_parameter_threshold": "2560",
            "unbounded_complete_block_threshold": "16384",
            "extension_with_small_radius_constructions": "both log-factor bounds hold for every R>=e",
        },
        "finite_initial_parameter_interval_audit": finite,
        "finite_log_lemma_audit": logs,
        "initial_unbounded_block_interval_audit": blocks,
        "large_n_induction_base": {"n": 16, "integer_inequality": "34*4^16 < 5^16", "passed": True},
        "supplementary_radius_jumps": jumps,
        "large_radius_examples": samples,
        "small_radius_exact_steps": [
            {"threshold_R": r, "area": a, "area_decimal": decimal(Fraction(a)),
             "source": source, "validity": "every real R at or above this threshold"}
            for r, a, source in small
        ],
    }
    target = HERE / "erdos953-explicit-constants-audit-2026-10-03.json"
    target.write_text(json.dumps(output, indent=2), encoding="utf-8")
    print(json.dumps({"constants": output["constants"],
                      "finite_initial_interval_count": len(finite),
                      "log_lemma_count": len(logs),
                      "early_block_interval_count": len(blocks),
                      "minimum_initial_squared_margin": min(float(Fraction(x["squared_margin_factor_lower"])) for x in finite),
                      "supplementary_radius_jumps": jumps,
                      "large_radius_examples": [
                          {k: x[k] for k in ("R", "k", "n", "explicit_uniform_bound_decimal", "actual_digit_construction_area_decimal")}
                          for x in samples],
                      "saved": str(target)}, indent=2))


if __name__ == "__main__":
    main()
