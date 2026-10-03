"""Independent exact verification of all required finite constant certificates.

This does not import the construction or its atanh logarithm evaluator.
It encloses logs using sum((1-1/x)^j/j) with a geometric tail instead.
All comparisons use arbitrary-precision integers and Fraction.
"""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
P = 144
GRID = 10**18


def outward(lo, hi):
    # Keep nested logs tractable without sacrificing an enclosure.
    low = Fraction(lo.numerator * GRID // lo.denominator, GRID)
    high = Fraction(-((-hi.numerator * GRID) // hi.denominator), GRID)
    return low, high


@lru_cache(maxsize=None)
def local_log(x):
    assert 1 <= x <= 2
    t = 1 - 1 / x
    power = t
    partial = Fraction(0)
    for j in range(1, P + 1):
        partial += power / j
        power *= t
    tail = power / ((P + 1) * (1 - t))
    return partial, partial + tail


@lru_cache(maxsize=None)
def log_interval(x):
    x = Fraction(x)
    assert x > 0
    shift = 0
    while x > 2:
        x /= 2
        shift += 1
    while x < 1:
        x *= 2
        shift -= 1
    l2, u2 = local_log(Fraction(2))
    lo, hi = local_log(x)
    if shift >= 0:
        return outward(lo + shift * l2, hi + shift * u2)
    return outward(lo + shift * u2, hi + shift * l2)


def check_q_upper(radius, saved):
    low_t, high_t = log_interval(Fraction(radius))
    assert low_t > 1
    independent_upper = log_interval(high_t)[1] / low_t
    assert independent_upper < saved


def main():
    data = json.loads((HERE / "erdos953-explicit-constants-audit-2026-10-03.json").read_text(encoding="utf-8"))
    assert data["constants"]["finite_C"] == "1/(32768*sqrt(10))"
    assert data["constants"]["one_unbounded_set_C"] == "1/524288"
    seen = set()
    for row in data["finite_initial_parameter_interval_audit"]:
        n, k = row["n"], row["k"]
        h = (2 * (n + 1))**(2 * (n + 1))
        c = min((k + 1)**(2 * n), h)
        assert k >= 2 * n and k**(2 * n) < h
        assert row["radius_interval_closed_left_open_right"] == [str(10 * k**(2 * n)), str(10 * c)]
        q = Fraction(row["loglogR_over_logR_upper_fraction"])
        check_q_upper(10 * c, q)
        left, right = Fraction(1024 * (k - 1)**(2 * n)), c * k**6 * q**6
        assert left > right
        assert left / right == Fraction(row["squared_margin_factor_lower_fraction"])
        assert (n, k) not in seen
        seen.add((n, k))
    expected = set()
    for n in range(2, 6):
        h = (2 * (n + 1))**(2 * (n + 1))
        k = 2 * n
        while k**(2 * n) < h:
            expected.add((n, k))
            k += 1
    assert seen == expected and len(seen) == 41

    seen_n = set()
    for row in data["finite_log_lemma_audit"]:
        n, k = row["n"], row["maximum_possible_k"]
        h = (2 * (n + 1))**(2 * (n + 1))
        assert k**(2 * n) < h <= (k + 1)**(2 * n)
        tl, tu = map(Fraction, row["T_interval"])
        l10, u10 = log_interval(Fraction(10))
        lk, uk = log_interval(Fraction(k))
        assert tl < l10 + 2 * n * lk
        assert u10 + 2 * n * uk < tu
        log_t_upper = Fraction(row["log_T_upper_fraction"])
        assert log_interval(tu)[1] < log_t_upper
        assert k * log_t_upper < 2 * tl
        assert k * log_t_upper / tl == Fraction(row["k_logT_over_T_upper_fraction"])
        assert n not in seen_n
        seen_n.add(n)
    assert seen_n == set(range(6, 16))
    assert 34 * 4**16 < 5**16
    assert Fraction(18, 17) < Fraction(5, 4)
    assert Fraction(5, 2) * 17 <= Fraction(8, 3) * 16

    seen_j = set()
    for row in data["initial_unbounded_block_interval_audit"]:
        j, k, n = row["j"], row["k"], row["n"]
        capacity = Fraction(4**j, 16)
        assert (2 * n)**(2 * n) <= capacity < (2 * (n + 1))**(2 * (n + 1))
        assert k**(2 * n) <= capacity < (k + 1)**(2 * n)
        assert n < 6
        area = Fraction((k - 1)**n, 1024 * k**3)
        assert area == Fraction(row["block_area"])
        r = 4**(j + 2)
        assert row["radius_interval_closed_left_open_right"] == [str(4**(j + 1)), str(r)]
        q = Fraction(row["loglogR_over_logR_upper_fraction"])
        check_q_upper(r, q)
        right = 2**(j + 2) * q**3
        assert area * 524288 > right
        assert area * 524288 / right == Fraction(row["margin_factor_lower_fraction"])
        assert j not in seen_j
        seen_j.add(j)
    assert seen_j == set(range(6, 24))
    assert 4**23 < 16 * 12**12 <= 4**24
    assert Fraction(128, 524288) < Fraction(1, 2048)
    assert Fraction(64, 32768) < Fraction(3, 4)

    result = {"status": "all independent exact rational checks passed",
              "log_method": "144-term positive log series with explicit geometric remainder; independent of atanh evaluator",
              "finite_digit_radius_intervals": len(seen),
              "log_lemma_parameter_extrema": len(seen_n),
              "early_unbounded_radius_intervals": len(seen_j),
              "coverage_and_large_n_induction_base_passed": True,
              "full_Lean_formalization": False}
    (HERE / "erdos953-explicit-constants-independent-audit-2026-10-03.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
