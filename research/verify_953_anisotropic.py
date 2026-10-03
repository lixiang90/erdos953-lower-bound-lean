"""Exact diagnostic checks for the 2026-10-03 thin-rectangle construction.

This finite computation is not the proof for arbitrary base, length, or radius.
Every comparison below uses integers, including the worst-corner square tests.
Run: python research/verify_953_anisotropic.py
"""

from itertools import product
import json


def check_differences(k: int, n: int) -> dict:
    den = 256 * k**3  # epsilon = 1 / den
    xp = [k**j for j in range(n)]
    yp = [8 * k * k ** (2 * j) for j in range(n)]
    checked = 0
    for digits in product(range(-(k - 2), k - 1), repeat=n):
        if not any(digits):
            continue
        b = abs(sum(d * p for d, p in zip(digits, xp)))
        a = abs(sum(d * p for d, p in zip(digits, yp)))
        assert b >= 1 and a >= 1
        assert b * b <= a <= 16 * k**3 * b * b
        # (a-eps)^2 + (3b/4)^2 > (a+eps)^2.
        lower_margin = 9 * b * b * den - 64 * a
        assert lower_margin > 0
        # (a+eps)^2 + (5b/4)^2 < (a+1-eps)^2.
        upper_margin = 16 * (2 * a + 1) * (den - 2) - 25 * b * b * den
        assert upper_margin > 0
        checked += 1
    # Maximum center coordinates and the sharper radius enclosure.
    xmax = (k - 2) * sum(xp)
    ymax = (k - 2) * sum(yp)
    assert xmax < k**n
    assert ymax < 8 * k ** (2 * n)
    assert xmax + ymax + 1 < 10 * k ** (2 * n)
    return {"k": k, "n": n, "nonzero_difference_vectors": checked}


def integer_root(value: int, degree: int) -> int:
    lo, hi = 0, 1
    while hi**degree <= value:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**degree <= value:
            lo = mid
        else:
            hi = mid
    return lo


def check_radius(R: int) -> dict:
    assert R >= 2560
    n = 2
    while 10 * (2 * (n + 1)) ** (2 * (n + 1)) <= R:
        n += 1
    k = integer_root(R // 10, 2 * n)
    count = (k - 1) ** n
    assert 2 * n <= k <= 9 * n
    assert 10 * k ** (2 * n) <= R < 10 * (k + 1) ** (2 * n)
    assert 10 * (2 * n) ** (2 * n) <= R
    assert R < 10 * (2 * (n + 1)) ** (2 * (n + 1))
    # N > sqrt(R/10)/4, with no floating-point evaluation.
    assert 160 * count**2 > R
    # M >= N / (1024 k^3); the printed coefficient is normalized by sqrt R.
    return {
        "R": str(R),
        "n": n,
        "k": k,
        "area_numerator": str(count),
        "area_denominator": 1024 * k**3,
    }


def main() -> None:
    differences = [check_differences(k, n) for k, n in
                   [(3, 8), (4, 6), (8, 5), (16, 3), (64, 2)]]
    # Include exact jump points and their immediate predecessors.
    radii = {2560, 10000}
    for n in range(2, 51):
        boundary = 10 * (2 * n) ** (2 * n)
        radii.add(boundary)
        if boundary > 2560:
            radii.add(boundary - 1)
    radii.update(10**power for power in [6, 12, 30, 100, 1000])
    parameters = [check_radius(R) for R in sorted(radii)]
    print(json.dumps({
        "status": "all exact checks passed",
        "difference_cases": differences,
        "difference_vectors_checked": sum(r["nonzero_difference_vectors"] for r in differences),
        "radius_cases_checked": len(parameters),
        "sample_parameters": [check_radius(10**p) for p in [6, 12, 30, 100]],
    }, indent=2))


if __name__ == "__main__":
    main()
