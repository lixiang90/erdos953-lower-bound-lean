"""Pure integer verification of all polygon vertices and vertex pairs.

Concavity/Jensen interpolation extends these inequalities to every point
between the knots, as proved in the companion research note. No scipy,
floating-point coordinates, or sampled distance tests are used here.
"""
from fractions import Fraction
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def verify(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    m, n, den = data["m"], data["intervals"], data["height_denominator"]
    heights = data["height_numerators"]
    assert m >= 2 and n > 0 and den > 0 and len(heights) == n + 1
    xden, xnums = data["x_denominator"], data["x_numerators"]
    assert isinstance(xden, int) and xden > 0 and len(xnums) == n+1
    assert 2*xnums[0] == (m-1)*xden and 2*xnums[-1] == m*xden
    assert all(isinstance(x, int) for x in xnums)
    assert all(xnums[i] < xnums[i+1] for i in range(n))
    for i, hi in enumerate(heights):
        assert isinstance(hi, int) and hi >= 0
        xnum = xnums[i]
        assert 4 * (hi*hi*xden*xden + xnum*xnum*den*den) <= m*m*xden*xden*den*den
        for j, hj in enumerate(heights):
            assert (hi+hj)**2*xden*xden + (xnums[i]-xnums[j])**2*den*den <= den*den*xden*xden
    area = Fraction(2 * sum((xnums[i+1]-xnums[i]) * (heights[i]+heights[i+1])
                           for i in range(n)), xden * den)
    # Strict rational lower bounds, independently chosen below the formula values.
    thresholds = {2: Fraction(895, 1000), 3: Fraction(9176, 10000), 4: Fraction(928, 1000)}
    assert area > thresholds[m], (area, thresholds[m])
    return {"R": str(Fraction(m, 2)), "area": str(area),
            "ordered_vertex_pairs_checked": (n+1)**2,
            "strictly_above": str(thresholds[m])}


if __name__ == "__main__":
    results = [verify(HERE / f"erdos953-small-radius-R{m}-over-2-certificate.json")
               for m in [2, 3, 4]]
    print(json.dumps({"status": "all exact integer checks passed", "results": results}, indent=2))
