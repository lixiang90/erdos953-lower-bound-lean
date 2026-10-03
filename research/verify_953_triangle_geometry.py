"""Independent numerical cross-checks of whole-cell circle/triangle extrema."""

import json
import math
from pathlib import Path

import numpy as np
from shapely.geometry import Point, Polygon
from scipy.spatial.distance import cdist

from erdos953_triangle_partition_search import (
    make_partition, clip_triangle, vertex_bounds, minimum_squared,
    curved_maximum_squared,
)
from verify_953_triangle_partition import verify_certificate, expected_triangle


def main():
    R, n = 1.5, 12
    cells, data = make_partition(R, n)
    disk = Point(0, 0).buffer(R, quad_segs=4096)
    reference = [Polygon(cell["triangle"]).intersection(disk) for cell in cells]
    area_errors = [abs(shape.area-cell["area"]) for shape, cell in zip(reference, cells)]
    assert max(area_errors) < 2e-7
    rng = np.random.default_rng(953793)
    boundary = np.flatnonzero(data["na"])
    pairs = [tuple(rng.choice(len(cells), 2, replace=False)) for _ in range(300)]
    pairs += [tuple(rng.choice(boundary, 2, replace=False)) for _ in range(100)]
    min_errors, max_errors = [], []
    for i, j in pairs:
        lo, hi = vertex_bounds(i, j, data["vertices"], data["nv"])
        low = minimum_squared(i, j, data["vertices"], data["nv"], data["segments"], data["ns"], lo)
        high = curved_maximum_squared(i, j, data["vertices"], data["nv"], data["arcs"], data["na"], R, hi)
        reference_low = reference[i].distance(reference[j])**2
        av, bv = np.array(reference[i].exterior.coords), np.array(reference[j].exterior.coords)
        reference_high = float(np.max(cdist(av, bv, "sqeuclidean")))
        min_errors.append(abs(low-reference_low))
        max_errors.append(abs(high-reference_high))
        assert abs(low-reference_low) < 7e-7
        assert high >= reference_high-1e-8
        assert high-reference_high < 7e-7
    # All original triangle vertices are outside the disk, but an arc cap remains.
    cap = clip_triangle(np.array([[.95, -.4], [1.1, 0.], [.95, .4]]), 1.)
    assert cap is not None and len(cap["vertices"]) == 2 and len(cap["arcs"]) == 1
    expected_cap = math.acos(.95)-.95*math.sqrt(1-.95**2)
    assert abs(cap["area"]-expected_cap) < 1e-12
    # An arc can attain its maximum in its interior: a vertex-only test misses it.
    _, one = make_partition(1., 12)
    found_interior_arc_maximum = False
    for i in np.flatnonzero(one["na"]):
        for j in range(len(one["nv"])):
            lo, hi = vertex_bounds(i, j, one["vertices"], one["nv"])
            true_high = curved_maximum_squared(i, j, one["vertices"], one["nv"], one["arcs"], one["na"], 1., hi)
            if true_high > hi+1e-5:
                found_interior_arc_maximum = True
                break
        if found_interior_arc_maximum:
            break
    assert found_interior_arc_maximum
    # Adjacent partition pieces share an edge but have disjoint interiors.
    Q = 24_000_000
    ids = [[-1, -1, 0], [-1, -1, 1]]
    pieces = [{"grid_id": p, "triangle": expected_triangle(p, Q, 2, 2, 12),
               "polygon": expected_triangle(p, Q, 2, 2, 12)} for p in ids]
    certificate = {"coordinate_denominator": Q, "radius_numerator": 2,
                   "radius_denominator": 2, "grid_n": 12, "pieces": pieces}
    assert verify_certificate(certificate)["area_fraction"] == "1/144"
    certificate["pieces"] = pieces+[pieces[0]]
    try:
        verify_certificate(certificate)
    except AssertionError:
        pass
    else:
        raise AssertionError("duplicate cell was accepted")
    output = {"status": "all geometry and exact-checker sanity checks passed",
              "clipped_cells_area_checked": len(cells), "independent_cell_pairs_checked": len(pairs),
              "reference_circle_segments": 16384,
              "largest_cell_area_error_against_inscribed_reference": max(area_errors),
              "largest_squared_minimum_distance_error": max(min_errors),
              "largest_squared_maximum_distance_error": max(max_errors),
              "two_vertex_circular_cap": "passed", "interior_arc_maximum": "passed",
              "shared_edge_area_and_duplicate_rejection": "passed",
              "note": "Shapely is only an independent numerical diagnostic; area certificates use exact integers"}
    path = Path(__file__).parent/"erdos953-triangle-geometry-audit-2026-10-03.json"
    path.write_text(json.dumps(output, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
