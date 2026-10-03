"""Several conservative rounds outside ALL integer annuli of A_infinity++.

Each addition is a union of whole rational rectangles, disjoint from previous
components. Every previous addition becomes a source for subsequent scans.
Future digital blocks are excluded by a uniform analytic phase enclosure.
Float arrays propose cells only; arbitrary-precision comparisons certify them.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import math
import time
import numpy as np
from erdos953_all_ring_hole_extension import load_sources
from erdos953_square_limit_construction import parameters, center

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def conflict(r, s, scale, band):
    l, h, b, t = r
    L, H, B, T = s
    dx, dy = max(L-h, l-H, 0), max(B-t, b-T, 0)
    farx, fary = max(abs(l-H), abs(h-L)), max(abs(b-T), abs(t-B))
    low, high = dx*dx+dy*dy, farx*farx+fary*fary
    m = math.isqrt(high)//scale
    return any(k >= 1 and low <= (k*scale+band)**2 and high >= (k*scale-band)**2 for k in (m, m+1))


def overlap(r, s):
    return min(r[1], s[1]) > max(r[0], s[0]) and min(r[3], s[3]) > max(r[2], s[2])


def tail_bounds(X, Y, offsets):
    xl, xr, yl, yr = offsets
    U = max(abs(xl), abs(xr))+F(1, 6)
    V = max(abs(yl), abs(yr))+F(1, 512)
    B, h = 2**14, F(1, 512)
    amin, bmin = 3*B*B-abs(Y), B-abs(X)
    assert bmin > U and amin > V
    ratio_upper = (F(7, 2)+F(abs(Y), B*B))/(1-F(abs(X), B))**2
    inverse_upper = (F(5, 4)+F(abs(X), B))**2/(3-F(abs(Y), B*B))
    u, v = U/bmin, V/amin
    low = (1-u)**2/ratio_upper/(2*(1+v)+inverse_upper*(1+u)**2/(2*amin*(1-v)))-h
    high = inverse_upper*(1+u)**2/(2*(1-v))+h
    return low, high


def merge_cells(mask, col0, row0):
    active, rectangles = {}, []
    for row, line in enumerate(mask, row0):
        changes = np.diff(np.r_[False, line, False].astype(np.int8))
        starts, ends = np.flatnonzero(changes == 1)+col0, np.flatnonzero(changes == -1)+col0
        nxt = {}
        for left, right in zip(starts, ends):
            key = (int(left), int(right))
            nxt[key] = (active[key][0], row+1) if key in active else (row, row+1)
        for key, span in active.items():
            if key not in nxt:
                rectangles.append((*key, *span))
        active = nxt
    rectangles.extend((*key, *span) for key, span in active.items())
    return rectangles


def propose(sources, X, Y, offsets, nx, ny, epsilon):
    xl, xr, yl, yr = offsets
    assert all((z*n).denominator == 1 for z, n in zip(offsets, (nx, nx, ny, ny)))
    col0, col1, row0, row1 = int(xl*nx), int(xr*nx), int(yl*ny), int(yr*ny)
    cols, rows = np.meshgrid(np.arange(col0, col1), np.arange(row0, row1))
    ul, ur, vl, vr = cols.ravel()/nx, (cols.ravel()+1)/nx, rows.ravel()/ny, (rows.ravel()+1)/ny
    safe = np.ones(len(ul), dtype=bool)
    low, high = tail_bounds(X, Y, offsets)
    safe &= float(low)-vr > float(epsilon)+1e-11
    safe &= float(high)-vl < 1-float(epsilon)-1e-11
    scale = math.lcm(nx, ny, epsilon.denominator, *(z.denominator for box in sources for z in box))
    band = int(epsilon*scale)
    ints = [tuple(int(z*scale) for z in box) for box in sources]
    window = (F(X)+xl, F(X)+xr, F(Y)+yl, F(Y)+yr)
    iwindow = tuple(int(z*scale) for z in window)
    relevant = [i for i, r in enumerate(ints) if conflict(iwindow, r, scale, band) or overlap(iwindow, r)]
    relevant.sort(key=lambda i: abs(float((sources[i][2]+sources[i][3])/2-Y)))
    filters = 0
    for i in relevant:
        ids = np.flatnonzero(safe)
        if not len(ids):
            break
        left, right, bottom, top = sources[i]
        l, r = float(left-X), float(right-X)
        sy = round((bottom+top)/2)
        sb, st = float(bottom-sy), float(top-sy)
        a = sy-Y
        # Reject any old interior overlap; areas must not be counted twice.
        over = (ur[ids] > l+1e-12) & (ul[ids] < r-1e-12)
        over &= (vr[ids] > float(bottom-Y)+1e-12) & (vl[ids] < float(top-Y)-1e-12)
        valid_ids = ids[~over]
        safe[ids[over]] = False
        if not len(valid_ids) or not conflict(iwindow, ints[i], scale, band):
            continue
        ids = valid_ids
        dx = np.maximum(np.maximum(l-ur[ids], ul[ids]-r), 0)
        farx = np.maximum(np.abs(ul[ids]-r), np.abs(ur[ids]-l))
        if bottom >= F(Y)+yr:
            base = a
            dlo, dhi = sb-vr[ids], st-vl[ids]
            ylo, yhi = base+dlo, base+dhi
            lo_phase = dlo+dx*dx/(np.sqrt(ylo*ylo+dx*dx)+ylo)
            hi_phase = dhi+farx*farx/(np.sqrt(yhi*yhi+farx*farx)+yhi)
            no_integer = np.floor(hi_phase+float(epsilon)+1e-11) < np.ceil(lo_phase-float(epsilon)-1e-11)
        elif top <= F(Y)+yl:
            base = -a
            dlo, dhi = vl[ids]-st, vr[ids]-sb
            ylo, yhi = base+dlo, base+dhi
            lo_phase = dlo+dx*dx/(np.sqrt(ylo*ylo+dx*dx)+ylo)
            hi_phase = dhi+farx*farx/(np.sqrt(yhi*yhi+farx*farx)+yhi)
            no_integer = np.floor(hi_phase+float(epsilon)+1e-11) < np.ceil(lo_phase-float(epsilon)-1e-11)
        else:
            dy = np.maximum(np.maximum(float(bottom-Y)-vr[ids], vl[ids]-float(top-Y)), 0)
            fary = np.maximum(np.abs(vl[ids]-float(top-Y)), np.abs(vr[ids]-float(bottom-Y)))
            distlo, disthi = np.sqrt(dx*dx+dy*dy), np.sqrt(farx*farx+fary*fary)
            first = np.maximum(1, np.ceil(distlo-float(epsilon)-1e-11))
            no_integer = first > disthi+float(epsilon)+1e-11
        safe[ids] &= no_integer
        filters += 1
    runs = merge_cells(safe.reshape(row1-row0, col1-col0), col0, row0)
    accepted, failures = [], 0
    for l, r, b, t in runs:
        box = (F(X)+F(l, nx), F(X)+F(r, nx), F(Y)+F(b, ny), F(Y)+F(t, ny))
        ibox = tuple(int(z*scale) for z in box)
        if any(conflict(ibox, ints[i], scale, band) or overlap(ibox, ints[i]) for i in relevant):
            failures += 1
            continue
        assert low-(box[3]-Y) > epsilon and high-(box[2]-Y) < 1-epsilon
        accepted.append(box)
    assert (xr-xl)**2+(yr-yl)**2 < (1-epsilon)**2
    return accepted, {"relevant_sources": len(relevant), "finite_sources": len(sources),
        "array_ring_filters": filters, "proposed_cells": int(safe.sum()),
        "compressed_candidates": len(runs), "exact_rejected_rectangles": failures,
        "tail_phase_bounds": [str(low), str(high)]}


def windows_for(j, full=False):
    k, n = parameters(j)
    if full:
        digits = list(product(range(k-1), repeat=n))
    else:
        digits = sorted({(0,)*n, ((k-2)//2,)*n, (k-2,)*n})
    return [(list(ds), center(j, ds)) for ds in digits]


def save(data, filename):
    (HERE/filename).write_text(json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8")


def run(rounds=2, later_scales=False):
    base, _ = load_sources()
    old_file = HERE/f"erdos953-Ainfty-all-ring-hole-extension-{STAMP}.json"
    old = json.loads(old_file.read_text())
    previous = [tuple(map(F, box)) for box in old["added_rectangles"]]
    sources = base+previous
    baseline_count = len(sources)
    selected_windows = [(6, ds, xy) for ds, xy in windows_for(6, full=True)]
    if later_scales:
        selected_windows += [(7, ds, xy) for ds, xy in windows_for(7, full=True)]
        for j in (8, 9, 10, 11, 12, 13):
            selected_windows += [(j, ds, xy) for ds, xy in windows_for(j)]
    payload = {"source_set": "A_infinity_plus_plus", "old_hole_certificate": old_file.name,
        "old_hole_certificate_sha256": hashlib.sha256(old_file.read_bytes()).hexdigest(),
        "finite_prefix_last": 13, "analytic_tail_first": 14,
        "baseline_source_rectangles_with_base_enclosure": baseline_count,
        "old_hole_area_fraction": old["area_fraction"], "groups": [], "rounds": [],
        "added_rectangles": [], "added_area_fraction": "0", "lean_formalized": False,
        "new_asymptotic_order_proved": False, "finite_optimum_proved": False,
        "same_fixed_unbounded_set_enlarged": True,
        "scope": "finite certified additions compatible with all future original tail blocks"}
    label = "multiscale" if later_scales else "first-block"
    filename = f"erdos953-iterated-ring-holes-{label}-{STAMP}.json"
    schedule = [("repeat-fixed", 320, 4096, F(1, 512), (F(-2, 5), F(2, 5), F(1, 256), F(1, 8)), selected_windows[:9])]
    for r in range(rounds):
        schedule.append((f"refine{r+1}", 160*2**r, 2048*2**r, F(1, 512*4**r),
                         (F(-2, 5), F(2, 5), F(-1, 8), F(1, 8)), selected_windows))
    total_area = F(0)
    for tag, nx, ny, epsilon, offsets, window_list in schedule:
        started = time.perf_counter()
        area, first, count_before = F(0), len(payload["added_rectangles"]), len(sources)
        for j, digits, (X, Y) in window_list:
            group_start = len(payload["added_rectangles"])
            accepted, diagnostics = propose(sources, X, Y, offsets, nx, ny, epsilon)
            group_area = sum(((b[1]-b[0])*(b[3]-b[2]) for b in accepted), F(0))
            group = {"round": tag, "j": j, "digits": digits, "center": [X, Y],
                "epsilon": str(epsilon), "grid_denominators": [nx, ny],
                "offset_window": [str(z) for z in offsets], "source_before_count": len(sources),
                "first_rectangle": group_start, "rectangle_count": len(accepted),
                "area_fraction": str(group_area), **diagnostics}
            payload["groups"].append(group)
            payload["added_rectangles"].extend([[str(z) for z in b] for b in accepted])
            sources.extend(accepted)
            area += group_area
            print(json.dumps({"round": tag, "j": j, "digits": digits, "rectangles": len(accepted),
                              "area": float(group_area), "relevant": diagnostics["relevant_sources"]}), flush=True)
        total_area += area
        result = {"round": tag, "epsilon": str(epsilon), "grid_denominators": [nx, ny],
            "windows": len(window_list), "area_fraction": str(area), "area": float(area),
            "cumulative_new_area_fraction": str(total_area), "first_rectangle": first,
            "new_rectangle_count": len(payload["added_rectangles"])-first,
            "source_count_before": count_before, "source_count_after": len(sources),
            "seconds": time.perf_counter()-started}
        payload["rounds"].append(result)
        payload["added_area_fraction"] = str(total_area)
        payload["old_and_new_hole_area_fraction"] = str(F(old["area_fraction"])+total_area)
        save(payload, filename)
        print(json.dumps(result), flush=True)
    return payload


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--rounds", type=int, default=2)
    p.add_argument("--later-scales", action="store_true")
    a = p.parse_args()
    run(a.rounds, a.later_scales)
