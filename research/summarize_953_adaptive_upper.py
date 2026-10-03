from pathlib import Path
from fractions import Fraction as F
import json
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def main():
    audit_file = HERE/f"erdos953-adaptive-outer-independent-audit-{STAMP}.json"
    audit = json.loads(audit_file.read_text())
    assert audit["all_passed"]
    approved = {r["certificate"] for r in audit["results"] if r["all_passed"]}
    cases = []
    for manifest in sorted(HERE.glob(f"erdos953-adaptive-outer-results-M*-{STAMP}.json")):
        d = json.loads(manifest.read_text())
        assert all(r["certificate"] in approved for r in d["results"])
        rows = d["results"]
        first = min((r for r in rows if r["tag"].startswith("adaptive0-")), key=lambda r: F(r["alpha_upper_fraction"]))
        best = min(rows, key=lambda r: (r["robust_point_upper"], F(r["alpha_upper_fraction"])))
        delta, M = F(d["delta_fraction"]), d["M"]
        packing = math.floor(1+4*M*M/(F(314159, 100000)*delta*delta)+8*M/(F(314159, 100000)*delta))
        stages = []
        for tag in sorted({r["tag"].split("-")[0] for r in rows if r["tag"].startswith("adaptive")}):
            step_best = min((r for r in rows if r["tag"].startswith(tag+"-")), key=lambda r: F(r["alpha_upper_fraction"]))
            stages.append({"stage": tag, "vertices": step_best["vertices"],
                "graph_upper": step_best["robust_point_upper"],
                "effective_point_upper": min(packing, step_best["robust_point_upper"]),
                "certificate": step_best["certificate"]})
        cases.append({"M": M, "domain": f"[0,{M}]^2", "delta_fraction": str(delta),
            "initial_vertices": first["vertices"], "initial_graph_upper": first["robust_point_upper"],
            "independent_disk_packing_upper": packing,
            "initial_effective_point_upper": min(first["robust_point_upper"], packing),
            "best_vertices": best["vertices"], "best_robust_point_upper": best["robust_point_upper"],
            "best_delta_squared_point_upper_fraction": str(delta*delta*best["robust_point_upper"]),
            "best_certificate": best["certificate"], "partition_certificate": stages[-1]["certificate"],
            "adaptive_stages": stages,
            "uniform_control": [{"vertices": r["vertices"], "upper": r["robust_point_upper"],
                "upper_fraction": r["alpha_upper_fraction"], "tag": r["tag"]}
                for r in rows if r["tag"].startswith("uniform")]})
    result = {"cases": cases, "independently_audited_certificates": len(audit["results"]),
        "all_passed": True, "finite_delta_point_upper_proved": True,
        "continuous_area_upper_proved": False, "uniform_over_delta_proved": False,
        "new_asymptotic_order_proved": False, "optimizer_optimality_proved": False,
        "lean_formalized": False,
        "variable_scale_kernel": {"paper_derivation_complete": True, "peer_reviewed": False,
            "explicit_absolute_constants_computed": False, "recovers_existing_square_root_order": True,
            "minimum_cell_size_loss_removed": True, "weighted_phase_dichotomy_proved": False},
        "caveats": ["Some finite graph certificates are weaker than elementary disk packing; effective bounds include that baseline.",
            "The equal-node comparison gave 23 for both adaptive and uniform partitions; no demonstrated adaptive efficiency advantage.",
            "The tested deltas 1/4 and 1/8 exceed the 1/10 range of the usual continuous-area reduction.",
            "Spatial capacities constrain actual geometric point occupancies, not all independent sets of the outer graph."],
        "notes": f"erdos953-adaptive-upper-notes-{STAMP}.txt",
        "audit": audit_file.name,
        "figure": f"erdos953-adaptive-upper-{STAMP}.png"}
    outfile = HERE/f"erdos953-adaptive-outer-summary-{STAMP}.json"
    outfile.write_text(json.dumps(result, indent=2, ensure_ascii=False), encoding="utf-8")

    fig, axes = plt.subplots(2, 2, figsize=(11, 10), constrained_layout=True)
    for ax, case in zip(axes.ravel()[:3], cases):
        cert = json.loads((HERE/case["partition_certificate"]).read_text())
        D, M = cert["coordinate_denominator"], case["M"]
        base = F(case["delta_fraction"])/2
        for x, y, h in cert["leaves"]:
            level = round(math.log2(float(base/(F(h, D)))))
            color = ("#eef0f2", "#adc8e4", "#468ac5", "#1d4c82")[min(level, 3)]
            ax.add_patch(Rectangle((x/D, y/D), h/D, h/D, facecolor=color, edgecolor="#35424b", linewidth=.35))
        ax.set(xlim=(0, M), ylim=(0, M), aspect="equal", xlabel="x", ylabel="y")
        ax.set_title(f"M={M}, delta={case['delta_fraction']}: point bound {case['best_robust_point_upper']}\n{case['initial_vertices']} -> {case['best_vertices']} leaves")
    ax = axes.ravel()[3]
    for case in cases:
        stages = case["adaptive_stages"]
        x = [s["vertices"] for s in stages]
        y = [s["effective_point_upper"] for s in stages]
        if case["best_robust_point_upper"] < y[-1]:
            x.append(case["best_vertices"])
            y.append(case["best_robust_point_upper"])
        ax.plot(x, y, "o-", label=f"M={case['M']}, delta={case['delta_fraction']}")
    ax.set(xlabel="Number of partition leaves", ylabel="Certified robust point upper bound", title="Finite-delta bounds, including packing baseline")
    ax.grid(alpha=.2)
    ax.legend(fontsize=9)
    fig.suptitle("Adaptive outer approximations for Erdős #953\nFinite robust point bounds; no new continuous-area order proved", fontsize=14)
    fig.savefig(HERE/result["figure"], dpi=160)

    record_path = HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    record = json.loads(record_path.read_text(encoding="utf-8"))
    record["graph_upper_adaptive_research"] = {"summary": outfile.name, "notes": result["notes"],
        "audit": result["audit"], "fixed_delta_bounds": [{"M": c["M"], "delta": c["delta_fraction"],
            "upper": c["best_robust_point_upper"]} for c in cases],
        "variable_scale_gram_derivation": "removes minimum-leaf-size loss; recovers existing order only",
        "continuous_upper_improvement_proved": False, "new_asymptotic_order_proved": False,
        "lean_formalized": False}
    record_path.write_text(json.dumps(record, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({"cases": [{k: v for k, v in c.items() if k not in ("adaptive_stages", "uniform_control")} for c in cases],
        "independently_audited_certificates": len(audit["results"]), "summary": outfile.name}, ensure_ascii=False), flush=True)


if __name__ == "__main__":
    main()
