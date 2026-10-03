"""Summarize exactly audited exploratory graph-method certificates."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def main():
    auditfile = f"erdos953-graph-methods-independent-audit-{STAMP}.json"
    audit = json.loads((HERE/auditfile).read_text())
    assert audit["all_passed"]
    for r in audit["full_matrix_theta_certificates"]+audit["spectral_certificates"]:
        assert hashlib.sha256((HERE/r["certificate"]).read_bytes()).hexdigest() == r["sha256"]
    for r in audit["cosine_certificates"]:
        assert hashlib.sha256((HERE/r["file"]).read_bytes()).hexdigest() == r["sha256"]
    old = json.loads((HERE/f"erdos953-square-window-cover-summary-{STAMP}.json").read_text())
    base = {(r["M"], r["N"]): r for r in old["rows"]}
    theta = json.loads((HERE/f"erdos953-theta-results-{STAMP}.json").read_text())["results"]
    spectral = json.loads((HERE/f"erdos953-graph-spectral-results-{STAMP}.json").read_text())["results"]
    rows = []
    for r in theta:
        b = base[r["M"], r["N"]]
        rows.append({"M": r["M"], "N": r["N"], "vertices": r["vertices"],
                     "previous_integer_upper": b["best_integer_upper"],
                     "new_integer_upper": r["integer_upper"],
                     "previous_grid_area_upper": b["best_grid_area_upper"],
                     "new_grid_area_upper": r["area_upper_fraction"],
                     "improvement_fraction": str(F(b["best_integer_upper"]-r["integer_upper"], b["best_integer_upper"])),
                     "certificate": r["certificate"], "is_continuous_upper_at_this_N": False})
    summary = {"theta_comparison": rows, "all_certificates_independently_verified": True,
               "theta_windows_improved": sum(r["new_integer_upper"] < r["previous_integer_upper"] for r in rows),
               "theta_certificates": len(theta), "spectral_certificates": len(spectral),
               "spectral_shell_ansatz_improved_previous_bounds": False,
               "spectral_scope": "one real weight per integer-distance shell; this does not rule out stronger spectral methods",
               "scalar_small_subgraph_cut_barrier": "LP with all clique constraints and subgraph rank cuts of bounded size h has optimum >= |V|/max(h,omega); no sqrt(M) order after fine-grid limit for fixed h",
               "priorities": [
                   {"method": "full theta-prime plus conditional exact-subgraph constraints", "status": "full theta-prime tested; conditional constraints proposed", "priority": 1},
                   {"method": "three-point Boolean constraints and higher-order moments", "status": "research direction, no new computed certificate this round", "priority": 2},
                   {"method": "boundary-modulated Fourier/Gram feature families", "status": "explicit PSD family proposed, scalability and uniform bounds unproved", "priority": 3},
                   {"method": "multiscale weighted occupancy-state graphs", "status": "valid relaxation direction specified; no new asymptotic construction", "priority": 4},
                   {"method": "padded weighted spectral graphs with richer directional weights", "status": "radial shell ansatz tested and did not improve bounds", "priority": 5},
                   {"method": "Haemers rank and finite-field fitting matrices", "status": "unexplored algebraic route; no applicable low-rank certificate yet", "priority": 6},
                   {"method": "supersaturation and containers", "status": "needs an applicable quantitative structural lemma", "priority": 7}],
               "uniform_in_N_continuous_improvement_proved": False,
               "new_logarithmic_improvement_proved": False, "lean_formalized": False,
               "research_note": f"erdos953-graph-methods-notes-{STAMP}.txt", "independent_audit": auditfile}
    (HERE/f"erdos953-graph-methods-summary-{STAMP}.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    shown = sorted(rows, key=lambda r: (r["M"], r["N"]))
    plt.rcParams.update({"font.size": 11, "axes.spines.top": False, "axes.spines.right": False})
    fig, ax = plt.subplots(figsize=(10, 4.7), constrained_layout=True)
    x = np.arange(len(shown))
    before = [r["previous_integer_upper"] for r in shown]
    after = [r["new_integer_upper"] for r in shown]
    b1 = ax.bar(x-.18, before, .36, label="Previous clique/Fourier upper", color="#a8b7c5")
    b2 = ax.bar(x+.18, after, .36, label="Certified full-matrix PSD upper", color="#237ca8")
    ax.bar_label(b1, padding=3)
    ax.bar_label(b2, padding=3)
    for i, r in enumerate(shown):
        pct = 100*float(F(r["improvement_fraction"]))
        if pct:
            ax.text(i, max(before[i], after[i])+7, f"{pct:.1f}% tighter", ha="center", fontsize=9, color="#237ca8")
    ax.set_xticks(x, [f"M={r['M']}\nN={r['N']}" for r in shown])
    ax.set_ylabel("Certified maximum number of selected cells")
    ax.set_ylim(0, max(before)*1.22)
    ax.grid(axis="y", alpha=.2)
    ax.set_axisbelow(True)
    ax.legend(loc="upper left", fontsize=9)
    ax.set_title("Full-matrix semidefinite certificates improve five of six test windows\nFinite-grid upper bounds; no continuous upper bound at sampled N is claimed", fontsize=12)
    fig.savefig(HERE/f"erdos953-graph-methods-comparison-{STAMP}.png", dpi=180)
    plt.close(fig)

    currentpath = HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current = json.loads(currentpath.read_text(encoding="utf-8"))
    current["graph_upper_method_experiments"] = {
        "summary": f"erdos953-graph-methods-summary-{STAMP}.json", "independent_audit": auditfile,
        "finite_grid_improvements": rows, "theta_certificates": len(theta),
        "spectral_certificates": len(spectral), "all_independently_verified": True,
        "new_uniform_continuous_upper_proved": False, "new_logarithmic_improvement_proved": False,
        "lean_formalized": False}
    currentpath.write_text(json.dumps(current, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({"theta_certificates": len(theta), "spectral_certificates": len(spectral),
                      "windows_improved": summary["theta_windows_improved"], "all_verified": True,
                      "comparison": rows}, indent=2))


if __name__ == "__main__":
    main()
