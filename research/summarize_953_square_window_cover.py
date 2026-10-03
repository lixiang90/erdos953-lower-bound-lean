"""Summarize audited square-window bounds without conflating the two limits."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def main():
    auditfile = f"erdos953-square-window-independent-audit-{STAMP}.json"
    audit = json.loads((HERE/auditfile).read_text(encoding="utf-8"))
    assert audit["all_passed"]
    for row in audit["certificates"]:
        assert hashlib.sha256((HERE/row["certificate"]).read_bytes()).hexdigest() == row["sha256"]
    for row in audit["cosine_certificates"]:
        assert hashlib.sha256((HERE/row["file"]).read_bytes()).hexdigest() == row["sha256"]
    kernels = json.loads((HERE/f"erdos953-square-window-kernel-results-{STAMP}.json").read_text())["results"]
    cliques = json.loads((HERE/f"erdos953-square-window-clique-results-{STAMP}.json").read_text())["results"]
    indexed = {}
    for r in kernels+cliques:
        indexed.setdefault((r["M"], r["N"]), {})[r["kind"]] = r
    rows = []
    for (M, N), kinds in sorted(indexed.items()):
        best = min(kinds.values(), key=lambda x: x["integer_upper"])
        rows.append({"M": M, "N": N, "vertices": (M*N)**2,
                     "row_grid_area_upper": str(F(M*(N-1), N)),
                     "kernel_grid_area_upper": kinds.get("kernel", {}).get("area_upper_fraction"),
                     "clique_grid_area_upper": kinds.get("clique", {}).get("area_upper_fraction"),
                     "best_integer_upper": best["integer_upper"],
                     "best_grid_area_upper": best["area_upper_fraction"],
                     "best_grid_selection_fraction_upper": str(F(best["integer_upper"], (M*N)**2)),
                     "best_certificate": best["certificate"],
                     "is_continuous_upper_at_this_N": False})
    summary = {"square_side": "M", "cell_side": "1/N", "vertices": "(MN)^2",
               "rows": rows, "all_certificates_independently_verified": True,
               "independent_audit": auditfile, "lean_formalized": False,
               "exact_continuous_limit": "S(M)=lim_N alpha(M,N)/N^2, for each fixed integer M>=1",
               "disk_comparison": "D(M/2)<=S(M)<=D(M/sqrt(2))",
               "row_cover": "MN^2 disjoint cliques, each containing M cells",
               "stronger_row_independence": "alpha(M,N)<=MN(N-1)",
               "fractional_clique_cover_barrier": {
                   "lower_limit": "liminf_N kappa_f(M,N)/N^2 >= 5*M/(11*sqrt(2))",
                   "upper_limit": "limsup_N kappa_f(M,N)/N^2 <= M",
                   "scope": "N tends to infinity for each fixed M; not a lower bound for independence or area",
                   "dependency": "Avdeev, arXiv:1906.11926, Corollary 2.18",
                   "uniform_explicit_threshold_N0_of_M_proved": False},
               "finite_direction_kernel_family": {
                   "bound": "alpha(M,N)<=1+(72*B^2/c)*N^2*sqrt(1+sqrt(2)*M)",
                   "parameters": "B>=max(1,A,1/s0); A,c,s0 from existing Poisson-Bessel negativity theorem",
                   "finite_frequency_count_H": "O(N*log(N*M))",
                   "finite_direction_count_J": "O(M*N*log(N*M))",
                   "external_dependency": "https://www.ulam.ai/research/erdos953-short.pdf, Proposition 4",
                   "new_numerical_uniform_constant_proved": False,
                   "scope": "analytic finite-feature discretization in the note, not the finite LP certificates"},
               "limiting_window_density": "S(M)/M^2=M^(-3/2+o(1)); existing square-root exponent transferred to squares",
               "new_logarithmic_improvement_proved": False,
               "research_note": f"erdos953-square-window-cover-notes-{STAMP}.txt"}
    (HERE/f"erdos953-square-window-cover-summary-{STAMP}.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False})
    fig, axs = plt.subplots(1, 3, figsize=(15.6, 4.8), constrained_layout=True)
    Mvals = [1, 2, 4, 8]
    axs[0].plot(Mvals, [7*M/8 for M in Mvals], "s--", color="#a5a5a5", label="Row independence bound")
    axs[0].plot(Mvals[:3], [float(F(indexed[M, 8]["clique"]["area_upper_fraction"])) for M in Mvals[:3]],
                "o-", color="#cd853f", label="Weighted clique cover")
    axs[0].plot(Mvals, [float(F(indexed[M, 8]["kernel"]["area_upper_fraction"])) for M in Mvals],
                "o-", color="#1c78a5", label="PSD Fourier certificate")
    axs[0].set(title="Ordinary square windows, fixed N = 8", xlabel="Square side M", ylabel="Certified finite-grid area upper")
    axs[0].set_xticks(Mvals)
    axs[0].legend(loc="upper left", fontsize=8)
    axs[0].grid(alpha=.2)

    Ns = [4, 8, 12, 16, 24, 32]
    axs[1].plot(Ns, [float(F(next(r for r in rows if r["M"] == 1 and r["N"] == N)["best_grid_area_upper"])) for N in Ns],
                "o-", color="#1c78a5", label="Best certified grid upper")
    axs[1].axhline(math.pi/4, color="#549354", linestyle=":", label="Continuous feasible disk: pi/4")
    axs[1].set(title="Refinement at M = 1", xlabel="Grid refinement N", ylabel="Area")
    axs[1].set_ylim(.4, .86)
    axs[1].legend(loc="lower right", fontsize=8)
    axs[1].text(.03, .94, "Finite-N bounds can lie below\ncontinuous feasible area.",
                transform=axs[1].transAxes, va="top", fontsize=9)
    axs[1].grid(alpha=.2)

    mm = np.geomspace(1, 10000, 100)
    axs[2].fill_between(mm, 5*mm/(11*math.sqrt(2)), mm, color="#cd853f", alpha=.22,
                       label="All clique covers: fine-grid limit band")
    axs[2].plot(mm, mm, "--", color="#cd853f", linewidth=1)
    axs[2].plot(mm, np.sqrt(mm), "-", color="#1c78a5", label="sqrt(M): exponent reference only")
    axs[2].set(xscale="log", yscale="log", title="Asymptotics after N tends to infinity",
               xlabel="Square side M", ylabel="Normalized certificate cost")
    axs[2].text(.03, .96, "PSD bound has form C sqrt(M).\nC remains unspecified.", transform=axs[2].transAxes,
                fontsize=9, va="top")
    axs[2].legend(loc="lower right", fontsize=7.7)
    axs[2].grid(alpha=.2, which="both")
    fig.suptitle("Integer-distance avoidance in MN by MN square-cell windows\nNumerical panels are finite-grid bounds, not continuous upper bounds at the sampled N", fontsize=13)
    fig.savefig(HERE/f"erdos953-square-window-cover-{STAMP}.png", dpi=170)
    plt.close(fig)

    # Preserve all existing lower constructions and their proof status.
    currentpath = HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current = json.loads(currentpath.read_text(encoding="utf-8"))
    current["square_window_cover_research"] = {k: summary[k] for k in
        ("exact_continuous_limit", "disk_comparison", "fractional_clique_cover_barrier",
         "finite_direction_kernel_family", "limiting_window_density",
         "new_logarithmic_improvement_proved", "lean_formalized")}
    current["square_window_cover_research"].update(
        summary=f"erdos953-square-window-cover-summary-{STAMP}.json",
        independent_audit=auditfile, distinct_windows=len(rows),
        kernel_certificates=len(kernels), clique_certificates=len(cliques))
    currentpath.write_text(json.dumps(current, indent=2, ensure_ascii=False), encoding="utf-8")
    print(json.dumps({"distinct_windows": len(rows), "kernel_certificates": len(kernels),
                      "clique_certificates": len(cliques), "all_passed": True,
                      "nonedge_displacements_checked": audit["nonedge_displacements_checked"],
                      "clique_pairs_checked": audit["clique_pairs_checked"]}))
    for r in rows:
        print(f"M={r['M']}, N={r['N']}: row={r['row_grid_area_upper']}, "
              f"clique={r['clique_grid_area_upper']}, kernel={r['kernel_grid_area_upper']}, "
              f"best={r['best_grid_area_upper']}")


if __name__ == "__main__":
    main()
