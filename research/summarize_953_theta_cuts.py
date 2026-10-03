"""Summarize independently audited finite bounds and scope of new lemmas."""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def brief(d, path):
    counts = {"conditional_rank": 0, "boolean_three": 0}
    largest = 0
    for cut in d["cuts"]:
        members = cut["members"] if cut["kind"] == "reflection_orbit" else [cut]
        for member in members:
            counts[member["kind"]] += 1
            if member["kind"] == "conditional_rank":
                largest = max(largest, len(member["vertices"]))
    return {"certificate": path.name, "tag": d["tag"],
        "integer_upper": d["integer_upper"], "alpha_upper_fraction": d["alpha_upper_fraction"],
        "area_upper_fraction": d["area_upper_fraction"], "active_cut_orbits": len(d["cuts"]),
        "individual_cut_counts": counts, "largest_conditional_subgraph": largest,
        "psd_optimality_proved": False}


def main():
    audit_path = HERE/f"erdos953-theta-cuts-independent-audit-{STAMP}.json"
    audit = json.loads(audit_path.read_text())
    assert audit["all_passed"]
    audit_rows = {row["certificate"]: row for row in audit["results"]}
    cases = {}
    for filename, proof in audit_rows.items():
        path = HERE/filename
        assert hashlib.sha256(path.read_bytes()).hexdigest() == proof["sha256"]
        d = json.loads(path.read_text())
        cases.setdefault((d["M"], d["N"]), []).append(brief(d, path))
    previous = {(row["M"], row["N"]): row["best_integer_upper"] for row in
                json.loads((HERE/f"erdos953-square-window-cover-summary-{STAMP}.json").read_text())["rows"]}
    for row in json.loads((HERE/f"erdos953-theta-results-{STAMP}.json").read_text())["results"]:
        key = row["M"], row["N"]
        previous[key] = min(previous.get(key, 10**20), row["integer_upper"])
    rows = []
    for (M, N), candidates in sorted(cases.items()):
        plain = min((r for r in candidates if not r["active_cut_orbits"]),
                    key=lambda r: F(r["alpha_upper_fraction"]))
        cuts = min((r for r in candidates if r["active_cut_orbits"]),
                   key=lambda r: F(r["alpha_upper_fraction"]))
        best = min(candidates, key=lambda r: F(r["alpha_upper_fraction"]))
        rows.append({"M": M, "N": N, "vertices": (M*N)**2,
            "previous_record_integer_upper": previous.get((M, N)),
            "baseline": plain, "cut_candidate": cuts, "best_new_certificate": best,
            "cut_candidate_improves_integer_bound": cuts["integer_upper"] < plain["integer_upper"],
            "normalized_grid_area_by_sqrt_M": float(F(best["area_upper_fraction"]))/math.sqrt(M),
            "finite_N_continuous_upper": False})
    summary = {"date": STAMP, "rows": rows,
        "certificates_verified": len(audit_rows), "windows": len(rows),
        "windows_with_integer_cut_improvement": sum(r["cut_candidate_improves_integer_bound"] for r in rows),
        "proof_scope": "upper bounds on selected complete square cells only; no continuous upper at finite N",
        "new_fixed_power_improvement_possible": False,
        "new_uniform_continuous_upper_proved": False, "new_logarithmic_saving_proved": False,
        "new_lemmas": [
            {"name": "fixed-size conditional/three-point dilution on vertex-transitive graphs",
             "bound": "1+(theta_prime-1)/h <= L_h <= theta_prime",
             "scope": "only the two homogeneous cut families implemented here; not a theorem about all ESC/SOS or finite box graphs",
             "status": "mathematical proof in note; not Lean formalized"},
            {"name": "nonnegative mixtures of the existing one-parameter Poisson-Bessel kernels",
             "bound": "worst-nonedge certificate cost is Omega(N^2*sqrt(M))",
             "scope": "even N>=4, integer M>=2, positive mixtures with s<=1/(B*N); not all PSD kernels",
             "status": "analytic proof from cited Poisson formula; not Lean formalized"},
            {"name": "phase-sensitive energy refinement",
             "bound": "|P| <= 1+C*N^2*sqrt(M)/E_phase(P)",
             "scope": "N>=11; consequence of existing kernel proof with ceil(distance)-distance retained",
             "status": "mathematical proof in note; growth of E_phase for large independent sets NOT proved"}],
        "next_structural_target": "uniform in N: every independent set is small at N^2*sqrt(M)/L(M) scale or its mean phase energy is >=L(M), with L(M)->infinity",
        "comparison_note": "M=4,N=8: shorter plain run 73 vs cut 72; equal total compute plain also reaches 72, so no integer cut improvement counted",
        "optimizer_optimality_used_as_proof": False, "lean_formalized": False,
        "audit": audit_path.name,
        "notes": f"erdos953-theta-cuts-asymptotic-notes-{STAMP}.txt",
        "audit_totals": {key: sum(r[key] for r in audit_rows.values()) for key in
            ("cuts_verified", "local_states_or_clique_pairs_checked", "nonedge_matrix_entries_checked", "psd_residual_rows_checked")}}
    (HERE/f"erdos953-theta-cuts-summary-{STAMP}.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    by_case = {(r["M"], r["N"]): r for r in rows}
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), constrained_layout=True)
    for ax, cases_on_axis, label in (
        (axes[0], [(M, 8) for M in (1, 2, 4)], "Square side M (N=8)"),
        (axes[1], [(2, N) for N in (4, 8, 16)], "Grid resolution N (M=2)")):
        x = [c[0] if ax is axes[0] else c[1] for c in cases_on_axis]
        plain = [float(F(by_case[c]["baseline"]["alpha_upper_fraction"]))/c[1]**2/math.sqrt(c[0]) for c in cases_on_axis]
        best = [float(F(by_case[c]["best_new_certificate"]["alpha_upper_fraction"]))/c[1]**2/math.sqrt(c[0]) for c in cases_on_axis]
        ax.plot(x, plain, "o--", color="#707e8e", label="Plain PSD certificate")
        ax.plot(x, best, "s-", color="#19769e", label="Best certificate with cuts available")
        ax.set_xlabel(label)
        ax.set_ylabel("Certified t / (N squared * sqrt(M))")
        ax.set_xticks(x)
        ax.grid(alpha=.25)
        ax.legend(fontsize=8)
    fig.suptitle("Finite-grid diagnostics: local gains do not establish a logarithmic saving", fontsize=12)
    figure = HERE/f"erdos953-theta-cuts-scaling-{STAMP}.png"
    fig.savefig(figure, dpi=170)
    plt.close(fig)
    # Preserve existing lower-bound data, adding a separate upper-research entry.
    current_path = HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current = json.loads(current_path.read_text())
    current["graph_upper_moment_research"] = {"summary": f"erdos953-theta-cuts-summary-{STAMP}.json",
        "audit": audit_path.name, "notes": summary["notes"], "certificates_verified": len(audit_rows),
        "finite_graph_only": True, "continuous_order_improvement_proved": False,
        "lean_formalized": False}
    current_path.write_text(json.dumps(current, indent=2), encoding="utf-8")
    print(json.dumps({"certificates_verified": len(audit_rows), "windows": len(rows),
        "integer_cut_improvements": summary["windows_with_integer_cut_improvement"],
        "bounds": [{"M": r["M"], "N": r["N"], "plain": r["baseline"]["integer_upper"],
                    "cuts": r["cut_candidate"]["integer_upper"], "best": r["best_new_certificate"]["integer_upper"]}
                   for r in rows], "figure": str(figure)}), flush=True)


if __name__ == "__main__":
    main()
