"""Collect certified bounds, preserve theorem scope, and plot grid limits."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"


def rebuild_clique_manifest():
    # Each immutable window certificate is authoritative. Rebuild the index
    # from all completed windows, including the last R=2 window and finer R=1.
    rows=[]
    for R,Ns in ((1,(4,6,8,12,16,24,32)),(2,(8,12,16))):
        for N in Ns:
            filename=f"erdos953-grid-clique-upper-R{R}-N{N}-{STAMP}.json"
            data=json.loads((HERE/filename).read_text())
            row={k:v for k,v in data.items() if k!="weighted_cliques"}
            row.update(certificate=filename,cliques=len(data["weighted_cliques"]))
            rows.append(row)
    (HERE/f"erdos953-square-grid-clique-upper-results-{STAMP}.json").write_text(
        json.dumps({"results":rows,"finite_graph_upper_only":True},indent=2),encoding="utf-8")
    print(json.dumps({"complete_clique_windows":len(rows)}))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--prepare",action="store_true")
    args=parser.parse_args()
    if args.prepare:
        rebuild_clique_manifest()
        return
    kernels=json.loads((HERE/f"erdos953-square-grid-upper-results-{STAMP}.json").read_text())["results"]
    cliques=json.loads((HERE/f"erdos953-square-grid-clique-upper-results-{STAMP}.json").read_text())["results"]
    audit=json.loads((HERE/f"erdos953-square-grid-upper-independent-audit-{STAMP}.json").read_text())
    assert audit["all_passed"] and len(audit["certificates"])==len(kernels)==14
    assert len(audit["clique_certificates"])==len(cliques)==10
    by_key={}
    for method,entries in (("Fourier kernel",kernels),("fractional clique cover",cliques)):
        for row in entries:
            key=(row["R"],row["N"])
            if key not in by_key or row["integer_upper"]<by_key[key]["integer_upper"]:
                by_key[key]={"R":row["R"],"N":row["N"],"vertices":row["vertices"],
                    "integer_upper":row["integer_upper"],"grid_area_upper":row["area_upper_fraction"],
                    "method":method,"certificate":row["certificate"]}
    rows=sorted(by_key.values(),key=lambda r:(F(r["R"]),r["N"]))
    for row in rows:
        row["grid_area_upper_decimal"]=float(F(row["grid_area_upper"]))
        row["finite_vertex_density_upper"]=float(F(row["integer_upper"],row["vertices"]))
        lower=HERE/f"erdos953-square-grid-R{row['R']}-N{row['N']}-free-{STAMP}.json"
        if lower.exists():
            data=json.loads(lower.read_text())
            low=F(data["area_fraction"])
            assert low<=F(row["grid_area_upper"])
            row["previous_certified_grid_lower"]=str(low)
            row["previous_lower_certificate"]=lower.name
        row["is_upper_bound_for_continuous_M_at_this_N"]=False
    summary={"infinite_graph_upper_Banach_density":"0 for every N>=2",
        "exact_maximum_cells_in_any_one_row":"N-1",
        "finite_window_alpha_upper":"2*(N-1)*ceil(N*R)",
        "elementary_continuous_upper":"M(R)<=2R",
        "continuous_limit":"M(R)=lim_N alpha_N(R)/N^2 for each fixed R",
        "upper_certificate_limit":"M(R)<=liminf_N U_N(R)/N^2",
        "known_uniform_grid_upper":"alpha_N(R)<=C*N^2*sqrt(R), universal C, N>=11 and R>=1",
        "known_continuous_upper":"M(R)<=C*sqrt(R), attributed existing Poisson-Bessel result",
        "new_uniform_constant_proved":False,"new_logarithmic_improvement_proved":False,
        "finite_bounds":rows,"certified_kernel_windows":14,"certified_clique_windows":10,
        "unique_finite_windows":len(rows),"finite_optimum_claimed":False,"lean_formalized_new_work":False,
        "proof_notes":f"erdos953-square-grid-upper-notes-{STAMP}.txt",
        "independent_audit":f"erdos953-square-grid-upper-independent-audit-{STAMP}.json"}
    (HERE/f"erdos953-square-grid-upper-summary-{STAMP}.json").write_text(json.dumps(summary,indent=2),encoding="utf-8")
    fig,axes=plt.subplots(1,3,figsize=(14,4.4))
    r1=[r for r in rows if r["R"]=="1"]
    axes[0].plot([r["N"] for r in r1],[r["grid_area_upper_decimal"] for r in r1],"o-",label="Certified finite-grid upper",color="#427b99")
    lows=[r for r in r1 if "previous_certified_grid_lower" in r]
    axes[0].plot([r["N"] for r in lows],[float(F(r["previous_certified_grid_lower"])) for r in lows],"o-",label="Existing finite-grid lower",color="#488d63")
    axes[0].axhline(.8950191291901026,color="#ae625d",linestyle="--",label="Known continuous lower for M(1)")
    axes[0].set_xlabel("N, with cell side length 1/N")
    axes[0].set_ylabel("Grid area")
    axes[0].set_title("R=1: finite mesh upper is not M(1) upper",fontsize=10)
    axes[0].legend(fontsize=7)
    for N,color in ((4,"#427b99"),(8,"#488d63")):
        rs=[r for r in rows if r["N"]==N]
        axes[1].plot([float(F(r["R"])) for r in rs],[r["grid_area_upper_decimal"]/math.sqrt(float(F(r["R"]))) for r in rs],"o-",label=f"N={N}",color=color)
    axes[1].set_xlabel("R")
    axes[1].set_ylabel("Finite-grid area upper / sqrt(R)")
    axes[1].set_title("Fixed-N curves do not certify a limit constant",fontsize=10)
    axes[1].legend(fontsize=8)
    L=[2**k for k in range(1,17)]
    for N,color in ((4,"#427b99"),(16,"#488d63"),(64,"#ae625d")):
        axes[2].loglog(L,[min(1,(N-1)/x) for x in L],label=f"N={N}",color=color)
    axes[2].set_xlabel("L: side length of square window in cells")
    axes[2].set_ylabel("Proved density upper: min(1,(N-1)/L)")
    axes[2].set_title("Infinite-graph density is exactly zero",fontsize=10)
    axes[2].legend(fontsize=8)
    for ax in axes: ax.grid(alpha=.18)
    fig.tight_layout()
    fig.savefig(HERE/f"erdos953-square-grid-upper-{STAMP}.png",dpi=170)
    plt.close(fig)
    current_path=HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current=json.loads(current_path.read_text())
    current["upper_bound_research"]={"date":STAMP,"summary":f"erdos953-square-grid-upper-summary-{STAMP}.json",
        "proof_notes":summary["proof_notes"],"independent_audit":summary["independent_audit"],
        "known_continuous_order":"O(sqrt(R))","new_order_improvement":False,
        "finite_graph_upper_bounds_are_not_continuous_upper_at_fixed_N":True,
        "new_work_lean_formalized":False}
    current_path.write_text(json.dumps(current,indent=2),encoding="utf-8")
    print(json.dumps({"windows":len(rows),"certificates":24,"finite_bounds":rows},ensure_ascii=False))


if __name__=="__main__": main()
