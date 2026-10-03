"""Report exact areas and draw the certified all-integer-ring additions."""
from fractions import Fraction as F
from pathlib import Path
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from erdos953_square_limit_construction import parameters,block_area

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"


def main():
    result=json.loads((HERE/f"erdos953-Ainfty-ring-extension-results-{STAMP}.json").read_text())
    extra=json.loads((HERE/f"erdos953-Ainfty-all-ring-hole-extension-{STAMP}.json").read_text())
    audit=json.loads((HERE/f"erdos953-Ainfty-ring-extension-independent-audit-{STAMP}.json").read_text())
    assert audit["all_passed"]
    beta=7*math.sqrt(15)/128+math.asin(7/8)/2
    beta_inner=F(result["base"]["area_fraction"])
    extra_area=F(extra["area_fraction"])
    optimized={b["j"]:F(b["extended_area_fraction"]) for b in result["blocks"]}
    old=F(1,2048)
    new_rectangles=F(0)
    growth=[]
    for j in range(6,61):
        k,n=parameters(j)
        old+=block_area(j)
        new_rectangles+=optimized.get(j,F((k-1)**n,108*k**3))
        lower=beta_inner+new_rectangles+extra_area
        growth.append({"j":j,"R":str(4**(j+1)),"old_exact_area":str(old),
                       "new_rational_lower":str(lower),"new_rational_lower_decimal":float(lower),
                       "new_exact_area_expression":f"7*sqrt(15)/128 + asin(7/8)/2 + {new_rectangles+extra_area}",
                       "new_area_decimal":beta+float(new_rectangles+extra_area)})
    summary={"construction":"A_infinity_plus_plus contains the original A_infinity",
        "base_area_expression":"7*sqrt(15)/128 + asin(7/8)/2","base_area_decimal":beta,
        "base_rational_inner_area":str(beta_inner),"additional_area_fraction":str(extra_area),
        "uniform_block_area_multiplier":"256/27","uniform_coefficient":"1/55296",
        "validity":"all real R>=e","growth_factor":"sqrt(R)*(log(log(R))/log(R))^3",
        "growth_order_of_this_fixed_set":"Theta(sqrt(R)*(log(log(R))/log(R))^3)",
        "not_a_sharpness_claim_for_M":True,"full_lean_formalization":False,
        "finite_optimum_proved":False,"sample_complete_radii":[g for g in growth if g["j"] in (6,9,12,13,20,40,60)],
        "finite_exact_pair_checks":audit["finite_exact_pairs"]+audit["all_integer_ring_cells"]["exact_source_pairs"]+audit["additional_hole_extension"]["exact_source_pairs"]+audit["additional_hole_extension"]["exact_added_pairs"],
        "proof_notes":f"erdos953-Ainfty-all-integer-rings-notes-{STAMP}.txt",
        "independent_audit":f"erdos953-Ainfty-ring-extension-independent-audit-{STAMP}.json"}
    (HERE/f"erdos953-Ainfty-ring-extension-summary-{STAMP}.json").write_text(json.dumps(summary,indent=2),encoding="utf-8")
    fig,axes=plt.subplots(1,3,figsize=(15,4.5))
    ax=axes[0]
    ax.add_patch(Rectangle((-.4,1/256),.8,31/256,facecolor="#f3e7e5",edgecolor="none"))
    first_window=extra["window_groups"][0]
    for values in extra["added_rectangles"][:first_window["rectangle_count"]]:
        l,r,b,t=map(F,values)
        ax.add_patch(Rectangle((float(l-64),float(b-12288)),float(r-l),float(t-b),
                               facecolor="#4f9f78",edgecolor="none"))
    cert=json.loads((HERE/f"erdos953-Ainfty-ring-block-j6-{STAMP}.json").read_text())
    H=cert["height_numerators"][0]/cert["height_denominator"]
    ax.add_patch(Rectangle((-1/6,-H/2),1/3,H,facecolor="#3b6d9d",edgecolor="none"))
    ax.set_xlim(-.42,.42)
    ax.set_ylim(-.006,.13)
    ax.set_xlabel("x - 64")
    ax.set_ylabel("y - 12288")
    ax.set_title(f"First window: {first_window['rectangle_count']} added rectangles\nAll 9 windows: area {extra['area_fraction']}",fontsize=10)
    ax.text(.01,.985,"Green: added; blue: existing rectangle",transform=ax.transAxes,fontsize=8,va="top")
    axes[1].bar([b["j"] for b in result["blocks"]],[b["multiplier_over_old"] for b in result["blocks"]],color="#428caa")
    axes[1].axhline(256/27,color="#444",linestyle="--",label="Uniform enlargement: 256/27")
    axes[1].set_xlabel("Block index j")
    axes[1].set_ylabel("Enlarged block area / original block area")
    axes[1].set_title(f"Rational height optimization\nExcludes the base and {len(extra['added_rectangles'])} extra rectangles",fontsize=10)
    axes[1].legend(fontsize=8)
    axes[2].semilogy([g["j"] for g in growth],[float(F(g["old_exact_area"])) for g in growth],label="Original fixed set",color="#777")
    axes[2].semilogy([g["j"] for g in growth],[g["new_rational_lower_decimal"] for g in growth],label="New fixed set: certified lower",color="#4f9f78")
    axes[2].set_xlabel("j, with R_j = 4^(j+1)")
    axes[2].set_ylabel("Area inside B(R_j)")
    axes[2].set_title("One compatible infinite construction\nSame asymptotic order; improved area",fontsize=10)
    axes[2].legend(fontsize=8)
    for ax in axes: ax.grid(alpha=.15)
    fig.tight_layout()
    fig.savefig(HERE/f"erdos953-Ainfty-ring-extension-summary-{STAMP}.png",dpi=170)
    plt.close(fig)
    current_path=HERE/f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current=json.loads(current_path.read_text())
    current["uniform_lower_bounds"]["one_fixed_unbounded_set_enlarged"]={
        "coefficient":"1/55296","factor":summary["growth_factor"],"validity":"every real R>=e",
        "set":"A_infinity_plus_plus, a superset of the original A_infinity",
        "full_lean_formalization":False,"proof":summary["proof_notes"],"independent_audit":summary["independent_audit"],
        "finite_addition_area":extra["area_fraction"],"summary":f"erdos953-Ainfty-ring-extension-summary-{STAMP}.json"}
    current["latest_infinite_set_research"]={"summary":f"erdos953-Ainfty-ring-extension-summary-{STAMP}.json",
        "all_integer_annuli":True,"fixed_epsilon_not_used_as_global_constraint":True,
        "finite_exact_pair_checks":summary["finite_exact_pair_checks"],"full_lean_formalization":False}
    current_path.write_text(json.dumps(current,indent=2),encoding="utf-8")
    print(json.dumps(summary,ensure_ascii=False))


if __name__=="__main__": main()
