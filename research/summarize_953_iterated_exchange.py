"""Summarize hash-matched exact audits; plot finite gains without extrapolation."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
from verify_953_iterated_ring_holes import baseline

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def read(name):
    return json.loads((HERE/name).read_text(encoding="utf-8"))


def sha(name):
    return hashlib.sha256((HERE/name).read_bytes()).hexdigest()


def audited(name):
    d = read(name)
    report_name = Path(name).stem+"-independent-audit.json"
    report = read(report_name)
    assert report["all_passed"] and report["sha256"] == sha(name)
    return d, report, report_name


def run():
    fill_name = f"erdos953-iterated-ring-holes-exchange-input-{STAMP}.json"
    exchange_name = f"erdos953-ring-exchange-{STAMP}.json"
    restore_name = f"erdos953-ring-exchange-restoration-{STAMP}.json"
    fill, fa, fan = audited(fill_name)
    exchange, ea, ean = audited(exchange_name)
    restore, ra, ran = audited(restore_name)
    assert exchange["input_sha256"] == sha(fill_name)
    assert restore["input_sha256"] == sha(fill_name)
    assert restore["exchange_sha256"] == sha(exchange_name)
    assert all(r["all_future_scales_included"] for r in (fa, ea, ra))
    assert ea["all_uniform_generation_floors_retained"] and ra["all_uniform_generation_floors_retained"]
    main_name = f"erdos953-iterated-ring-holes-multiscale-{STAMP}.json"
    assert sha(main_name) == sha(fill_name)
    # Main and snapshot are byte-identical; reuse the completed full audit,
    # explicitly recording the provenance rather than leaving a stale report.
    main_report = dict(fa, certificate=main_name,
        audit_reused_from_byte_identical_certificate=fill_name,
        audit_reused_from_report=fan)
    (HERE/(Path(main_name).stem+"-independent-audit.json")).write_text(
        json.dumps(main_report, indent=2)+"\n", encoding="utf-8")
    fill_gain = F(fill["added_area_fraction"])
    whole_gain = F(exchange["net_gain_fraction"])
    recovered = F(ra["restored_area_fraction"])
    added = sum((F(o["added_area_fraction"]) for o in exchange["operations"]), F(0))
    gross_deleted = sum((F(o["removed_area_fraction"]) for o in exchange["operations"]), F(0))
    deleted = F(ra["final_deleted_area_fraction"])
    exchange_gain = F(ra["exchange_plus_restoration_net_gain_fraction"])
    assert added-gross_deleted == whole_gain
    assert gross_deleted-recovered == deleted and added-deleted == exchange_gain
    total = fill_gain+exchange_gain
    sources, labels = baseline(fill)
    previous_gen = {j: sum(((b[1]-b[0])*(b[3]-b[2]) for b, g in zip(sources, labels) if g == j), F(0)) for j in range(6, 14)}
    final_gen = {int(j): F(a) for j, a in ra["generation_areas_after"].items()}
    assert sum(final_gen.values(), F(0))-sum(previous_gen.values(), F(0)) == total
    summary = {
        "date": STAMP, "all_independent_audits_passed_and_hash_matched": True,
        "source_set": "A_infinity_plus_plus", "new_set": "A_infinity_iterated_exchange",
        "new_set_contains_source_set": False,
        "rounds": fill["rounds"], "fill_added_rectangles": len(fill["added_rectangles"]),
        "fill_net_gain_fraction": str(fill_gain),
        "exchange_candidates": exchange["candidate_count"],
        "accepted_exchanges": len(exchange["operations"]),
        "new_target_area_fraction": str(added),
        "gross_deleted_area_fraction": str(gross_deleted),
        "restored_pieces": ra["restored_pieces"], "restored_area_fraction": str(recovered),
        "final_deleted_area_fraction": str(deleted),
        "exchange_plus_restoration_net_gain_fraction": str(exchange_gain),
        "total_net_gain_fraction": str(total), "total_net_gain_decimal": float(total),
        "finite_components_including_base_enclosure": ea["active_components"]+ra["restored_pieces"],
        "modified_generations": list(range(6, 14)), "unchanged_uniform_tail_first_generation": 14,
        "large_radius_additive_improvement": {"valid_for_every_real_R_at_least": 4**14,
            "delta_fraction": str(total), "delta_decimal": float(total)},
        "retained_uniform_lower_bound": {"coefficient": "1/55296",
            "factor": "sqrt(R)*(log(log(R))/log(R))^3", "validity": "every real R>=e",
            "proof_basis": "unchanged curved base and uniform tail; exact generation floors and containment checked"},
        "generation_areas_after": ra["generation_areas_after"],
        "certificates": [{"file": n, "sha256": sha(n), "audit": a} for n, a in ((fill_name, fan), (exchange_name, ean), (restore_name, ran))],
        "full_lean_formalization": False, "new_asymptotic_order_proved": False,
        "finite_optimum_proved": False,
        "limitations": ["finite modifications inside one fixed bounded region cannot change the asymptotic order",
            "only 43 windows tested; generations 8 through 13 sampled, not fully scanned",
            "copying additions to future scales requires a new cross-scale proof",
            "fixed A_infinity tail restrictions are optional for a separate finite-radius construction"],
        "research_note": f"erdos953-iterated-fill-exchange-notes-{STAMP}.txt",
        "figure": f"erdos953-iterated-fill-exchange-{STAMP}.png"
    }
    summary_name = f"erdos953-iterated-fill-exchange-summary-{STAMP}.json"
    (HERE/summary_name).write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    current_name = f"erdos953-current-certified-lower-bounds-{STAMP}.json"
    current = read(current_name)
    current["iterated_lower_bound_research"] = {"summary": summary_name,
        "status": "exact positive finite-area gains with all future scales checked; no asymptotic-order improvement",
        "total_net_gain_fraction": str(total), "total_net_gain_decimal": float(total),
        "exchange_plus_local_crop_net_gain_fraction": str(exchange_gain),
        "large_radius_additive_threshold": 4**14, "independent_audits": [fan, ean, ran],
        "full_lean_formalization": False, "new_asymptotic_order_proved": False}
    current["uniform_lower_bounds"]["one_fixed_unbounded_set_iterated_exchange"] = dict(
        summary["retained_uniform_lower_bound"], set=summary["new_set"],
        full_lean_formalization=False, summary=summary_name,
        large_radius_additive_improvement=summary["large_radius_additive_improvement"])
    (HERE/current_name).write_text(json.dumps(current, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")

    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False})
    fig, axs = plt.subplots(2, 2, figsize=(12, 8), constrained_layout=True)
    ax = axs[0, 0]
    rounds = [F(r["area_fraction"]) for r in fill["rounds"] if r["round"].startswith("refine")]
    stages = [F(0), rounds[0], fill_gain, fill_gain+whole_gain, total]
    ax.plot(range(5), list(map(float, stages)), "o-", color="#2464a3", lw=2)
    ax.set_xticks(range(5), ["Old set", "Fill 1", "Fill 2", "Exchange", "Local crop"])
    ax.set_ylabel("Net area above old A_infinity++")
    ax.set_title("Two fills, two exchanges, 30 restored pieces")
    for i, a in enumerate(stages):
        ax.annotate(f"{float(a):.6f}", (i, float(a)), xytext=(0, 9), textcoords="offset points", ha="center", fontsize=9)
    ax.set_ylim(-.02, .405)
    ax = axs[0, 1]
    vals = list(map(float, (added, gross_deleted, recovered, exchange_gain)))
    bars = ax.bar(range(4), vals, color=["#2464a3", "#b24848", "#31845b", "#6f51a6"])
    ax.set_xticks(range(4), ["New targets", "Whole deletion", "Restored", "Final net gain"])
    ax.set_ylabel("Area (exchange stage only)")
    ax.set_title("Partial deletion improves the exchange profit")
    ax.set_ylim(0, .038)
    for b, v in zip(bars, vals):
        ax.text(b.get_x()+b.get_width()/2, v+.0008, f"{v:.6f}", ha="center", fontsize=9)
    ax = axs[1, 0]
    candidates = [g for g in restore["groups"] if F(g["retained_area_fraction"]) > 0]
    g = max(candidates, key=lambda z: len(z["retained_pieces"]))
    l, r, b, t = map(F, g["source_box"])
    ax.add_patch(Rectangle((0, 0), 1, 1, facecolor="#edc1c1", edgecolor="#a14444"))
    for p in g["retained_pieces"]:
        box = p["box"] if isinstance(p, dict) else p
        pl, pr, pb, pt = map(F, box)
        ax.add_patch(Rectangle((float((pl-l)/(r-l)), float((pb-b)/(t-b))),
            float((pr-pl)/(r-l)), float((pt-pb)/(t-b)), facecolor="#31845b", edgecolor="white", lw=.5))
    fraction = F(g["retained_area_fraction"])/((r-l)*(t-b))
    ax.set(xlim=(0, 1), ylim=(0, 1), xlabel="Normalized parent width", ylabel="Normalized parent height")
    ax.set_title(f"Source {g['source_id']}: green {100*float(fraction):.1f}% restored")
    ax.set_aspect("equal")
    ax = axs[1, 1]
    beta = 7*math.sqrt(15)/128+math.asin(7/8)/2
    old_values, new_values = [], []
    old_sum = new_sum = F(0)
    for j in range(6, 14):
        old_sum += previous_gen[j]
        new_sum += final_gen[j]
        old_values.append(beta+float(old_sum))
        new_values.append(beta+float(new_sum))
    xs = [4**(j+1) for j in range(6, 14)]
    ax.semilogx(xs, old_values, "o-", label="Old A_infinity++", color="#828282")
    ax.semilogx(xs, new_values, "o-", label="After fill and cropped exchange", color="#2464a3")
    ax.set(xlabel="Complete-generation radius R_j = 4^(j+1)", ylabel="Constructed area inside disk")
    ax.set_title("Certified finite-prefix areas; unchanged infinite tail")
    ax.legend(fontsize=9)
    fig.suptitle("Erdos 953: finite improvements, no new growth exponent", fontsize=15)
    fig.savefig(HERE/summary["figure"], dpi=160)
    fig.savefig(HERE/summary["figure"].replace(".png", ".svg"))
    print(json.dumps({"summary": summary_name, "total_gain": str(total), "total_gain_decimal": float(total),
        "exchange_gain_decimal": float(exchange_gain), "candidate_count": exchange["candidate_count"],
        "figure": summary["figure"], "all_hashes_match": True}, indent=2))


if __name__ == "__main__":
    run()
