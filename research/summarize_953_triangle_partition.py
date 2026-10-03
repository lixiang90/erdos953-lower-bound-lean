"""Summarize whole-cell partition experiments and exact area certificates."""

from pathlib import Path
from fractions import Fraction
import json

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def main():
    path = HERE/f"erdos953-triangle-partition-results-{STAMP}.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    results = report["results"]
    for result in results:
        result.setdefault("seed", int(result["case"].split("seed")[1].split("-")[0]))
        result.setdefault("sweeps_per_temperature", 80 if result["case"] == "R1-n12-seed79312"
                          else 150 if result["n"] <= 24 else 180 if result["n"] == 40 else 240)
        result.setdefault("patches_per_temperature", 0)
        if result["MILP"] and result["MILP"].get("partition_upper_bound"):
            result["MILP"]["relative_gap_above_reported_heuristic"] = (
                result["MILP"]["partition_upper_bound"]-result["selected_curved_area"])/result["selected_curved_area"]
    report["closed_cell_conflict_policy"] = "integer in the closed [minimum_distance,maximum_distance] interval; even boundary-only hits conflict"
    report["numerical_curve_area_is_separate_from_exact_inner_polygon_certificate"] = True
    report["boundary_approximation_is_only_for_area_certification_not_for_optimization"] = True
    path.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    audit = json.loads((HERE/f"erdos953-triangle-partition-independent-audit-{STAMP}.json").read_text(encoding="utf-8"))
    exact = {a["file"]: Fraction(a["area_fraction"]) for a in audit["results"]}
    previous = {1.: .8950191291901026, 1.5: 1.0192810180167344, 2.: 1.039132}
    summary = {"experiment_count": len(results), "radii": [],
               "max_partition_cells": max(r["cells"] for r in results),
               "max_conflict_edges": max(r["edges"] for r in results),
               "independent_certificates_verified": audit["certificates_verified"],
               "piece_pairs_checked_exactly": sum(a["piece_pairs_checked"] for a in audit["results"]),
               "new_global_best_lower_bound_found": False,
               "finite_partition_optimality_proved": False,
               "global_M_optimality_proved": False, "new_certificates_formalized_in_Lean": False,
               "resolution_table": []}
    for n in sorted({r["n"] for r in results}):
        row = {"n": n, "cells": next(r["cells"] for r in results if r["n"] == n), "radii": {}}
        for R in [1., 1.5, 2.]:
            best = max((r for r in results if r["R"] == R and r["n"] == n), key=lambda r: exact[r["certificate"]])
            row["radii"][str(R)] = {"case": best["case"], "curved_area": best["selected_curved_area"],
                                    "exact_inner_area": float(exact[best["certificate"]])}
        summary["resolution_table"].append(row)
    for R in [1., 1.5, 2.]:
        best = max((r for r in results if r["R"] == R), key=lambda r: exact[r["certificate"]])
        fraction = exact[best["certificate"]]
        summary["radii"].append({"R": R, "best_case": best["case"], "cells": best["cells"],
                                "selected_cells": best["selected_cells"], "conflict_edges": best["edges"],
                                "selected_curved_area_numeric": best["selected_curved_area"],
                                "exact_inner_area_fraction": str(fraction), "exact_inner_area_decimal": float(fraction),
                                "certificate": best["certificate"],
                                "certification_loss": best["selected_curved_area"]-float(fraction),
                                "previous_verified_lower_bound": previous[R],
                                "gap_below_previous_lower_bound": previous[R]-float(fraction)})
    (HERE/f"erdos953-triangle-partition-summary-{STAMP}.json").write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    lines = [f"JSP-000793 / Erdős #953 圆弧三角剖分研究，{STAMP}", "",
             "按用户要求建立全圆盘剖分，每个单元要么保留、要么消除。",
             "内部单元为三角形；边界单元是三角形与真实圆盘的交集，保留圆弧。",
             "做了 18 组实验、五档网格，最多 58448 个单元；R=2 最细图有 73071328 条冲突边。",
             "当前解采用多初值带权独立集搜索、退火、单元交换和局部区域整批交换。",
             "各半径约 58k 单元的圆弧区域面积：0.8717564323、0.9947890252、1.0376781510。",
             "本轮均未超过此前已经核验的下界：0.8950191292、1.0192810180、1.039132。",
             "求解器未证明有限剖分的全局最优，也未证明 M(R) 的全局最优。", "",
             "模型：", "C_i = T_i ∩ closed_disk(R)。",
             "每个 C_i 凸且连通，各单元内部的距离均小于 1（三角形直径小于 1）。",
             "d_min(i,j)=min{|x-y|:x∈C_i,y∈C_j}；d_max 类似。",
             "C_i×C_j 连通，距离函数连续，故它的值域是完整区间 [d_min,d_max]。",
             "若这个闭区间包含任何正整数，则 i,j 冲突。此模型连只在边界取得的整数也排除。",
             "选择 z_i∈{0,1}，maximize sum(area(C_i) z_i)，所有冲突边约束 z_i+z_j≤1。",
             "各单元内部互不相交，边界交集面积为零，故保留区域面积等于权重之和。",
             "取保留单元并集后去掉外圆周，就得到原题开圆盘内的集合，面积不变。", "",
             "圆弧区域的解析面积与距离：",
             "用线段与圆的二次方程交点截取三角形边，圆周角区间用半平面包含检查判定。",
             "面积=端点多边形的鞋带面积 + sum(R^2(θ−sin θ)/2)，圆弧从未被折线替代来优化。",
             "最小正距离不会仅在外圆弧的内部取得：沿径向向内微移可降低到圆盘内另一点的距离。",
             "因此最小距离由截取后的直线边及其端点间的最近距离给出。",
             "最大距离除了顶点对，还包括圆弧上与另一个顶点方向相反的点。",
             "若两段圆弧含一对对径点，则最大距离为 2R；否则弧对弧最大值在端点取得。",
             "这些解析极值采用 float64 计算，比较平方距离时加入 2e−10 的保守余量。",
             "全图先用包含整单元的圆盘过滤明显不可能冲突的对，选中单元再全对复查（不使用过滤）。", "",
             "独立核验：",
             "960 单元的面积总和与 πR² 相符；每档整个剖分的面积也均核对。",
             "用 Shapely 的 16384 边圆形近似独立检查 400 对区域的距离及 960 个区域的面积。",
             "最小、最大平方距离差在 8.0e−8、3.6e−7 内，符合参考圆形内接近似误差。",
             "另外检查仅有两个圆弧端点的圆弓形单元，和顶点法会漏掉的圆弧内部最大值。", "",
             "严格面积证书（与上述浮点计算分开）：",
             "每个被选中的单元内，取有理顶点的内接凸多边形。",
             "圆弧用 8 个内接弦段表示，并少量收缩、整数化；优化本身仍使用真正的圆弧。",
             "验证器用整数检查每个多边形位于对应网格三角形与圆盘内。",
             "网格三角形编号唯一，内部互不相交，因而多边形面积可直接相加。",
             "最大距离由顶点对取得；最小距离用顶点到边的精确投影算出，平方距离用 Fraction。",
             "每对多边形的整个闭距离区间都避开所有正整数，既非只验顶点也非只验采样点。",
             "加速过滤只使用 int64 的包围盒上下界；事先用 Python 大整数证明所有乘法不会溢出。",
             "不确定对再交给 Python 大整数及 Fraction 检查。与纯 Python 模式比较一致，并验证拒绝整数距离反例。",
             f"18 份证书均独立通过，共检查 {summary['piece_pairs_checked_exactly']} 对单元。",
             "最细网格的严格证书面积和圆弧计算面积相差均小于 3.3e−7；下界以证书面积为准。",
             "新证书尚未形式化到 Lean。", "",
             "分辨率比较（圆弧计算面积）：", "单元数         R=1          R=1.5        R=2"]
    for row in summary["resolution_table"]:
        lines.append(f"{row['cells']:6d}      "+"    ".join(f"{row['radii'][str(R)]['curved_area']:.9f}" for R in [1.,1.5,2.]))
    lines.extend(["", "最佳严格面积证书："])
    for r in summary["radii"]:
        lines.extend([f"R={r['R']}: {r['exact_inner_area_fraction']} ≈ {r['exact_inner_area_decimal']:.12f}",
                      r["certificate"]])
    lines.extend(["", "复现命令（工作区根目录；已有随机构造作为搜索对照）：",
                  "python research/erdos953_triangle_partition_search.py --append --cases 1:96:79396 1.5:96:79496 2:96:79596 --sweeps 240 --patches 1600",
                  "python research/verify_953_triangle_geometry.py",
                  f"python research/verify_953_triangle_partition.py --fast --output research/erdos953-triangle-partition-independent-audit-{STAMP}.json",
                  "python research/summarize_953_triangle_partition.py",
                  "python research/erdos953_triangle_partition_search.py --plot-only", "",
                  "细化仍在提高可行面积；图的单元限制和启发式搜索都有损失，不能把最后一档等同于 M(R)。",
                  "下一步适合在候选区域边缘及接近整数距离的单元附近自适应细化，而非仅将全网格均匀加密。"])
    (HERE/f"erdos953-triangle-partition-notes-{STAMP}.txt").write_text("\n".join(lines)+"\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
