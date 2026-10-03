"""Make a reproducible summary and plots from the checked random experiments."""

from fractions import Fraction
from pathlib import Path
import json

from erdos953_random_point_search import plot_results

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def main():
    path = HERE / f"erdos953-random-point-results-{STAMP}.json"
    report = json.loads(path.read_text(encoding="utf-8"))
    for result in report["results"]:
        if "graph_independent_set_exactly_audited" in result:
            result["graph_independent_set_all_pairs_audited"] = result.pop("graph_independent_set_exactly_audited")
        result["graph_pair_audit_arithmetic"] = "float64 (continuous certificates use exact integers)"
    report["continuous_adaptive_ball_union_lemma"] = (
        "r_i <= min(1/2, min_j min_k |distance(p_i,p_j)-k|/2); "
        "r_i+r_j <= each forbidden-distance gap. Open ball unions avoid integers by the triangle inequality."
    )
    report["method_background_primary_source"] = "https://arxiv.org/abs/1804.09099"
    report["optimizer_certifies_global_independence_number"] = False
    path.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    polygons = json.loads((HERE/f"erdos953-random-polygons-audit-{STAMP}.json").read_text(encoding="utf-8"))["results"]
    balls = json.loads((HERE/f"erdos953-random-balls-independent-audit-{STAMP}.json").read_text(encoding="utf-8"))["results"]
    exact = {item["file"]: Fraction(item["area_fraction"]) for item in polygons+balls}
    previous = {1.: .8950191291901026, 1.5: .9176478349623267, 2.: .928030414065414}
    summary = {"experiment_count": len(report["results"]),
               "total_training_points": sum(r["N"] for r in report["results"]),
               "sample_sizes": sorted({r["N"] for r in report["results"]}),
               "epsilon_values": sorted({r["epsilon"] for r in report["results"]}),
               "ball_pairs_checked_exactly": sum(a["ball_pairs_checked"] for a in balls),
               "all_polygon_certificates_verified": len(polygons),
               "all_ball_grid_certificates_verified": len(balls),
               "globally_optimal_areas_proved": False,
               "lean_formalization_of_new_certificates": False, "radii": []}
    for R in [1., 1.5, 2.]:
        subset = [r for r in report["results"] if r["R"] == R]
        candidate_files = [r["polygon_certificate"] for r in subset if r["polygon_certificate"]]
        candidate_files += [r["ball_grid_certificate"] for r in subset if r.get("ball_grid_certificate")]
        winner = max(candidate_files, key=lambda filename: exact[filename])
        fraction = exact[winner]
        point_proxy = next(r for r in subset if r["N"] == 32000 and r["epsilon"] == .008)
        summary["radii"].append({"R": R, "selected_at_N32000_epsilon0008": point_proxy["selected_count"],
                                "point_fraction_area_proxy": point_proxy["training_fraction_area_proxy"],
                                "best_random_construction_area_fraction": str(fraction),
                                "best_random_construction_area_decimal": float(fraction),
                                "best_random_certificate": winner,
                                "previous_analytic_lower_bound_decimal": previous[R],
                                "improvement_over_previous_percent": max(0., (float(fraction)/previous[R]-1)*100),
                                "best_known_in_this_workspace_lower_bound_decimal": max(float(fraction), previous[R])})
    (HERE/f"erdos953-random-search-summary-{STAMP}.json").write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    plot_results(report["results"])
    text = f"""JSP-000793 / Erdős #953 小半径随机点研究，{STAMP}

结论：随机搜索改善了本工作区 R=1.5、R=2 的已核验构造下界。
R=1.5：20385620360334689/20000000000000000 = 1.01928101801673445（四个凸多边形）。
R=2：259783/250000 = 1.039132（有理矩形并集）。
R=1：本轮随机构造未超过已有双叶面积 0.8950191291901026。
这些是实际可测集合的面积下界，未证明不受形状限制的 M(R) 最优值。
这些新证书尚未连接 Lean；验证器及其几何正确性的证明如下。

实验：24 组，累计 336000 个训练点；每轮 N=4000、12000 或 32000。
epsilon=0.008、0.015、0.03、0.06；各例及随机种子见结果 JSON。
圆盘均匀采样：(x,y)=R sqrt(U)(cos(2 pi V), sin(2 pi V))，U,V 独立均匀。
对每对点及每个相关整数 k，在 |distance-k|<=epsilon 时加冲突边。
图还包含 k=2R 的边缘安全带；虽然开圆盘本身无法达到该距离，这有助于安全扩张。
优化 max sum(z_i)，约束 z_i+z_j<=1（所有冲突边）、z_i in {{0,1}}。
大图使用随机初值、空间生长、已知双叶对照、退火与局部交换。并未证明图最优。
保存选中点后另行全点对复查（浮点数）。最终构造证书的审核全部用整数/Fraction。
独立面积测试每例 500000 点，大样本例为 1000000 点；95% Wilson 区间只针对固定并集。
240 点小图 MILP：R=1 求得最优 86 点；R=1.5、2 限时 12 秒未证明图最优。

点比例：A_hat = pi R^2 K/N。N=32000、epsilon=.008 时：
R=1：9179/32000，A_hat=0.9011462177281472。
R=1.5：4815/32000，A_hat=1.0636009190883882。
R=2：2944/32000，A_hat=1.156106096521044。
同一批点既用来优化又用来计数，比例可能受选择偏差影响，不能当作 M(R) 的上界。
固定 epsilon 会排除整数周围一整条距离带；不同 epsilon 的优化目标也不同。
epsilon=0 时随机有限点几乎必然全可选，比例会误导性地等于 1。
因此需要同时检查 N、epsilon、优化初值，并从形状提取连续构造；本轮没有宣称收敛到全局最优。

连续构造一：凸多边形。
以空间聚类找出直径<1的点组，构造凸包；也尝试把安全圆盘的内接顶点纳入凸包。
将顶点四舍五入到分母 10^8 的有理网格，之后完全重新检查。
每个顶点严格在 D_R 内，故由圆盘凸性，整个凸多边形在 D_R 内。
凸多边形最大直径在顶点对处取得；所有顶点对距离平方<1。
两凸多边形最大距离在顶点对处取得；最小距离用顶点到边的投影、交叉与包含检验求出。
投影在边内时距离平方=cross^2/edge_length^2，所以无需浮点开方。
对每个整数 k 检验 k^2 不在 [minimum_distance^2,maximum_distance^2] 内。
多边形内部两两不交，鞋带公式精确计算面积；取开内部即可。

连续构造二：安全圆盘及有理矩形。
令 g_ij=min_k |distance(p_i,p_j)-k|，r_i=min(1/2,min_j g_ij/2)。
于是 r_i+r_j<=g_ij。圆盘内两点之间距离相对中心距离的变化严格小于 r_i+r_j。
同一圆盘任意两点的距离<1；不同圆盘的距离区间避开所有相关整数。交上 D_R 保持合法。
中心四舍五入到分母 Q=10^8，半径向下舍入再减 32/Q，之后由整数验证器重新检查。
对于整数 k，设中心距离平方 d2、半径和 s（都按 Q 缩放）：
若 d2<(kQ)^2，则要求 kQ>s 且 d2<(kQ-s)^2；否则要求 d2>(kQ+s)^2。
此处恰好检验两球的全部可能距离，而非只检查采样点。
对 1/1000 网格，仅保留四角均严格在某个安全圆盘及 D_R 内的完整网格单元。
每行用附带圆盘编号的互不重叠矩形段表示；凸性保证每个矩形完全合法。
矩形开内部的面积相加，是单元数/1000000；无需积分或蒙特卡洛误差。
R=2 的证书验证 2647 个球、3501981 个球对、101278 个矩形段，面积为 1039132/1000000。
两个圆盘矩形证书总共检验 13458934 个球对，24 个多边形证书全部通过独立检查。

主要文件：
erdos953_random_point_search.py：随机实验及优化、独立面积测试、图形。
verify_953_random_polygons.py：独立纯整数/有理数多边形审核。
erdos953_random_ball_certificates.py：从安全圆盘提取精确矩形证书。
verify_953_random_balls.py：独立纯整数圆盘及矩形审核。
erdos953-random-point-results-{STAMP}.json：逐例参数、种子与结果。
erdos953-random-search-summary-{STAMP}.json：汇总与最佳证书文件名。
*.npz：所有随机点、选中掩码以及安全球半径，用于重建形状。

复现单例（在工作区根目录）：
python research/erdos953_random_point_search.py --append --cases 1.5:32000:.008:95503 --test-n 1000000 --sweeps 180
python research/erdos953_random_point_search.py --append --cases 2:32000:.03:95506 --test-n 1000000 --sweeps 180
python research/erdos953_random_ball_certificates.py --top 1 --radii 1.5 2 --grid 1000
python research/verify_953_random_polygons.py --output research/erdos953-random-polygons-audit-{STAMP}.json
python research/verify_953_random_balls.py --output research/erdos953-random-balls-independent-audit-{STAMP}.json
python research/summarize_953_random_search.py

方法背景：DeCorte–de Oliveira Filho–Vallentin, Complete positivity and distance-avoiding sets,
https://arxiv.org/abs/1804.09099 （距离规避及独立集的研究背景；不作为本次有限圆盘最优性的证明。）
本次构造只声称相对本工作区已有下界的改进，尚未进行完整新颖性审查，也未提交新的奖项声明。
"""
    (HERE/f"erdos953-random-search-notes-{STAMP}.txt").write_text(text, encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
