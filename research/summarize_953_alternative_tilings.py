"""Collect independently audited bounds and render the new grid constructions."""
from __future__ import annotations
from datetime import datetime,timezone
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

from verify_953_alternative_tilings import verify
from erdos953_alternative_tilings import make_tiling,planar_vertices

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
COLORS={"oct":"#4376b8","regular-oct":"#7146a7","hex":"#158779","square":"#777777"}
NAMES={"oct":"Octagon + square, cut 3/10","regular-oct":"Regular octagon + square",
       "hex":"Regular hexagon","square":"Square control"}
OLD={1:0.8950191291901026,1.5:float(Fraction(20385620360334689,20000000000000000)),
     2:float(Fraction(295605,262144)),4:float(Fraction(1203,1024)),8:float(Fraction(153,128))}
OLD_FRACTIONS={1:"586555002834469/655360000000000",1.5:"20385620360334689/20000000000000000",
               2:"295605/262144",4:"1203/1024",8:"153/128"}


def complete_audit(rows):
    path=HERE/f"erdos953-alternative-tilings-independent-audit-{STAMP}.json"
    previous=json.loads(path.read_text()) if path.exists() else {"results":[]}
    checked={r["certificate"]:r for r in previous["results"]}
    for row in rows:
        filename=row["certificate"]
        digest=hashlib.sha256((HERE/filename).read_bytes()).hexdigest()
        if filename not in checked or checked[filename]["sha256"]!=digest:
            checked[filename]=verify(HERE/filename)
            print(json.dumps({"verified":filename,"pairs":checked[filename]["pair_checks"]}),flush=True)
    all_checks=[checked[r["certificate"]] for r in rows]
    audit={"recorded_at_utc":datetime.now(timezone.utc).isoformat(),
           "certificates_verified":len(all_checks),"pair_checks":sum(r["pair_checks"] for r in all_checks),
           "method":"independent vertex-to-segment squared distances and separating-axis intersection, exact integral axial or Cartesian arithmetic with overflow bounds; no optimizer masks, FFT or Shapely",
           "regular_octagons":"full ideal cells are enclosed by rational proof polygons; exact ideal-cell area is used, not the sum of overlapping envelope areas",
           "source_sha256":{f:hashlib.sha256((HERE/f).read_bytes()).hexdigest() for f in
                            ["erdos953_alternative_tilings.py","verify_953_alternative_tilings.py"]},
           "lean_formalized":False,"results":all_checks}
    path.write_text(json.dumps(audit,indent=2),encoding="utf-8")
    return checked,audit


def effective_resolution(row):
    if row["family"] in ("oct","regular-oct"):
        return math.sqrt(2)*row["N"]
    if row["family"]=="hex":
        data=json.loads((HERE/row["certificate"]).read_text())
        return data["parameters"]["q"]/math.sqrt(3*math.sqrt(3)/2)
    return row["N"]


def plot_layouts():
    fig,axes=plt.subplots(1,2,figsize=(10,4.7),layout="constrained")
    a=1-1/math.sqrt(2)
    octagon=np.array([(a,0),(1-a,0),(1,a),(1,1-a),(1-a,1),(a,1),(0,1-a),(0,a)])
    diamond=np.array([(0,-a),(a,0),(0,a),(-a,0)])
    for x in range(-1,3):
        for y in range(-1,3):
            axes[0].add_collection(PolyCollection([octagon+[x,y]],facecolor="#5f83bd",edgecolor="white",linewidth=.8))
            axes[0].add_collection(PolyCollection([diamond+[x,y]],facecolor="#efad53",edgecolor="white",linewidth=.8))
    axes[0].set(xlim=(-.25,2.25),ylim=(-.25,2.25),title="Regular octagons and squares",
                xlabel="Area per parent square: (2sqrt(2)-2) + (3-2sqrt(2)) = 1")
    tiling=make_tiling("hex",16)
    labels=np.array([(a,b,0) for a in range(-3,4) for b in range(-3,4)],dtype=np.int32)
    vertices=planar_vertices(labels,tiling)*tiling.scale
    axes[1].add_collection(PolyCollection(vertices,facecolor="#54a397",edgecolor="white",linewidth=.8))
    axes[1].set(xlim=(-3.7,3.7),ylim=(-3.1,3.1),title="Regular hexagons",
                xlabel="Hexagon side s; cell area = 3sqrt(3)s^2/2")
    for ax in axes:
        ax.set_aspect("equal"); ax.set_xticks([]); ax.set_yticks([])
    fig.suptitle("Tiling geometry only: this picture does not select an admissible set")
    fig.savefig(HERE/f"erdos953-alternative-tilings-layouts-{STAMP}.png",dpi=180)
    plt.close(fig)


def plot_comparison(rows):
    fig,axes=plt.subplots(2,3,figsize=(13,7.5),layout="constrained")
    for ax,R in zip(axes.flat,[1,1.5,2,4,8]):
        for family in ["oct","regular-oct","hex","square"]:
            data=sorted([r for r in rows if r["R"]==R and r["family"]==family],key=effective_resolution)
            if data:
                ax.plot([effective_resolution(r) for r in data],[r["area"] for r in data],"o-",
                        color=COLORS[family],label=NAMES[family],markersize=3)
        ax.axhline(OLD[R],color="#bb403e",linestyle="--",label="Previous best bound")
        ax.set(xscale="log",title=f"R = {R:g}",xlabel="1 / sqrt(mean tile area)",ylabel="Certified area")
        ax.grid(alpha=.2)
    handles,labels=axes[0,0].get_legend_handles_labels()
    axes[1,2].axis("off")
    axes[1,2].legend(handles,labels,loc="upper left",frameon=False)
    axes[1,2].text(.03,.43,"Matched resolution:\nhexagon and square N=362\nvs octagon N=256;\nN=91 vs octagon N=64.\n\nAll points are lower bounds.\nNo finite optimum is claimed.",transform=axes[1,2].transAxes)
    fig.savefig(HERE/f"erdos953-alternative-tilings-comparison-{STAMP}.png",dpi=180)
    plt.close(fig)


def true_vertices(data):
    family,N=data["family"],data["N"]
    labels=np.array(data["cells"],dtype=np.int32)
    if family!="regular-oct":
        return planar_vertices(labels,make_tiling(family,N)),labels
    a=1-1/math.sqrt(2)
    templates=[np.array([(a,0),(1-a,0),(1,a),(1,1-a),(1-a,1),(a,1),(0,1-a),(0,a)]),
               np.array([(0,-a),(a,0),(0,a),(-a,0)])]
    polygons=[]
    for x,y,t in labels:
        polygons.append((templates[int(t)]+[x,y])/N)
    return polygons,labels


def plot_shapes(best):
    fig,axes=plt.subplots(2,3,figsize=(13,8),layout="constrained")
    for row,family in enumerate(["regular-oct","hex"]):
        for col,R in enumerate([1.5,4,8]):
            r=best[str(R)][family]
            data=json.loads((HERE/r["certificate"]).read_text())
            polygons,labels=true_vertices(data)
            colors=np.where(labels[:,2]==0,"#4c77b1","#d99531") if family=="regular-oct" else "#188979"
            ax=axes[row,col]
            ax.add_collection(PolyCollection(polygons,facecolor=colors,edgecolor="none"))
            ax.add_patch(plt.Circle((0,0),R,fill=False,color="#999999",linewidth=.8))
            ax.set(xlim=(-R*1.04,R*1.04),ylim=(-R*1.04,R*1.04),
                   title=f"{NAMES[family]}, R={R:g}\narea={r['area']:.6f}")
            ax.set_aspect("equal"); ax.set_xticks([]); ax.set_yticks([])
    fig.savefig(HERE/f"erdos953-alternative-tilings-constructions-{STAMP}.png",dpi=170)
    plt.close(fig)


def main():
    rows=json.loads((HERE/f"erdos953-alternative-tilings-results-{STAMP}.json").read_text())
    checks,audit=complete_audit(rows)
    best={}
    for R in [1,1.5,2,4,8]:
        key=str(R)
        best[key]={}
        for family in ["oct","regular-oct","hex","square"]:
            candidates=[r for r in rows if r["R"]==R and r["family"]==family]
            if candidates:
                winner=max(candidates,key=lambda r:Fraction(checks[r["certificate"]]["area_lower_fraction"]))
                best[key][family]={**winner,"independent_audit":checks[winner["certificate"]]}
    summary={"date":STAMP,"previous_best":OLD,"best_by_radius_and_family":best,
             "certificates":audit["certificates_verified"],"pair_checks":audit["pair_checks"],
             "finite_optimum_proved":False,"lean_formalized":False,
             "matched_resolution":"mean cell area; octagon tiling has two tiles per parent square",
             "interpretation":"new finite-radius constructions; these experiments do not establish an asymptotic growth law or a globally optimal grid"}
    (HERE/f"erdos953-alternative-tilings-summary-{STAMP}.json").write_text(json.dumps(summary,indent=2),encoding="utf-8")
    lines=["Erdős #953：八角形—正方形网格与正六边形网格",f"日期：{STAMP}","",
           "结果：全部构造已由独立的整数几何验证器核验。表中小数为显示近似，精确表达式在证书中。",
           "搜索为启发式，只给出严格面积下界，不宣称有限独立集最大值或 M(R) 最优值。",
           "这些新多边形证书尚未进行 Lean 形式化；此前统一精确常数下界的 Lean 定理仍保留。","",
           "半径 | 前轮最佳 | 截角3/10八角形+方格 | 正八角形+方格 | 正六边形 | 同程序正方形对照"]
    for R in [1,1.5,2,4,8]:
        bb=best[str(R)]
        lines.append(f"{R:g} | {OLD[R]:.12f} | "+" | ".join(f"{bb[f]['area']:.12f}" for f in ["oct","regular-oct","hex","square"]))
    lines.extend(["","网格和面积：",
                  "(1) 截角3/10：母方格边长1/N，四角各截直角边3/(10N)的三角形。",
                  "    剩余八角形面积41/(50N²)，每个顶点周围的小正方形面积9/(50N²)。",
                  "    O个八角形、S个小正方形的并集面积=(41O+9S)/(50N²)。",
                  "(2) 真正的正八角形网格：截角比例t=1-1/√2。",
                  "    面积=[3S-2O+2(O-S)√2]/N²。",
                  "    距离核验使用外包八角形截角0.292、外包小正方形截角0.293；",
                  "    通过2·708²≥1000²≥2·707²严格证明完整的代数坐标单元包含于外包区域。",
                  "    外包多边形可能重叠，面积只计算原正八角形网格单元，绝不累加外包区域面积。",
                  "(3) 正六边形：边长1/q，顶点采用轴坐标(a,b)，",
                  "    物理坐标=(a+b/2,√3 b/2)/q，平方范数=(a²+ab+b²)/q²。",
                  "    中心位于(2i+j,-i+j)/q，K个完整六边形面积=3K√3/(2q²)。","",
                  "冲突判据：",
                  "两个闭凸多边形之间的所有距离组成闭区间[dmin,dmax]。若其中含任一正整数，",
                  "则两单元冲突。最大平方距离在顶点对取得；最小平方距离用边交叠判定及",
                  "两个方向的顶点到线段距离取得。只需检测不超过dmax的最大正整数。",
                  "各单元顶点严格在开圆盘内，且各自直径小于1，故单元内部合法。",
                  "原网格单元的内部互不相交，边界零测度，因此可直接累加精确面积。","",
                  "搜索与比较：",
                  "粗网格采用面积权重的独立集贪心、局部替换与小空间簇替换。",
                  "细网格以此前证书及较粗网格作种子，只添加精确兼容的完整单元。",
                  "FFT、浮点坐标和Shapely只生成候选；最终距离、包含与面积不依赖其正确性。",
                  "八角形网格每个母方格有两个单元；六边形和正方形对照补算N=362和N=91，",
                  "使平均单元面积与八角形N=256、N=64匹配（取整误差约0.6%以内）。",
                  "正方形对照也会改善旧下界，不能把所有收益归于网格形状；各网格用相同旧种子。","",
                  "最佳精确证书："])
    for R in [1,1.5,2,4,8]:
        for family in ["oct","regular-oct","hex","square"]:
            r=best[str(R)][family]
            lines.append(f"  R={R:g}, {family}, N={r['N']}: {r['area_expression']}; {r['certificate']}")
    lines.extend(["","改进后的单调下界："])
    for R in [1.5,2,4,8]:
        candidates=list(best[str(R)].values())
        winner=max(candidates,key=lambda r:Fraction(r["independent_audit"]["area_lower_fraction"]))
        lower=Fraction(winner["independent_audit"]["area_lower_fraction"])
        previous=Fraction(OLD_FRACTIONS[R])
        if lower>previous:
            lines.append(f"  每个实数R≥{R:g}，M(R)≥{winner['area_expression']}（{winner['family']}）；")
            lines.append(f"  相对于前轮该半径下界，增幅约{100*(winner['area']/OLD[R]-1):.6f}%。")
    lines.extend(["可与此前全部半径的解析分段下界及其他证书取最大值。有限半径结果不证明新的渐近阶。","",
                  f"独立核验：{audit['certificates_verified']}个证书，{audit['pair_checks']}次完整单元对检查，",
                  "另检查全部顶点圆内包含、单元直径、唯一标签、平方根有理区间及int64无溢出界。",
                  f"核验文件：erdos953-alternative-tilings-independent-audit-{STAMP}.json。"])
    (HERE/f"erdos953-alternative-tilings-notes-{STAMP}.txt").write_text("\n".join(lines)+"\n",encoding="utf-8")
    plot_layouts()
    plot_comparison(rows)
    plot_shapes(best)
    print(json.dumps({"certificates":audit["certificates_verified"],"pair_checks":audit["pair_checks"],
                      "best":{R:{f:r['area'] for f,r in row.items()} for R,row in best.items()}},ensure_ascii=False),flush=True)


if __name__=="__main__":
    main()
