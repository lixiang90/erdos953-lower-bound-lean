"""All integer epsilon annuli of the original infinite A_infinity.

Computes complete point-to-rectangle distance intervals, without enumerating
millions of radii or subtracting two nearly equal huge floating numbers.
Blocks 6..11 are scanned, and ALL later blocks have a rational phase envelope.
Green pixels are a conservative diagnostic; separately selected entire cells
are independently checked with Fraction against the finite sources and tail.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.patches import Rectangle, Polygon
from erdos953_square_limit_construction import parameters, center
from erdos953_infinite_ring_extension import hull

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
EPSILONS = (F(1,64), F(1,512), F(1,32768))
LAST = 11
FIRST_TAIL = 12


def sources():
    out = [(0,0,F(1,512))]
    for j in range(6,LAST+1):
        k,n = parameters(j)
        for ds in product(range(k-1),repeat=n):
            x,y = center(j,ds)
            out.append((x,y,F(1,256*k**3)))
    return out


def tail_envelope(X,Y,umax,vmax):
    """Rational enclosure of d-(y_source-Y), equal to -v+[lo,hi].

    Future x,y lie in [B,5B/4] x [3B^2,7B^2/2], B>=2^12.
    Old future half-heights <=1/32768. Bounds are uniform in future digits.
    """
    B = 2**FIRST_TAIL
    U, V = umax+F(1,8), vmax+F(1,32768)
    bmin, amin = B-abs(X), 3*B*B-abs(Y)
    assert bmin > U and amin > V
    C = (F(7,2)+F(abs(Y),B*B))/(1-F(abs(X),B))**2
    D = (F(5,4)+F(abs(X),B))**2/(3-F(abs(Y),B*B))
    u, v = U/bmin, V/amin
    lo = (1-u)**2/C/(2*(1+v)+D*(1+u)**2/(2*amin*(1-v)))-F(1,32768)
    hi = D*(1+u)**2/(2*(1-v))+F(1,32768)
    assert 0 < lo < hi < 1
    return lo,hi


def exact_conflict(box, source, eps):
    xlo,xhi,ylo,yhi = box
    sx,sy,h = source
    slo,shi = sy-h/2, sy+h/2
    dxlo = max(sx-F(1,8)-xhi,xlo-(sx+F(1,8)),0)
    dylo = max(slo-yhi,ylo-shi,0)
    dxhi = max(abs(xlo-(sx+F(1,8))),abs(xhi-(sx-F(1,8))))
    dyhi = max(abs(ylo-shi),abs(yhi-slo))
    L, U = dxlo*dxlo+dylo*dylo, dxhi*dxhi+dyhi*dyhi
    m0 = math.isqrt(U.numerator//U.denominator)
    for m in (m0,m0+1):
        if m >= 1 and L <= (m+eps)**2 and U >= (m-eps)**2:
            return True
    return False


def tail_cell_safe(vlo,vhi,lo,hi,eps):
    a,b = lo-vhi-eps,hi-vlo+eps
    ceil_a = -((-a.numerator)//a.denominator)
    floor_b = b.numerator//b.denominator
    return ceil_a > floor_b


def safe_base():
    Q = 2**24
    cy, r = -9*Q//32, Q//2-2
    bottom,top = -45*Q//64+1,9*Q//64-1
    ps = []
    for t in np.linspace(0,2*math.pi,2048,endpoint=False):
        x,y = round(r*math.cos(t)),cy+round(r*math.sin(t))
        if bottom <= y <= top: ps.append((x,y))
    for y in (bottom,top):
        x = math.isqrt(r*r-(y-cy)**2)-1
        ps.extend([(x,y),(-x,y)])
    vs = hull(ps)
    area = F(sum(x*Y-y*X for (x,y),(X,Y) in zip(vs,vs[1:]+vs[:1])),2*Q*Q)
    data = {"coordinate_denominator":Q,"vertices":vs,"area_fraction":str(area),
            "vertical_strip":["-45/64","9/64"],
            "enclosing_open_disk_center":["0","-9/32"],"enclosing_disk_radius":"1/2",
            "epsilon":"1/64","exact_area_expression":"27*sqrt(295)/2048 + asin(27/32)/2",
            "claim":"misses all old-source positive-integer epsilon annuli including every future block"}
    path = HERE/f"erdos953-Ainfty-all-integer-safe-base-{STAMP}.json"
    path.write_text(json.dumps(data,separators=(",",":")),encoding="utf-8")
    return data


def masks(window,src,nx=256,ny=256):
    X,Y,umin,umax,vmin,vmax = window
    u = np.linspace(float(umin),float(umax),nx,endpoint=False)+(float(umax-umin)/nx/2)
    v = np.linspace(float(vmin),float(vmax),ny,endpoint=False)+(float(vmax-vmin)/ny/2)
    uu,vv = np.meshgrid(u,v)
    covered = [np.zeros((ny,nx),dtype=bool) for e in EPSILONS]
    for sx,sy,H in src:
        h = float(H)/2
        dx = np.abs((X-sx)+uu)
        xlo,xhi = np.maximum(dx-.125,0),dx+.125
        a = abs(Y-sy)
        if a:
            sign = 1 if Y>sy else -1
            lo_delta,hi_delta = sign*vv-h,sign*vv+h
            yl,yh = a+lo_delta,a+hi_delta
            assert yl.min() > 0
            lo = lo_delta+xlo*xlo/(np.sqrt(yl*yl+xlo*xlo)+yl)
            hi = hi_delta+xhi*xhi/(np.sqrt(yh*yh+xhi*xhi)+yh)
        else:
            dy = np.abs(vv)
            yl,yh = np.maximum(dy-h,0),dy+h
            lo,hi = np.sqrt(yl*yl+xlo*xlo),np.sqrt(yh*yh+xhi*xhi)
        for e,mask in zip(EPSILONS,covered):
            mlo = np.maximum(np.ceil(lo-float(e)),1-a)
            mask |= np.floor(hi+float(e)) >= mlo
    tlo,thi = tail_envelope(X,Y,max(abs(umin),abs(umax)),max(abs(vmin),abs(vmax)))
    outputs = []
    cells = []
    for e,mask in zip(EPSILONS,covered):
        maybe_tail = np.floor(-vv+float(thi+e)) >= np.ceil(-vv+float(tlo-e))
        # 0=proved outside tail envelope and finite annuli; 1=finite-covered;
        # 2=finite-free but future envelope cannot certify it.
        status = np.where(mask,1,np.where(maybe_tail,2,0))
        available = np.flatnonzero(status.ravel()==0)
        candidates = available[np.linspace(0,len(available)-1,min(48,len(available)),dtype=int)] if len(available) else []
        accepted = []
        for ix in candidates:
            row,col = divmod(int(ix),nx)
            ul = umin+(umax-umin)*F(col,nx)
            ur = umin+(umax-umin)*F(col+1,nx)
            vl = vmin+(vmax-vmin)*F(row,ny)
            vr = vmin+(vmax-vmin)*F(row+1,ny)
            if not tail_cell_safe(vl,vr,tlo,thi,e): continue
            box = (X+ul,X+ur,Y+vl,Y+vr)
            if any(exact_conflict(box,s,e) for s in src): continue
            accepted.append([str(z) for z in box])
        cells.append({"epsilon":str(e),"boxes":accepted,
                      "box_area_each":str((umax-umin)*(vmax-vmin)/(nx*ny)),
                      "tail_phase_interval":[str(tlo),str(thi)]})
        outputs.append({"epsilon":str(e),"finite_covered_pixels":int(mask.sum()),
            "guaranteed_uncovered_pixels":int((status==0).sum()),
            "tail_uncertain_pixels":int((status==2).sum()),"pixels":nx*ny,
            "exact_whole_cells_checked":len(accepted),"status":status})
    return outputs,cells


def main():
    src = sources()
    base = safe_base()
    # Two representatives illustrate both a large hole and a nearly integer pair.
    x,y = center(6,(0,0))
    X,Y = center(6,(0,1))
    windows = [
        ("Origin",(0,0,F(-1),F(1),F(-6,5),F(9,10))),
        ("Block 6, digits (0,0)",(x,y,F(-2,5),F(2,5),F(-1,20),F(1,20))),
        ("Block 6, digits (0,1)",(X,Y,F(-2,5),F(2,5),F(-1,100),F(1,100))),
    ]
    fig,axes = plt.subplots(3,3,figsize=(13,10))
    cmap = ListedColormap(["#b6dfbf","#de9f99","#eed799"])
    summary = {"source":"original A_infinity", "finite_sources":len(src),
               "finite_block_indices":[6,LAST],"analytic_tail_start":FIRST_TAIL,
               "all_positive_integer_radii_included":True,
               "pixel_counts_are_not_area_certificates":True,
               "green":"finite-free and outside a uniform rational envelope of ALL future annuli",
               "red":"covered by a finite-source integer epsilon annulus",
               "yellow":"finite-free, but future envelope is inconclusive", "windows":[]}
    cert = {"finite_prefix_last":LAST,"all_future_first":FIRST_TAIL,"windows":[]}
    for row,(name,w) in enumerate(windows):
        results,cells = masks(w,src)
        data = {"name":name,"center":[w[0],w[1]],"offset_window":[str(z) for z in w[2:]],"epsilons":[]}
        cert["windows"].append({"name":name,"center":[w[0],w[1]],
                                 "offset_window":[str(z) for z in w[2:]],"cell_groups":cells})
        for col,r in enumerate(results):
            ax = axes[row,col]
            ax.imshow(r.pop("status"),origin="lower",extent=[float(z) for z in w[2:]],
                      cmap=cmap,vmin=0,vmax=2,aspect="auto",interpolation="nearest")
            if row == 0:
                Q = base["coordinate_denominator"]
                ax.add_patch(Polygon(np.array(base["vertices"])/Q,closed=True,fill=False,edgecolor="#214d80",linewidth=1.5))
                height = 1/512
            else: height = 1/(256*4**3)
            ax.add_patch(Rectangle((-.125,-height/2),.25,height,fill=False,edgecolor="black",linewidth=1.3))
            if row:
                jcert = json.loads((HERE/f"erdos953-Ainfty-ring-block-j6-{STAMP}.json").read_text())
                idx = 0 if row==1 else 1
                H = jcert["height_numerators"][idx]/jcert["height_denominator"]
                ax.add_patch(Rectangle((-1/6,-H/2),1/3,H,fill=False,edgecolor="#214d80",linewidth=1.4))
            ax.set_title(f"{name}; epsilon={r['epsilon']}",fontsize=10)
            ax.set_xlabel("x offset")
            ax.set_ylabel("y offset")
            data["epsilons"].append(r)
        summary["windows"].append(data)
    fig.suptitle("ALL positive integer annuli of the original infinite set\nGreen: certified tail exclusion; red: finite coverage; yellow: tail inconclusive\nBlack: original region; blue: proposed enlargement (not necessarily safe for that fixed epsilon)",fontsize=12)
    fig.tight_layout(rect=[0,0,1,.91])
    fig.savefig(HERE/f"erdos953-Ainfty-all-integer-rings-{STAMP}.png",dpi=170)
    plt.close(fig)
    summary["epsilon_safe_base"] = {"epsilon":"1/64","area_fraction":base["area_fraction"],
        "area_decimal":float(F(base["area_fraction"])),
        "analytic_area_decimal":27*math.sqrt(295)/2048+math.asin(27/32)/2,
        "certificate":f"erdos953-Ainfty-all-integer-safe-base-{STAMP}.json"}
    # Explicit counterexample to fixed-epsilon robustness of the original set.
    k = 4
    a,b = 8*k*(k*k-k+2),2
    summary["fixed_epsilon_obstruction"] = {"j":6,"first_digits":[0,1],"second_digits":[2,0],
        "vertical_integer":a,"horizontal_difference":b,
        "distance_to_integer":"4/(sqrt(a^2+4)+a)","strict_upper_bound":str(F(2,a)),
        "epsilon_1_over_64_conflict":F(2,a)<F(1,64),
        "general_upper_bound":"1/[4*k*(k^2-k+2)] tends to zero"}
    (HERE/f"erdos953-Ainfty-all-integer-rings-results-{STAMP}.json").write_text(json.dumps(summary,indent=2),encoding="utf-8")
    (HERE/f"erdos953-Ainfty-all-integer-ring-cells-{STAMP}.json").write_text(json.dumps(cert,separators=(",",":")),encoding="utf-8")
    print(json.dumps(summary,ensure_ascii=False),flush=True)


if __name__ == "__main__": main()
