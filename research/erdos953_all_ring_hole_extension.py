"""Fill uncovered holes of ALL integer annuli of the enlarged infinite set.

Whole small cells are screened, compressed to rational rectangles and checked
with arbitrary-precision integers. All candidates lie in a diameter<1 window,
so they can all be added together. The infinite tail is excluded analytically.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import math
import numpy as np
from erdos953_square_limit_construction import parameters,center

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
EPS=F(1,512)
X,Y=64,12288
NX=320
NY=4096
COL0,COL1=-128,128
ROW0,ROW1=16,512


def load_sources():
    # Bounding rectangle of the curved base, used conservatively.
    boxes=[(F(-1,2),F(1,2),F(-23,32),F(5,32))]
    centers=[]
    for j in range(6,14):
        data=json.loads((HERE/f"erdos953-Ainfty-ring-block-j{j}-{STAMP}.json").read_text())
        k,n=parameters(j)
        for ds,h in zip(product(range(k-1),repeat=n),data["height_numerators"]):
            x,y=center(j,ds)
            H=F(h,data["height_denominator"])
            boxes.append((x-F(1,6),x+F(1,6),y-H/2,y+H/2))
            centers.append((x,y,H))
    return boxes,centers


def tail_bounds(X,Y):
    B=2**14
    U,V=F(2,5)+F(1,6),F(1,8)+F(1,512)
    bmin,amin=B-X,3*B*B-Y
    C=(F(7,2)+F(Y,B*B))/(1-F(X,B))**2
    D=(F(5,4)+F(X,B))**2/(3-F(Y,B*B))
    u,v=U/bmin,V/amin
    lo=(1-u)**2/C/(2*(1+v)+D*(1+u)**2/(2*amin*(1-v)))-F(1,512)
    hi=D*(1+u)**2/(2*(1-v))+F(1,512)
    assert lo-F(ROW1,NY)>EPS
    assert hi-F(ROW0,NY)<1-EPS
    return lo,hi


def proposal(boxes,X,Y):
    cols=np.arange(COL0,COL1)
    rows=np.arange(ROW0,ROW1)
    ul,ur=np.meshgrid(cols/NX,(rows+0.0)/NY)[0],np.meshgrid((cols+1)/NX,rows/NY)[0]
    vl,vr=np.meshgrid(cols/NX,rows/NY)[1],np.meshgrid(cols/NX,(rows+1)/NY)[1]
    safe=np.ones(ul.shape,dtype=bool)
    for left,right,bottom,top in boxes:
        sx,sy=(left+right)/2,round((bottom+top)/2)
        # Source intervals must not straddle the candidate window vertically,
        # except the candidate's own source, whose distance is always below 1.
        if sx==X and sy==Y:
            assert F(16,25)+F(31,256)**2 < (1-EPS)**2
            continue
        a=abs(Y-sy)
        if Y>sy:
            delta_lo=vl-float(top-sy)
            delta_hi=vr-float(bottom-sy)
        else:
            delta_lo=float(bottom-sy)-vr
            delta_hi=float(top-sy)-vl
        ylo,yhi=a+delta_lo,a+delta_hi
        xlo=np.maximum(np.maximum(float(left-X)-ur,ul-float(right-X)),0)
        xhi=np.maximum(np.abs(ul-float(right-X)),np.abs(ur-float(left-X)))
        assert ylo.min()>0
        dlo=delta_lo+xlo*xlo/(np.sqrt(ylo*ylo+xlo*xlo)+ylo)
        dhi=delta_hi+xhi*xhi/(np.sqrt(yhi*yhi+xhi*xhi)+yhi)
        safe &= np.floor(dhi+float(EPS)) < np.ceil(dlo-float(EPS))
    # Merge equal horizontal runs on adjacent rows.
    active={}
    rects=[]
    for row,line in zip(rows,safe):
        padded=np.r_[False,line,False].astype(np.int8)
        starts=np.flatnonzero(np.diff(padded)==1)+COL0
        ends=np.flatnonzero(np.diff(padded)==-1)+COL0
        next_active={}
        for l,r in zip(starts,ends):
            key=(int(l),int(r))
            next_active[key]=(active[key][0],int(row)+1) if key in active else (int(row),int(row)+1)
        for key, span in active.items():
            if key not in next_active: rects.append((*key,*span))
        active=next_active
    rects.extend((*key,*span) for key,span in active.items())
    return rects,int(safe.sum())


def conflict_int(r,s,S):
    xl,xr,yl,yr=r
    al,ar,bl,br=s
    dx=max(al-xr,xl-ar,0)
    dy=max(bl-yr,yl-br,0)
    DX=max(abs(xl-ar),abs(xr-al))
    DY=max(abs(yl-br),abs(yr-bl))
    L,U=dx*dx+dy*dy,DX*DX+DY*DY
    m0=math.isqrt(U//(S*S))
    E=S//512
    for m in (m0,m0+1):
        if m>=1 and L<=(m*S+E)**2 and U>=(m*S-E)**2: return True
    return False


def main():
    boxes,centers=load_sources()
    accepted=[]
    failures=0
    area=F(0)
    groups=[]
    total_pixels=total_runs=0
    for ds in product(range(3),repeat=2):
        X,Y=center(6,ds)
        lo,hi=tail_bounds(X,Y)
        runs,pixels=proposal(boxes,X,Y)
        total_pixels+=pixels
        total_runs+=len(runs)
        S=math.lcm(NX,NY,512,*(z.denominator for box in boxes for z in box))
        iboxes=[tuple(int(z*S) for z in b) for b in boxes]
        first=len(accepted)
        group_area=F(0)
        pending=[]
        for l,r,b,t in runs:
            box=(F(X)+F(l,NX),F(X)+F(r,NX),F(Y)+F(b,NY),F(Y)+F(t,NY))
            ibox=tuple(int(z*S) for z in box)
            if any(conflict_int(ibox,s,S) for s in iboxes):
                failures+=1
                continue
            assert lo-F(t,NY)>EPS and hi-F(b,NY)<1-EPS
            group_area+=F((r-l)*(t-b),NX*NY)
            accepted.append([str(z) for z in box])
            pending.append(box)
        # Each whole window has diameter<1-epsilon, so its candidates can
        # be added together; later windows check all preceding additions.
        boxes.extend(pending)
        area+=group_area
        group={"digits":list(ds),"center":[X,Y],"first_rectangle":first,
               "rectangle_count":len(pending),"area_fraction":str(group_area),
               "tail_phase_bounds":[str(lo),str(hi)]}
        groups.append(group)
        print(json.dumps(group),flush=True)
    data={"added_rectangles":accepted,"area_fraction":str(area),"area_decimal":float(area),
          "epsilon_against_preexisting_set":"1/512","source_set":"A_infinity_plus",
          "finite_prefix_last":13,"analytic_tail_first":14,"window_groups":groups,
          "candidate_window":["-2/5","2/5","1/256","1/8"],
          "window_squared_diameter":"16/25 + (31/256)^2",
          "window_diameter_less_than_one":True,"grid_denominators":[NX,NY],
          "finite_source_rectangles_including_base_enclosure":2703,
          "proposed_cells":total_pixels,"compressed_candidates":total_runs,
          "exact_rejected_rectangles":failures,
          "scope":"whole added rectangles; misses every old integer epsilon annulus and ALL future annuli",
          "new_set":"A_infinity_plus_plus = A_infinity_plus union these rectangles",
          "lean_formalized":False,"finite_optimum_proved":False}
    assert F(16,25)+F(31,256)**2<1
    path=HERE/f"erdos953-Ainfty-all-ring-hole-extension-{STAMP}.json"
    path.write_text(json.dumps(data,indent=2),encoding="utf-8")
    print(json.dumps({k:v for k,v in data.items() if k not in ("added_rectangles","tail_phase_bounds")}),flush=True)


if __name__=="__main__": main()
