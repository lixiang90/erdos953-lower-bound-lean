"""Enlarge the fixed unbounded construction using uncovered distance annuli.

LP proposes symmetric rectangle heights. Rational rounding and exact checks
certify the output; a separate verifier reconstructs the geometry. All later
blocks use width 1/3 and height 1/(36*k^3), proved safe by a sharper digit
estimate. The new base is a clipped open half-unit disk.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse
import json
import math
import time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

from erdos953_square_limit_construction import parameters,center,block_area

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
WIDTH=Fraction(1,3)
CAP=Fraction(1,256)
EPS=Fraction(1,64)
MULTIPLIER=Fraction(256,27)


def block_centers(j):
    k,n=parameters(j)
    return [center(j,digits) for digits in product(range(k-1),repeat=n)]


def hull(points):
    points=sorted(set(points))
    def cross(a,b,c):
        return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    lo,hi=[],[]
    for p in points:
        while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0: lo.pop()
        lo.append(p)
    for p in reversed(points):
        while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0: hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]


def make_base_certificate():
    Q=2**24
    cy=-9*Q//32
    radius=Q//2-2
    top,bottom=5*Q//32-1,-23*Q//32+1
    points=[]
    for t in np.linspace(0,2*math.pi,2048,endpoint=False):
        x=round(radius*math.cos(t))
        y=cy+round(radius*math.sin(t))
        if bottom<=y<=top: points.append((x,y))
    for y in (top,bottom):
        x=math.isqrt(radius*radius-(y-cy)**2)-1
        points.extend([(x,y),(-x,y)])
    polygon=hull(points)
    area2=sum(x*Y-y*X for (x,y),(X,Y) in zip(polygon,polygon[1:]+polygon[:1]))
    area=Fraction(area2,2*Q*Q)
    payload={"coordinate_denominator":Q,"vertices":polygon,"area_fraction":str(area),
             "enclosing_open_disk_center":["0","-9/32"],"enclosing_disk_radius":"1/2",
             "vertical_strip":["-23/32","5/32"],
             "exact_open_base_area":"7*sqrt(15)/128 + asin(7/8)/2",
             "role":"rational inner certificate for the enlarged base; boundary is strictly inside the base"}
    path=HERE/f"erdos953-Ainfty-ring-base-{STAMP}.json"
    path.write_text(json.dumps(payload,separators=(",",":")),encoding="utf-8")
    return {"certificate":path.name,"area_fraction":str(area),"area":float(area),
            "exact_area":7*math.sqrt(15)/128+math.asin(7/8)/2,"vertices":len(polygon)}


def solve_block(j):
    started=time.perf_counter()
    k,n=parameters(j)
    points=block_centers(j)
    xy=np.array(points,dtype=np.int64)
    count=len(points)
    base=Fraction(1,36*k**3)
    rows=[]
    for i in range(count):
        a=np.abs(xy[i+1:,1]-xy[i,1])
        b=np.abs(xy[i+1:,0]-xy[i,0])
        ids=np.flatnonzero(128*(3*b-1)**2<9*a)
        for z in ids:
            j2=i+1+int(z)
            rows.append((i,j2,int(a[z]),int(b[z])))
    # z_i = H_i/base - 1 keeps LP coefficients well scaled.
    upper=float(CAP/base-1)
    if rows:
        rr=np.repeat(np.arange(len(rows)),2)
        cc=np.array([(i,j) for i,j,a,b in rows],dtype=np.int32).ravel()
        matrix=coo_matrix((np.ones(len(rr)),(rr,cc)),shape=(len(rows),count)).tocsr()
        rhs=np.array([4*k**3*(3*b-1)**2/a-2 for i,j,a,b in rows])
        result=linprog(-np.ones(count),A_ub=matrix,b_ub=rhs,bounds=(0,upper),method="highs",
                       options={"primal_feasibility_tolerance":1e-9,"dual_feasibility_tolerance":1e-9})
        assert result.success,result.message
        values=result.x
        solver_message=result.message
    else:
        values=np.full(count,upper)
        solver_message="all capped heights satisfy the nonredundant constraints"
    Q=2**24
    D=36*k**3*Q
    units=[min(D//256,Q+max(0,math.floor(float(v)*Q))) for v in values]
    repaired=0
    for i,j2,a,b in rows:
        excess=9*a*(units[i]+units[j2])-D*(3*b-1)**2
        if excess>0:
            needed=(excess+9*a-1)//(9*a)
            take=min(needed,units[i]-Q)
            units[i]-=take
            needed-=take
            assert needed<=units[j2]-Q
            units[j2]-=needed
            repaired+=take+needed
    area=Fraction(sum(units),3*D)
    old=block_area(j)
    uniform=Fraction(count,108*k**3)
    filename=f"erdos953-Ainfty-ring-block-j{j}-{STAMP}.json"
    cert={"j":j,"k":k,"n":n,"width":"1/3","height_cap":"1/256",
          "height_denominator":D,"height_numerators":units,
          "ordering":"itertools.product(range(k-1), repeat=n), digit index zero is least significant",
          "area_fraction":str(area),"uniform_area_fraction":str(uniform),"old_area_fraction":str(old),
          "pair_constraint":"H_i+H_j <= (3*b-1)^2/(9*a); a=abs(dy), b=abs(dx)",
          "lp_nonredundant_constraints":len(rows),"solver_message":solver_message,
          "rational_repair_units":repaired,"finite_optimum_proved":False,"lean_formalized":False}
    (HERE/filename).write_text(json.dumps(cert,separators=(",",":")),encoding="utf-8")
    outcome={"j":j,"k":k,"n":n,"rectangles":count,"old_area":float(old),
             "uniform_area":float(uniform),"extended_area":float(area),"extended_area_fraction":str(area),
             "multiplier_over_old":float(area/old),"height_min":min(units)/D,"height_max":max(units)/D,
             "height_cap_count":sum(u==D//256 for u in units),"constraints":len(rows),
             "rational_repair_units":repaired,"certificate":filename,"seconds":time.perf_counter()-started}
    print(json.dumps(outcome),flush=True)
    return outcome


def unit_forbidden_area(width,height,epsilon):
    # Q + {1-epsilon <= |z| <= 1+epsilon}; farthest-corner hole is exact.
    w,h,e=map(float,(width,height,epsilon))
    rin,rout=1-e,1+e
    a,b=w/2,h/2
    assert a*a+b*b<rin*rin
    end=math.sqrt(rin*rin-b*b)
    def primitive(x):
        return (x*math.sqrt(max(0,rin*rin-x*x))+rin*rin*math.asin(x/rin))/2
    hole=4*(primitive(end)-primitive(a)-b*(end-a))
    outer=w*h+2*(w+h)*rout+math.pi*rout*rout
    return outer-hole


def unit_coverage(j):
    count=1
    area=unit_forbidden_area(Fraction(1,4),Fraction(1,512),EPS)
    for l in range(6,j+1):
        k,n=parameters(l)
        m=(k-1)**n
        count+=m
        area+=m*unit_forbidden_area(Fraction(1,4),Fraction(1,256*k**3),EPS)
    R=4**(j+1)
    # Exact area of each outer offset is <4, and pi>3.
    covered_fraction_upper=Fraction(4*count,3*R*R)
    return {"j":j,"R":str(R),"components":str(count),"epsilon":"1/64",
            "unit_band_area_approx":area,"covered_fraction_approx":area/(math.pi*R*R),
            "strict_covered_fraction_upper":str(covered_fraction_upper),
            "strict_uncovered_fraction_lower":str(1-covered_fraction_upper),
            "bands_disjoint":True,"all_future_unit_bands_outside_disk":True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--last-j",type=int,default=13)
    args=parser.parse_args()
    base=make_base_certificate()
    blocks=[]
    path=HERE/f"erdos953-Ainfty-ring-extension-results-{STAMP}.json"
    for j in range(6,args.last_j+1):
        blocks.append(solve_block(j))
        payload={"base":base,"blocks":blocks,"tail_rule":"for every j beyond the last computed block, H=1/(36*k_j^3), width=1/3",
                 "uniform_block_multiplier":str(MULTIPLIER),"uniform_lower_coefficient":"1/55296",
                 "unit_coverage":[unit_coverage(j) for j in [6,9,12,20,40]],
                 "infinite_set":"A_infinity_plus contains the original A_infinity; finite optimized prefix and analytically proved uniform tail",
                 "lean_formalized":False,"finite_optimum_proved":False}
        path.write_text(json.dumps(payload,indent=2),encoding="utf-8")


if __name__=="__main__":
    main()
