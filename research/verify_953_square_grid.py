"""Independent exact square certificates; does not import the search program."""
from __future__ import annotations

from fractions import Fraction
from pathlib import Path
import json
import math

import numpy as np
from numba import njit, prange, set_num_threads

from verify_953_random_balls import verify_balls
from verify_953_random_polygons import verify_certificate as verify_polygons

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
set_num_threads(8)


@njit(cache=True,parallel=True)
def all_integer_distance_checks(cells,N,kmax):
    bad=np.zeros(len(cells),dtype=np.int64)
    for ii in prange(len(cells)):
        i=np.int64(ii)
        for j in range(i+1,len(cells)):
            a,b=cells[i,0],cells[i,1]
            c,d=cells[j,0],cells[j,1]
            nearx=max(0,a-c-1,c-a-1)
            neary=max(0,b-d-1,d-b-1)
            farx=max(abs(a-c-1),abs(a-c+1))
            fary=max(abs(b-d-1),abs(b-d+1))
            minimum=nearx*nearx+neary*neary
            maximum=farx*farx+fary*fary
            for k in range(1,kmax+1):
                target=(k*N)**2
                if minimum<=target<=maximum:
                    bad[i]+=1
    return bad.sum()


def check_basics(data):
    R,N=Fraction(data["R"]),data["N"]
    cells=data["squares"]
    assert isinstance(N,int) and N>=2
    assert len(cells)==len(set(map(tuple,cells)))
    for a,b in cells:
        assert isinstance(a,int) and isinstance(b,int)
        for x in (a,a+1):
            for y in (b,b+1):
                assert (x*x+y*y)*R.denominator**2<(N*R.numerator)**2
    area=Fraction(len(cells),N*N)
    assert area==Fraction(data["area_fraction"])
    return R,N,area


def check_target_witnesses(data,source_cache):
    R,N,area=check_basics(data)
    source=data["source"]
    kind=source["kind"]
    if kind=="rational_two_lobes":
        Q=source["Q"]
        assert R==1 and source["cutoff"]=="1/2" and source["radius"]=="1/2"
        balls=[[source["center"],0,Q//2],[-source["center"],0,Q//2]]
        polygons=None
    else:
        path=source["source"]
        original=json.loads((HERE/path).read_text())
        Q=original["coordinate_denominator"]
        if path not in source_cache:
            if kind=="rational_convex_polygons":
                result=verify_polygons(original)
                result.pop("area_fraction_value")
            else:
                result=verify_balls(original)
            source_cache[path]=result
        balls=original.get("balls")
        polygons=original.get("polygons")
    common=math.lcm(N,Q)
    cs,ss=common//N,common//Q
    assert len(data["source_witnesses"])==len(data["squares"])
    for (a,b),witness in zip(data["squares"],data["source_witnesses"]):
        if balls is not None:
            assert 0<=witness<len(balls)
            cx,cy,r=balls[witness]
            cx,cy,r=cx*ss,cy*ss,r*ss
            for x in (a,a+1):
                for y in (b,b+1):
                    assert (x*cs-cx)**2+(y*cs-cy)**2<r*r
            if kind=="rational_two_lobes":
                assert (witness==0 and 2*a>N) or (witness==1 and 2*(a+1)<-N)
        else:
            assert 0<=witness<len(polygons)
            polygon=polygons[witness]
            for p,q in zip(polygon,polygon[1:]+polygon[:1]):
                px,py=p[0]*ss,p[1]*ss
                qx,qy=q[0]*ss,q[1]*ss
                for x in (a,a+1):
                    for y in (b,b+1):
                        assert (qx-px)*(y*cs-py)-(qy-py)*(x*cs-px)>0
    return len(data["squares"])


def main():
    manifest=json.loads((HERE/f"erdos953-square-grid-results-{STAMP}.json").read_text())
    files={c["certificate"] for r in manifest for c in r["certificates"]}
    source_cache={}
    audit=[]
    total_pairs=0
    target_witnesses=0
    chains={}
    for filename in sorted(files):
        data=json.loads((HERE/filename).read_text())
        R,N,area=check_basics(data)
        if data["kind"]=="target" and R in (1,Fraction(3,2),2):
            count=check_target_witnesses(data,source_cache)
            target_witnesses+=count
            method="exact source geometry and source certificate"
            pairs=0
        else:
            cells=np.array(data["squares"],dtype=np.int64)
            extent=int(np.ptp(cells,axis=0).max())
            kmax=math.ceil(2*R)
            assert max(2*(extent+1)**2,(kmax*N)**2)<2**63
            assert all_integer_distance_checks(cells,N,kmax)==0
            pairs=len(cells)*(len(cells)-1)//2
            total_pairs+=pairs
            method="every integer in every pair interval, bounded exact int64"
        audit.append({"file":filename,"count":len(data["squares"]),"area_fraction":str(area),
                      "pair_checks":pairs,"method":method})
        if data["kind"] in ("nested","target"):
            chains.setdefault((str(R),data["kind"]),[]).append(data)
        print(json.dumps(audit[-1]),flush=True)
    inclusions=0
    for key,chain in chains.items():
        chain.sort(key=lambda d:d["N"])
        for a,b in zip(chain,chain[1:]):
            assert b["N"]==2*a["N"]
            children={(2*x+dx,2*y+dy) for x,y in a["squares"] for dx in (0,1) for dy in (0,1)}
            assert children<=set(map(tuple,b["squares"]))
            assert Fraction(a["area_fraction"])<=Fraction(b["area_fraction"])
            inclusions+=1
    output={"certificates":len(audit),"exact_square_pair_checks":total_pairs,
            "exact_target_witnesses":target_witnesses,"nested_inclusions":inclusions,
            "source_certificates":source_cache,"all_passed":True,"results":audit}
    (HERE/f"erdos953-square-grid-independent-audit-{STAMP}.json").write_text(json.dumps(output,indent=2),encoding="utf-8")
    print(json.dumps({k:v for k,v in output.items() if k not in ("results","source_certificates")}))


if __name__=="__main__":
    main()
