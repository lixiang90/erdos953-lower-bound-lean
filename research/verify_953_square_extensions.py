"""Exact incremental certificates, independent of FFT and search masks."""
from pathlib import Path
import json
import math
import numpy as np
from numba import njit,prange,set_num_threads
from shapely.geometry import Polygon

from verify_953_square_grid import check_basics

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
set_num_threads(8)


@njit(cache=True,inline="always")
def bad_pair(a,b,c,d,N):
    nearx=max(0,a-c-1,c-a-1)
    neary=max(0,b-d-1,d-b-1)
    farx=max(abs(a-c-1),abs(a-c+1))
    fary=max(abs(b-d-1),abs(b-d+1))
    lo,hi=nearx*nearx+neary*neary,farx*farx+fary*fary
    for k in range(1,5):
        if lo<=(k*N)**2<=hi:
            return 1
    return 0


@njit(cache=True,parallel=True)
def check_added(old,new,N):
    bad=np.zeros(len(new),dtype=np.int64)
    for ii in prange(len(new)):
        i=np.int64(ii)
        a,b=new[i,0],new[i,1]
        for j in range(len(old)):
            bad[i]+=bad_pair(a,b,old[j,0],old[j,1],N)
        for j in range(i+1,len(new)):
            bad[i]+=bad_pair(a,b,new[j,0],new[j,1],N)
    return bad.sum()


def main():
    initial=json.loads((HERE/f"erdos953-square-grid-independent-audit-{STAMP}.json").read_text())
    assert initial["all_passed"]
    verified={r["file"] for r in initial["results"]}
    results=[]
    for item in json.loads((HERE/f"erdos953-square-nested-extensions-{STAMP}.json").read_text()):
        d=json.loads((HERE/item["certificate"]).read_text())
        assert d["parent_certificate"] in verified
        parent=json.loads((HERE/d["parent_certificate"]).read_text())
        R,N,area=check_basics(d)
        assert R==2 and N==2*parent["N"] and d["refinement_factor"]==2
        old={(2*a+dx,2*b+dy) for a,b in parent["squares"] for dx in (0,1) for dy in (0,1)}
        new=set(map(tuple,d["added_squares"]))
        assert len(new)==len(d["added_squares"]) and not old&new
        assert old|new==set(map(tuple,d["squares"]))
        assert 8*(4*N+2)**2<2**63
        assert check_added(np.array(sorted(old),dtype=np.int64),np.array(sorted(new),dtype=np.int64),N)==0
        pairs=len(old)*len(new)+len(new)*(len(new)-1)//2
        result={"certificate":item["certificate"],"refined_parent_squares":len(old),
                "added_squares":len(new),"exact_new_pairs_checked":pairs,
                "area_fraction":str(area),"passed":True}
        results.append(result)
        verified.add(item["certificate"])
        print(json.dumps(result),flush=True)
    # A separate geometry sanity check, including closed-boundary equality.
    assert bad_pair(0,0,4,0,4)==1
    assert bad_pair(0,0,5,0,4)==1
    assert bad_pair(0,0,1,0,4)==0
    rng=np.random.default_rng(953128)
    max_error=0.
    for _ in range(1000):
        a,b,c,d=map(int,rng.integers(-100,101,size=4))
        lo=max(0,a-c-1,c-a-1)**2+max(0,b-d-1,d-b-1)**2
        pa=Polygon([(a,b),(a+1,b),(a+1,b+1),(a,b+1)])
        pb=Polygon([(c,d),(c+1,d),(c+1,d+1),(c,d+1)])
        error=abs(pa.distance(pb)**2-lo)
        max_error=max(error,max_error)
        assert error<1e-9
    output={"all_passed":True,"extension_certificates":len(results),
            "exact_incremental_pairs":sum(r["exact_new_pairs_checked"] for r in results),
            "independent_geometry_comparisons":1000,"maximum_squared_distance_error":max_error,
            "fft_used_for_verification":False,"results":results}
    (HERE/f"erdos953-square-extension-independent-audit-{STAMP}.json").write_text(json.dumps(output,indent=2),encoding="utf-8")
    print(json.dumps({k:v for k,v in output.items() if k!="results"}))


if __name__=="__main__":
    main()
