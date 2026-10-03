"""Refine a certified square union and only add compatible squares.

FFT proposes unblocked cells. Each proposed addition is rechecked against
every selected square using an exact integer mask. FFT is not part of the
certificate or proof. A separate incremental verifier checks new-vs-all pairs.
"""
from __future__ import annotations
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np
from numba import njit
from scipy.signal import fftconvolve
from scipy.spatial import cKDTree

from erdos953_square_grid_search import HERE,STAMP,labels_in_disk,make_mask,seed_witnesses


@njit(cache=True)
def grow(labels,lookup,mask,offsets,blocked,initial,order,origin):
    n=len(labels)
    chosen=initial.copy()
    selected=np.empty(n,dtype=np.int32)
    count=0
    for i in range(n):
        if chosen[i]:
            selected[count]=i
            count+=1
    rejections=0
    for i in order:
        if chosen[i] or blocked[i]!=0:
            continue
        safe=True
        for position in range(count):
            j=selected[position]
            if mask[abs(labels[i,0]-labels[j,0]),abs(labels[i,1]-labels[j,1])]:
                safe=False
                break
        if not safe:
            rejections+=1
            continue
        chosen[i]=True
        selected[count]=i
        count+=1
        a,b=labels[i,0]+origin,labels[i,1]+origin
        for t in range(len(offsets)):
            x,y=a+offsets[t,0],b+offsets[t,1]
            if 0<=x<lookup.shape[0] and 0<=y<lookup.shape[1]:
                neighbor=lookup[x,y]
                if neighbor>=0:
                    blocked[neighbor]+=1
    return chosen,rejections


def extend(parentfile,N):
    data=json.loads((HERE/parentfile).read_text())
    assert Fraction(data["R"])==2 and N==2*data["N"]
    labels=labels_in_disk(2,N)
    parents=set(map(tuple,data["squares"]))
    initial=np.array([(int(a)//2,int(b)//2) in parents for a,b in labels],dtype=np.bool_)
    assert initial.sum()==4*len(parents)
    origin=2*N
    lookup=np.full((4*N,4*N),-1,dtype=np.int32)
    lookup[labels[:,0]+origin,labels[:,1]+origin]=np.arange(len(labels))
    extent=int(np.ptp(labels,axis=0).max())
    mask=make_mask(N,extent)
    offsets=np.arange(-extent,extent+1,dtype=np.int32)
    kernel=mask[np.abs(offsets)[:,None],np.abs(offsets)[None,:]]
    distances=np.maximum(np.abs(offsets)-1,0)
    kernel=kernel & (distances[:,None]**2+distances[None,:]**2<=(4*N)**2)
    occupied=np.zeros(lookup.shape,dtype=np.float64)
    occupied[labels[initial,0]+origin,labels[initial,1]+origin]=1
    values=fftconvolve(occupied,kernel.astype(np.float64),mode="same")
    rounded=np.rint(values)
    max_rounding_error=float(np.abs(values-rounded).max())
    assert max_rounding_error<1e-6
    blocked=rounded[labels[:,0]+origin,labels[:,1]+origin].astype(np.int32)
    assert np.all(blocked[initial]==0)
    candidates=np.flatnonzero((blocked==0)&~initial)
    offsets2=(np.argwhere(kernel)-extent).astype(np.int32)
    nearest=cKDTree(labels[initial]).query(labels[candidates],workers=8)[0]
    witnesses,_=seed_witnesses(labels,N,2)
    rng=np.random.default_rng(953256+N)
    orders=[candidates[np.argsort(nearest+rng.random(len(candidates))*.1)],
            candidates[np.argsort((witnesses[candidates]<0)*100+nearest)],
            rng.permutation(candidates)]
    best=initial.copy()
    outcomes=[]
    for order in orders:
        found,rejections=grow(labels,lookup,mask,offsets2,blocked.copy(),initial,order,origin)
        outcomes.append({"count":int(found.sum()),"exact_rejections_after_fft":int(rejections)})
        if found.sum()>best.sum():
            best=found
    assert np.all(best[initial])
    added=labels[best & ~initial]
    area=Fraction(int(best.sum()),N*N)
    filename=f"erdos953-square-grid-R2-N{N}-nested-extension-{STAMP}.json"
    certificate={"R":"2","N":N,"kind":"nested_extension","squares":labels[best].tolist(),
                 "area_fraction":str(area),"parent_certificate":parentfile,"refinement_factor":2,
                 "added_squares":added.tolist(),"region_policy":"closed squares strictly inside the open disk"}
    (HERE/filename).write_text(json.dumps(certificate,separators=(",",":")),encoding="utf-8")
    result={"N":N,"nodes":len(labels),"parent":parentfile,"initial_count":int(initial.sum()),
            "added_count":len(added),"count":int(best.sum()),"area_fraction":str(area),"area":float(area),
            "initial_unblocked_candidates":len(candidates),"fft_max_rounding_error":max_rounding_error,
            "outcomes":outcomes,"certificate":filename,"finite_optimum_proved":False}
    print(json.dumps(result),flush=True)
    return result


def main():
    parent=f"erdos953-square-grid-R2-N128-free-{STAMP}.json"
    results=[]
    for N in (256,512):
        result=extend(parent,N)
        results.append(result)
        parent=result["certificate"]
        (HERE/f"erdos953-square-nested-extensions-{STAMP}.json").write_text(json.dumps(results,indent=2),encoding="utf-8")


if __name__=="__main__":
    main()
