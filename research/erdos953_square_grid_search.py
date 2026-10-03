"""Exact whole-square conflict graphs, nested chains, and continuous seeds.

S_ij=[i/N,(i+1)/N] x [j/N,(j+1)/N]. Conflict predicates, disk containment,
and output areas use integers. The search is heuristic; no optimum is claimed.
"""
from __future__ import annotations

import argparse
import gc
import json
import math
import time
from fractions import Fraction
from pathlib import Path
from types import SimpleNamespace

import numpy as np
from numba import njit, prange, set_num_threads
from scipy.spatial import cKDTree
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection

from erdos953_triangle_partition_search import weighted_greedy, weighted_local, weighted_patch_local

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
set_num_threads(8)


def labels_in_disk(R,N):
    R=Fraction(str(R))
    extent=math.ceil(R*N)
    return np.array([(i,j) for i in range(-extent,extent)
                     for j in range(-extent,extent)
                     if (max(i*i,(i+1)**2)+max(j*j,(j+1)**2))*R.denominator**2
                     < (N*R.numerator)**2],dtype=np.int32)


def conflict_python(a,b,N):
    u,v=abs(int(a[0])-int(b[0])),abs(int(a[1])-int(b[1]))
    lo=max(u-1,0)**2+max(v-1,0)**2
    hi=(u+1)**2+(v+1)**2
    k=math.isqrt(hi)//N
    return k>=1 and lo<=(k*N)**2


def make_mask(N,extent):
    mask=np.zeros((extent+1,extent+1),dtype=np.uint8)
    for u in range(extent+1):
        for v in range(extent+1):
            lo=max(u-1,0)**2+max(v-1,0)**2
            hi=(u+1)**2+(v+1)**2
            k=math.isqrt(hi)//N
            mask[u,v]=k>=1 and lo<=(k*N)**2
    assert mask[0,0]==0
    return mask


@njit(cache=True,parallel=True)
def graph_counts(labels,mask):
    n=len(labels)
    counts=np.zeros(n,dtype=np.int64)
    for ii in prange(n):
        i=np.int64(ii)
        count=0
        for j in range(n):
            count+=mask[abs(labels[i,0]-labels[j,0]),abs(labels[i,1]-labels[j,1])]
        counts[i]=count
    return counts


@njit(cache=True,parallel=True)
def graph_fill(labels,mask,pointer):
    n=len(labels)
    indices=np.empty(pointer[-1],dtype=np.int32)
    for ii in prange(n):
        i=np.int64(ii)
        pos=pointer[i]
        for j in range(n):
            if mask[abs(labels[i,0]-labels[j,0]),abs(labels[i,1]-labels[j,1])]:
                indices[pos]=j
                pos+=1
    return indices


def build_graph(labels,N):
    extent=int(np.ptp(labels,axis=0).max())
    mask=make_mask(N,extent)
    counts=graph_counts(labels,mask)
    pointer=np.r_[0,np.cumsum(counts)]
    indices=graph_fill(labels,mask,pointer)
    return SimpleNamespace(indptr=pointer,indices=indices)


@njit(cache=True,parallel=True)
def audit_integer_pairs(labels,N):
    violations=np.zeros(len(labels),dtype=np.int64)
    for ii in prange(len(labels)):
        i=np.int64(ii)
        for j in range(i+1,len(labels)):
            u=abs(labels[i,0]-labels[j,0])
            v=abs(labels[i,1]-labels[j,1])
            lo=max(u-1,0)**2+max(v-1,0)**2
            hi=(u+1)**2+(v+1)**2
            k=int(math.sqrt(hi))//N
            while ((k+1)*N)**2<=hi:
                k+=1
            while (k*N)**2>hi:
                k-=1
            if k>=1 and lo<=(k*N)**2:
                violations[i]+=1
    return violations.sum()


def audit_selection(labels,N,R):
    assert N>=2 and len({tuple(map(int,p)) for p in labels})==len(labels)
    r=Fraction(str(R))
    for i,j in labels:
        i,j=int(i),int(j)
        assert (max(i*i,(i+1)**2)+max(j*j,(j+1)**2))*r.denominator**2<(N*r.numerator)**2
    # This numerical kernel performs integer comparisons only; prove no overflow.
    extent=int(np.ptp(labels,axis=0).max()) if len(labels) else 0
    assert 2*(extent+1)**2<2**63
    assert audit_integer_pairs(labels.astype(np.int64),N)==0
    return len(labels)*(len(labels)-1)//2


@njit(cache=True)
def ball_witnesses(labels,N,balls,Q,common):
    # All calculations are exact after conversion to a common integer scale.
    cell_scale,ball_scale=common//N,common//Q
    result=np.full(len(labels),-1,dtype=np.int32)
    for c in range(len(balls)):
        cx,cy,rad=balls[c,0]*ball_scale,balls[c,1]*ball_scale,balls[c,2]*ball_scale
        left=(cx-rad)//cell_scale-1
        right=(cx+rad)//cell_scale+1
        bottom=(cy-rad)//cell_scale-1
        top=(cy+rad)//cell_scale+1
        for s in range(len(labels)):
            if result[s]>=0:
                continue
            i,j=labels[s,0],labels[s,1]
            if i<left or i>right or j<bottom or j>top:
                continue
            good=True
            for dx in range(2):
                for dy in range(2):
                    x,y=(i+dx)*cell_scale-cx,(j+dy)*cell_scale-cy
                    if x*x+y*y>=rad*rad:
                        good=False
            if good:
                result[s]=c
    return result


@njit(cache=True)
def polygon_witnesses(labels,N,polygons,lengths,Q,common):
    cell_scale,poly_scale=common//N,common//Q
    result=np.full(len(labels),-1,dtype=np.int32)
    for s in range(len(labels)):
        for p in range(len(polygons)):
            good=True
            for e in range(lengths[p]):
                a=polygons[p,e]*poly_scale
                b=polygons[p,(e+1)%lengths[p]]*poly_scale
                for dx in range(2):
                    for dy in range(2):
                        x,y=(labels[s,0]+dx)*cell_scale,(labels[s,1]+dy)*cell_scale
                        if (b[0]-a[0])*(y-a[1])-(b[1]-a[1])*(x-a[0])<=0:
                            good=False
                if not good:
                    break
            if good:
                result[s]=p
                break
    return result


def seed_witnesses(labels,N,R):
    if R==1:
        # A rational center gives an explicit two-lobe limit, within 1e-8 of
        # the previously derived optimal center in this restricted family.
        Q=100_000_000
        c=math.floor(((.5+math.sqrt(2.5))/3)*Q)
        balls=np.array([[c,0,Q//2],[-c,0,Q//2]],dtype=np.int64)
        result=ball_witnesses(labels,N,balls,Q,math.lcm(N,Q))
        # Entire cells must lie strictly outside |x|=1/2.
        result[(2*labels[:,0]<=N)&(2*(labels[:,0]+1)>=-N)]=-1
        return result,{"kind":"rational_two_lobes","Q":Q,"center":c,
                       "radius":"1/2","cutoff":"1/2"}
    if R==1.5:
        filename="erdos953-random-polygons-R1.5-N32000-eps0.008-seed95503.json"
        data=json.loads((HERE/filename).read_text())
        lengths=np.array([len(p) for p in data["polygons"]],dtype=np.int64)
        polygons=np.zeros((len(lengths),lengths.max(),2),dtype=np.int64)
        for i,p in enumerate(data["polygons"]):
            polygons[i,:len(p)]=p
        Q=data["coordinate_denominator"]
        result=polygon_witnesses(labels,N,polygons,lengths,Q,math.lcm(N,Q))
        return result,{"kind":"rational_convex_polygons","source":filename,
                       "limit_area":"20385620360334689/20000000000000000"}
    if R==2:
        filename="erdos953-random-ball-grid-R2-N32000-eps0.03-seed95506.json"
        data=json.loads((HERE/filename).read_text())
        Q=data["coordinate_denominator"]
        common=math.lcm(N,Q)
        assert 32*common*common<2**63
        result=ball_witnesses(labels,N,np.array(data["balls"],dtype=np.int64),Q,common)
        return result,{"kind":"rational_open_balls_clipped_to_disk","source":filename,
                       "known_lower_for_limit_area":"259783/250000"}
    # A radius <1/2 central ball for larger-R exploratory runs.
    result=np.full(len(labels),-1,dtype=np.int32)
    good=np.maximum(labels[:,0]**2,(labels[:,0]+1)**2)+np.maximum(labels[:,1]**2,(labels[:,1]+1)**2)
    result[4*good<N*N]=0
    return result,{"kind":"open_half_unit_disk","limit_area":"pi/4"}


def refine_mask(labels,N,previous):
    result=np.zeros(len(labels),dtype=np.bool_)
    if previous is None:
        return result
    assert N==2*previous["N"]
    parents={tuple(p) for p in previous["labels"]}
    result=np.array([(int(i)//2,int(j)//2) in parents for i,j in labels],dtype=np.bool_)
    assert result.sum()==4*len(parents)
    return result


def run_case(R,N,previous_free,previous_nested,sweeps,patches):
    started=time.perf_counter()
    labels=labels_in_disk(R,N)
    seed=953000+int(R*1000)+N
    rng=np.random.default_rng(seed)
    witnesses,source=seed_witnesses(labels,N,R)
    target=witnesses>=0
    inherited_free=refine_mask(labels,N,previous_free)
    inherited_nested=refine_mask(labels,N,previous_nested)
    graph=build_graph(labels,N)
    n=len(labels)
    weights=np.ones(n)
    degrees=np.diff(graph.indptr)
    xy=(labels+.5)/N
    starts=[("target",target),("parent",inherited_free)]
    for center in (np.zeros(2),xy[rng.integers(n)]):
        order=np.argsort(np.sum((xy-center)**2,axis=1))
        starts.append(("spatial",weighted_greedy(graph.indptr,graph.indices,order,np.zeros(n,dtype=np.bool_))))
    order=np.argsort(degrees+rng.exponential(max(1.,degrees.mean()*.2),n))
    starts.append(("degree",weighted_greedy(graph.indptr,graph.indices,order,np.zeros(n,dtype=np.bool_))))
    best=max(starts,key=lambda p:int(p[1].sum()))[1].copy()
    for trial,(name,initial) in enumerate(starts):
        if trial>=2 and initial.sum()<.8*best.sum():
            continue
        initial=weighted_greedy(graph.indptr,graph.indices,rng.permutation(n),initial)
        found=weighted_local(graph.indptr,graph.indices,weights,initial,seed+trial,sweeps)
        if found.sum()>best.sum():
            best=found
    if patches:
        radius=min(.14,(1-2*math.sqrt(2)/N)/3)
        assert 2*radius+2*math.sqrt(2)/N<1
        centers=xy[rng.integers(n,size=patches)]
        radii=rng.uniform(radius*.15,radius,size=patches)
        groups=cKDTree(xy).query_ball_point(centers,radii)
        pointer=np.r_[0,np.cumsum([len(g) for g in groups])]
        indices=np.array([v for g in groups for v in g],dtype=np.int32)
        found=weighted_patch_local(graph.indptr,graph.indices,weights,pointer,indices,best,seed+3000)
        if found.sum()>best.sum():
            best=found
    # This chain may only ADD cells. Refinement preserves its previous union.
    priority=np.r_[np.flatnonzero(best),np.flatnonzero(target & ~best),rng.permutation(np.flatnonzero(~(best|target)))]
    nested=weighted_greedy(graph.indptr,graph.indices,priority,inherited_nested)
    assert np.all(nested[inherited_nested])
    assert best.sum()>=inherited_free.sum() and best.sum()>=target.sum()
    certificates=[]
    for kind,chosen in (("free",best),("nested",nested),("target",target)):
        points=labels[chosen].tolist()
        certificate={"R":str(Fraction(str(R))),"N":N,"kind":kind,"squares":points,
                     "area_fraction":str(Fraction(len(points),N*N)),"source":source,
                     "region_policy":"closed squares strictly inside the open disk"}
        if kind=="target":
            certificate["source_witnesses"]=witnesses[chosen].tolist()
        filename=f"erdos953-square-grid-R{R:g}-N{N}-{kind}-{STAMP}.json"
        (HERE/filename).write_text(json.dumps(certificate,separators=(",",":")),encoding="utf-8")
        pairs=audit_selection(labels[chosen],N,R)
        certificates.append({"kind":kind,"count":len(points),"area_fraction":certificate["area_fraction"],
                             "area":len(points)/(N*N),"certificate":filename,"exact_pairs":pairs})
    result={"R":R,"N":N,"nodes":n,"edges":int(len(graph.indices)//2),
            "certificates":certificates,"seconds":time.perf_counter()-started,
            "finite_optimum_proved":False}
    next_free={"N":N,"labels":labels[best].tolist()}
    next_nested={"N":N,"labels":labels[nested].tolist()}
    del graph
    gc.collect()
    return result,next_free,next_nested


def fine_target(R,N):
    labels=labels_in_disk(R,N)
    witnesses,source=seed_witnesses(labels,N,R)
    chosen=witnesses>=0
    points=labels[chosen].tolist()
    certificate={"R":str(Fraction(str(R))),"N":N,"kind":"target","squares":points,
                 "source_witnesses":witnesses[chosen].tolist(),"source":source,
                 "area_fraction":str(Fraction(len(points),N*N)),
                 "region_policy":"closed squares strictly inside the open disk"}
    filename=f"erdos953-square-grid-R{R:g}-N{N}-target-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(certificate,separators=(",",":")),encoding="utf-8")
    return {"R":R,"N":N,"nodes":len(labels),"target_only":True,
            "certificates":[{"kind":"target","count":len(points),"area":len(points)/(N*N),
                             "area_fraction":certificate["area_fraction"],"certificate":filename}]}


def plot(results):
    fig,axes=plt.subplots(2,3,figsize=(14,8))
    for col,R in enumerate((1,1.5,2)):
        subset=[r for r in results if r["R"]==R]
        for kind,color in (("free","#147baf"),("nested","#d47d20"),("target","#438a65")):
            points=[(r["N"],next(c["area"] for c in r["certificates"] if c["kind"]==kind))
                    for r in subset if any(c["kind"]==kind for c in r["certificates"])]
            axes[0,col].plot(*zip(*points),"o-",color=color,label=kind)
        extension_path=HERE/f"erdos953-square-nested-extensions-{STAMP}.json"
        if R==2 and extension_path.exists():
            extensions=json.loads(extension_path.read_text())
            parent=next(c["area"] for r in subset if r["N"]==128 for c in r["certificates"] if c["kind"]=="free")
            axes[0,col].plot([128]+[e["N"] for e in extensions],
                             [parent]+[e["area"] for e in extensions],"o-",color="#8453b3",label="nested from best N128")
        axes[0,col].set_xscale("log",base=2)
        axes[0,col].set_title(f"R={R:g}: certified square areas")
        axes[0,col].set_xlabel("Grid denominator N")
        axes[0,col].set_ylabel("Area")
        axes[0,col].grid(alpha=.2)
        axes[0,col].legend()
        r=max((r for r in subset if not r.get("target_only")),key=lambda r:r["N"])
        c=next(c for c in r["certificates"] if c["kind"]=="free")
        data=json.loads((HERE/c["certificate"]).read_text())
        run_path=HERE/f"erdos953-square-runs-R2-N512-{STAMP}.json"
        if R==2 and run_path.exists():
            data=json.loads(run_path.read_text())
            N=data["coordinate_denominator"]
            corners=np.array([[[a,c],[b,c],[b,d],[a,d]] for a,b,c,d in data["rectangles"]])/N
            drawn_area=float(Fraction(data["area_fraction"]))
        else:
            N=r["N"]
            squares=np.array(data["squares"])
            corners=(squares[:,None,:]+np.array([[0,0],[1,0],[1,1],[0,1]])[None,:,:])/N
            drawn_area=c["area"]
        axes[1,col].add_collection(PolyCollection(corners,facecolors="#147baf",edgecolors="none"))
        axes[1,col].add_patch(plt.Circle((0,0),R,fill=False,color="black",lw=1))
        axes[1,col].set_xlim(-R*1.05,R*1.05)
        axes[1,col].set_ylim(-R*1.05,R*1.05)
        axes[1,col].set_aspect("equal")
        axes[1,col].set_title(f"N={N}, area={drawn_area:.6f}")
    fig.tight_layout()
    fig.savefig(HERE/f"erdos953-square-grid-search-{STAMP}.png",dpi=170)
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--max-N",type=int,default=64)
    parser.add_argument("--sweeps",type=int,default=40)
    parser.add_argument("--patches",type=int,default=600)
    parser.add_argument("--fine-target-N",type=int,default=256)
    parser.add_argument("--large-radii",action="store_true")
    args=parser.parse_args()
    results=[]
    destination=HERE/f"erdos953-square-grid-results-{STAMP}.json"
    radii=(1,1.5,2,4,8) if args.large_radii else (1,1.5,2)
    for R in radii:
        previous_free=previous_nested=None
        Ns=[N for N in (8,16,32,64,128) if N<=args.max_N and R*N<=128]
        if R>=4:
            Ns=[N for N in (4,8,16,32) if N<=args.max_N and R*N<=128]
        for N in Ns:
            result,previous_free,previous_nested=run_case(R,N,previous_free,previous_nested,args.sweeps,args.patches)
            results.append(result)
            destination.write_text(json.dumps(results,indent=2),encoding="utf-8")
            print(json.dumps(result),flush=True)
        if R<=2 and args.fine_target_N:
            for N in (128,256):
                if N>args.max_N and N<=args.fine_target_N:
                    result=fine_target(R,N)
                    results.append(result)
                    destination.write_text(json.dumps(results,indent=2),encoding="utf-8")
                    print(json.dumps(result),flush=True)
    plot(results)


if __name__=="__main__":
    main()
