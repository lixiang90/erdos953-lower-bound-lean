"""Whole-cell searches on octagon/square and regular hexagon tilings.

Conflict masks use integer geometry of Minkowski differences. Floating-point
coordinates, Shapely seeds and FFT counts only propose search moves. Saved
selections are checked against the integer masks; a separate verifier uses
vertex-to-segment distances instead of Minkowski differences.
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
from scipy.signal import fftconvolve
from scipy.spatial import cKDTree
import shapely
from shapely.geometry import Polygon, Point, box
from shapely.ops import unary_union

from erdos953_triangle_partition_search import weighted_greedy, weighted_local, weighted_patch_local

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"
set_num_threads(8)


def convex_hull(points):
    points = sorted(set(map(tuple, points)))
    def cross(a, b, c):
        return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    lo, hi = [], []
    for p in points:
        while len(lo)>1 and cross(lo[-2],lo[-1],p)<=0:
            lo.pop()
        lo.append(p)
    for p in reversed(points):
        while len(hi)>1 and cross(hi[-2],hi[-1],p)<=0:
            hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]


def make_tiling(family, N):
    if family=="square":
        polygons=[np.array([(0,0),(1,0),(1,1),(0,1)],dtype=np.int64)]
        shift=np.array([[1,0],[0,1]],dtype=np.int64)
        areas=np.array([1],dtype=np.int64)
        scale,metric,minimum_scale=N,0,2
        parameters={"square_side":"1/"+str(N),"coordinate_denominator":N,"full_tiling":True}
    elif family in ("oct", "regular-oct"):
        # For the exact regular tiling, use outward rational envelopes:
        # octagon cut 0.292 <= 1-1/sqrt(2) <= square cut 0.293.
        # Avoiding distances on the envelopes proves the full ideal cells safe.
        d, a, b = (10,3,3) if family=="oct" else (1000,292,293)
        polygons = [np.array([(a,0),(d-a,0),(d,a),(d,d-a),
                              (d-a,d),(a,d),(0,d-a),(0,a)],dtype=np.int64),
                    np.array([(0,-b),(b,0),(0,b),(-b,0)],dtype=np.int64)]
        shift = np.array([[d,0],[0,d]],dtype=np.int64)
        areas = np.array([d*d-2*a*a,2*b*b],dtype=np.int64)
        if family=="regular-oct":
            areas=np.array([828427125,171572875],dtype=np.int64)
        scale, metric, minimum_scale = d*N, 0, 2
        parameters = {"parent_square_side":"1/"+str(N),"coordinate_denominator":scale,
                      "cut_octagon":str(Fraction(a,d)),"cut_square":str(Fraction(b,d)),
                      "full_tiling":True}
        if family=="regular-oct":
            parameters.update({"ideal_cut":"1-1/sqrt(2)","rational_polygons":"outward envelopes only",
                               "true_cell_areas":"(2sqrt(2)-2)/N^2; (3-2sqrt(2))/N^2"})
    else:
        assert family=="hex"
        q = max(4,round(math.sqrt(3*math.sqrt(3)/2)*N))
        polygons = [np.array([(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)],dtype=np.int64)]
        shift = np.array([[2,-1],[1,1]],dtype=np.int64)
        areas = np.array([3],dtype=np.int64)  # actual area = 3 sqrt(3)/(2 q^2)
        scale, metric, minimum_scale = q, 1, 16
        parameters = {"q":q,"hexagon_side":"1/"+str(q),
                      "axial_coordinates":"(a+b/2,sqrt(3)*b/2)/q","full_tiling":True}
    nv = np.array([len(p) for p in polygons],dtype=np.int64)
    vertices = np.zeros((len(polygons),max(nv),2),dtype=np.int64)
    for t,p in enumerate(polygons):
        vertices[t,:len(p)] = p
    differences = [[convex_hull([tuple(map(int,x-y)) for x in p for y in z])
                    for z in polygons] for p in polygons]
    nd = np.array([[len(p) for p in row] for row in differences],dtype=np.int64)
    hulls = np.zeros((len(polygons),len(polygons),int(nd.max()),2),dtype=np.int64)
    for t,row in enumerate(differences):
        for u,p in enumerate(row):
            hulls[t,u,:len(p)] = p
    return SimpleNamespace(family=family,N=N,vertices=vertices,nv=nv,shift=shift,
        scale=scale,metric=metric,minimum_scale=minimum_scale,areas=areas,
        hulls=hulls,nd=nd,parameters=parameters)


@njit(cache=True)
def norm(x,y,metric):
    return x*x+y*y+(x*y if metric else 0)


@njit(cache=True)
def hull_interval(hull,nv,dx,dy,metric):
    """Return (2 min distance squared, max) or (16 min, max)."""
    hi, lo, inside = np.int64(0),np.int64(2**62),True
    for e in range(nv):
        x,y=hull[e,0]+dx,hull[e,1]+dy
        xx,yy=hull[(e+1)%nv,0]+dx,hull[(e+1)%nv,1]+dy
        vx,vy=xx-x,yy-y
        hi=max(hi,norm(x,y,metric))
        if vx*(-y)-vy*(-x)<0:
            inside=False
        if metric:
            length=norm(vx,vy,1)
            dot2=-2*x*vx-x*vy-y*vx-2*y*vy
            if dot2<=0:
                value=16*norm(x,y,1)
            elif dot2>=2*length:
                value=16*norm(xx,yy,1)
            else:
                # Hexagon difference is twice a hexagon, edge norm = 4.
                assert length==4
                value=16*norm(x,y,1)-dot2*dot2
        else:
            length=vx*vx+vy*vy
            dot=-x*vx-y*vy
            if dot<=0:
                value=2*(x*x+y*y)
            elif dot>=length:
                value=2*(xx*xx+yy*yy)
            elif vx==0:
                value=2*x*x
            elif vy==0:
                value=2*y*y
            else:
                assert abs(vx)==abs(vy)
                value=(x-y if vx==vy else x+y)**2
        lo=min(lo,value)
    return (0 if inside else lo),hi


@njit(cache=True,parallel=True)
def make_conflict_mask(hulls,nd,shift,metric,minimum_scale,scale,extent):
    nt=len(nd)
    width=2*extent+1
    mask=np.zeros((nt,nt,width,width),dtype=np.uint8)
    for ii in prange(nt*nt*width*width):
        z=np.int64(ii)
        j=z%width-extent
        i=(z//width)%width-extent
        u=(z//(width*width))%nt
        t=z//(width*width*nt)
        dx=i*shift[0,0]+j*shift[1,0]
        dy=i*shift[0,1]+j*shift[1,1]
        lo,hi=hull_interval(hulls[t,u],nd[t,u],-dx,-dy,metric)
        root=int(math.sqrt(hi))
        while (root+1)**2<=hi:
            root+=1
        while root*root>hi:
            root-=1
        k=root//scale
        if k>=1 and lo<=minimum_scale*(k*scale)**2:
            mask[t,u,i+extent,j+extent]=1
    return mask


def labels_in_disk(R,tiling):
    r=Fraction(str(R))
    ext=math.ceil(float(r)*tiling.N)+2 if not tiling.metric else math.ceil(2*float(r)*tiling.scale/3)+2
    a,b=np.meshgrid(np.arange(-ext,ext+1),np.arange(-ext,ext+1),indexing="ij")
    labels=[]
    for t,nv in enumerate(tiling.nv):
        good=np.ones(a.shape,dtype=bool)
        for v in tiling.vertices[t,:nv]:
            x=a*tiling.shift[0,0]+b*tiling.shift[1,0]+v[0]
            y=a*tiling.shift[0,1]+b*tiling.shift[1,1]+v[1]
            squared=x*x+y*y+(x*y if tiling.metric else 0)
            good &= squared*r.denominator**2 < (r.numerator*tiling.scale)**2
        labels.extend(zip(a[good].tolist(),b[good].tolist(),[t]*int(good.sum())))
    return np.array(labels,dtype=np.int32)


def planar_vertices(labels,tiling):
    result=np.zeros((len(labels),int(tiling.nv.max()),2))
    center=labels[:,:2]@tiling.shift
    for t,nv in enumerate(tiling.nv):
        ids=np.flatnonzero(labels[:,2]==t)
        v=center[ids,None,:]+tiling.vertices[t,:nv][None,:,:]
        result[ids,:nv,0]=(v[:,:,0]+v[:,:,1]/2)/tiling.scale if tiling.metric else v[:,:,0]/tiling.scale
        result[ids,:nv,1]=v[:,:,1]*(math.sqrt(3)/2 if tiling.metric else 1)/tiling.scale
        if nv<result.shape[1]:
            result[ids,nv:]=result[ids,nv-1,None,:]
    return result


def pack_stencil(mask,extent):
    rows=[]
    pointer=[0]
    for t in range(len(mask)):
        for u in range(len(mask)):
            offsets=np.argwhere(mask[t,u]).astype(np.int32)-extent
            rows.extend((int(i),int(j),u) for i,j in offsets)
        pointer.append(len(rows))
    return np.array(pointer,dtype=np.int64),np.array(rows,dtype=np.int32)


def make_lookup(labels,nt):
    origin=-labels[:,:2].min(axis=0)
    shape=labels[:,:2].max(axis=0)+origin+1
    lookup=np.full((nt,int(shape[0]),int(shape[1])),-1,dtype=np.int32)
    lookup[labels[:,2],labels[:,0]+origin[0],labels[:,1]+origin[1]]=np.arange(len(labels))
    return lookup,origin


@njit(cache=True,parallel=True)
def stencil_counts(labels,lookup,origin,sptr,offsets):
    counts=np.zeros(len(labels),dtype=np.int64)
    for ii in prange(len(labels)):
        i=np.int64(ii)
        a,b,t=labels[i]
        a+=origin[0]; b+=origin[1]
        for z in range(sptr[t],sptr[t+1]):
            x,y,u=a+offsets[z,0],b+offsets[z,1],offsets[z,2]
            if 0<=x<lookup.shape[1] and 0<=y<lookup.shape[2] and lookup[u,x,y]>=0:
                counts[i]+=1
    return counts


@njit(cache=True,parallel=True)
def stencil_fill(labels,lookup,origin,sptr,offsets,pointer):
    indices=np.empty(pointer[-1],dtype=np.int32)
    for ii in prange(len(labels)):
        i=np.int64(ii)
        a,b,t=labels[i]
        a+=origin[0]; b+=origin[1]
        pos=pointer[i]
        for z in range(sptr[t],sptr[t+1]):
            x,y,u=a+offsets[z,0],b+offsets[z,1],offsets[z,2]
            if 0<=x<lookup.shape[1] and 0<=y<lookup.shape[2]:
                j=lookup[u,x,y]
                if j>=0:
                    indices[pos]=j; pos+=1
    return indices


@njit(cache=True,parallel=True)
def mask_pair_violations(labels,mask,extent):
    bad=np.zeros(len(labels),dtype=np.int64)
    for ii in prange(len(labels)):
        i=np.int64(ii)
        for j in range(i+1,len(labels)):
            a,b=labels[j,0]-labels[i,0]+extent,labels[j,1]-labels[i,1]+extent
            bad[i]+=mask[labels[i,2],labels[j,2],a,b]
    return bad.sum()


def baseline_file(R):
    return {1:"erdos953-square-grid-R1-N128-free-2026-10-03.json",
        1.5:"erdos953-random-polygons-R1.5-N32000-eps0.008-seed95503.json",
        2:"erdos953-square-runs-R2-N512-2026-10-03.json",
        4:"erdos953-square-grid-R4-N32-free-2026-10-03.json",
        8:"erdos953-square-grid-R8-N16-free-2026-10-03.json"}[float(R)]


def certificate_geometry(path):
    data=json.loads(Path(path).read_text())
    if "family" in data:
        tiling=make_tiling(data["family"],data["N"])
        labels=np.array(data["cells"],dtype=np.int32)
        vertices=planar_vertices(labels,tiling)
        return unary_union([Polygon(v[:tiling.nv[int(t)]]) for v,t in zip(vertices,labels[:,2])])
    if "rectangles" in data:
        q=data["coordinate_denominator"]
        return unary_union([box(a/q,c/q,b/q,d/q) for a,b,c,d in data["rectangles"]])
    if "polygons" in data:
        q=data["coordinate_denominator"]
        return unary_union([Polygon(np.array(p)/q) for p in data["polygons"]])
    if "squares" in data:
        q=data["N"]
        return unary_union([box(a/q,b/q,(a+1)/q,(b+1)/q) for a,b in data["squares"]])
    raise ValueError(path)


def seed_proposals(vertices,labels,tiling,R,parent=None):
    sources=[(baseline_file(R),certificate_geometry(HERE/baseline_file(R)))]
    if float(R)==1:
        c=(.5+math.sqrt(2.5))/3
        disk=Point(0,0).buffer(1,quad_segs=256)
        lobes=(Point(c,0).buffer(.5,quad_segs=256).intersection(box(.5,-2,2,2))
               .union(Point(-c,0).buffer(.5,quad_segs=256).intersection(box(-2,-2,-.5,2))))
        sources.append(("two_lobe_analytic_seed",disk.intersection(lobes)))
    if parent:
        sources.append((Path(parent).name,certificate_geometry(parent)))
    cells=shapely.polygons(vertices)
    return [(name,shapely.covers(geometry,cells)) for name,geometry in sources]


@njit(cache=True)
def compatible_seed_subset(labels,mask,extent,order):
    chosen=np.zeros(len(labels),dtype=np.bool_)
    selected=np.empty(len(order),dtype=np.int32)
    count=0
    for v in order:
        safe=True
        for z in range(count):
            u=selected[z]
            if mask[labels[v,2],labels[u,2],labels[u,0]-labels[v,0]+extent,labels[u,1]-labels[v,1]+extent]:
                safe=False; break
        if safe:
            chosen[v]=True
            selected[count]=v; count+=1
    return chosen


@njit(cache=True)
def grow_implicit(labels,lookup,origin,mask,extent,sptr,offsets,blocked,initial,order):
    chosen=initial.copy()
    selected=np.empty(len(labels),dtype=np.int32)
    count=0
    for v in range(len(labels)):
        if chosen[v]:
            selected[count]=v; count+=1
    rejected=0
    for v in order:
        if chosen[v] or blocked[v]!=0:
            continue
        # FFT is only a proposal. Every addition is checked exactly.
        safe=True
        for z in range(count):
            u=selected[z]
            if mask[labels[v,2],labels[u,2],labels[u,0]-labels[v,0]+extent,labels[u,1]-labels[v,1]+extent]:
                safe=False; break
        if not safe:
            rejected+=1; continue
        chosen[v]=True
        selected[count]=v; count+=1
        a,b,t=labels[v]
        a+=origin[0]; b+=origin[1]
        for z in range(sptr[t],sptr[t+1]):
            x,y,u=a+offsets[z,0],b+offsets[z,1],offsets[z,2]
            if 0<=x<lookup.shape[1] and 0<=y<lookup.shape[2]:
                neighbor=lookup[u,x,y]
                if neighbor>=0:
                    blocked[neighbor]+=1
    return chosen,rejected


def implicit_extend(labels,mask,extent,lookup,origin,sptr,offsets,initial,xy,weights,seed):
    initial_violations=int(mask_pair_violations(labels[initial],mask,extent))
    if initial_violations:
        proposed=np.flatnonzero(initial)
        order=proposed[np.argsort(-weights[proposed],kind="stable")]
        initial=compatible_seed_subset(labels,mask,extent,order)
        assert mask_pair_violations(labels[initial],mask,extent)==0
    occupied=np.zeros(lookup.shape)
    occupied[labels[initial,2],labels[initial,0]+origin[0],labels[initial,1]+origin[1]]=1
    blocked=np.zeros(len(labels),dtype=np.int32)
    error=0.
    for t in range(len(mask)):
        values=sum(fftconvolve(occupied[u],mask[t,u,::-1,::-1].astype(float),mode="same") for u in range(len(mask)))
        rounded=np.rint(values)
        error=max(error,float(np.abs(values-rounded).max()))
        ids=np.flatnonzero(labels[:,2]==t)
        blocked[ids]=rounded[labels[ids,0]+origin[0],labels[ids,1]+origin[1]].astype(np.int32)
    assert error<1e-5 and np.all(blocked[initial]==0)
    candidates=np.flatnonzero((blocked==0)&~initial)
    rng=np.random.default_rng(seed)
    nearest=cKDTree(xy[initial]).query(xy[candidates],workers=8)[0] if len(candidates) else np.array([])
    orders=[candidates[np.argsort(nearest+rng.random(len(candidates))/max(1,math.sqrt(len(labels))))],
            candidates[np.argsort(-weights[candidates]+rng.random(len(candidates))*.03)],rng.permutation(candidates)]
    best=initial.copy()
    outcomes=[]
    for order in orders:
        found,rejected=grow_implicit(labels,lookup,origin,mask,extent,sptr,offsets,blocked.copy(),initial,order)
        outcomes.append({"area_units":int(weights@found),"rejected_after_fft":int(rejected)})
        if weights@found>weights@best:
            best=found
    return best,{"seed_conflicts_removed":initial_violations,"certified_seed_area_units":int(weights@initial),
                "fft_rounding_error":error,"unblocked_candidates":len(candidates),"outcomes":outcomes}


def run_case(family,R,N,sweeps=35,patches=350,mode="coarse",parent=None):
    started=time.perf_counter()
    tiling=make_tiling(family,N)
    labels=labels_in_disk(R,tiling)
    extent=int(np.ptp(labels[:,:2],axis=0).max())
    mask=make_conflict_mask(tiling.hulls,tiling.nd,tiling.shift,tiling.metric,
                            tiling.minimum_scale,tiling.scale,extent)
    assert not any(mask[t,t,extent,extent] for t in range(len(mask)))
    assert np.array_equal(mask,mask.transpose(1,0,2,3)[:,:,::-1,::-1])
    lookup,origin=make_lookup(labels,len(mask))
    sptr,offsets=pack_stencil(mask,extent)
    vertices=planar_vertices(labels,tiling)
    xy=vertices.mean(axis=1)
    weights=tiling.areas[labels[:,2]]
    proposals=seed_proposals(vertices,labels,tiling,R,parent)
    seed=793000+int(R*1000)+N+(10000 if family=="hex" else 0)
    rng=np.random.default_rng(seed)
    outcomes=[]
    if mode=="coarse":
        counts=stencil_counts(labels,lookup,origin,sptr,offsets)
        pointer=np.r_[0,np.cumsum(counts)]
        assert pointer[-1]<600_000_000,"use fine mode for larger graphs"
        indices=stencil_fill(labels,lookup,origin,sptr,offsets,pointer)
        empty=np.zeros(len(labels),dtype=np.bool_)
        starts=[]
        for name,proposed in proposals:
            initial=weighted_greedy(pointer,indices,np.flatnonzero(proposed),empty)
            starts.append((name,initial))
        for center in [np.zeros(2),xy[rng.integers(len(labels))]]:
            order=np.argsort(np.sum((xy-center)**2,axis=1))
            starts.append(("spatial",weighted_greedy(pointer,indices,order,empty)))
        order=np.argsort(counts/weights+rng.random(len(labels))*counts.mean()/weights.mean()*.1)
        starts.append(("weighted_degree",weighted_greedy(pointer,indices,order,empty)))
        best=max(starts,key=lambda p:weights@p[1])[1].copy()
        for trial,(name,initial) in enumerate(starts):
            if weights@initial<.82*(weights@best):
                continue
            initial=weighted_greedy(pointer,indices,rng.permutation(len(labels)),initial)
            found=weighted_local(pointer,indices,weights/weights.max(),initial,seed+trial,sweeps)
            outcomes.append({"source":name,"area_units":int(weights@found)})
            if weights@found>weights@best:
                best=found
        if patches:
            radius=.13
            assert 2*radius+2*np.linalg.norm(vertices-xy[:,None,:],axis=2).max()<1
            centers=xy[rng.integers(len(labels),size=patches)]
            groups=cKDTree(xy).query_ball_point(centers,rng.uniform(.035,radius,patches))
            pptr=np.r_[0,np.cumsum([len(g) for g in groups])]
            pind=np.array([v for g in groups for v in g],dtype=np.int32)
            found=weighted_patch_local(pointer,indices,weights/weights.max(),pptr,pind,best,seed+3300)
            if weights@found>weights@best:
                best=found
        search_info={"edges":int(pointer[-1]//2),"outcomes":outcomes,"sweeps":sweeps,"patches":patches}
        del indices,pointer
    else:
        best=np.zeros(len(labels),dtype=np.bool_)
        records=[]
        for trial,(name,initial) in enumerate(proposals):
            found,info=implicit_extend(labels,mask,extent,lookup,origin,sptr,offsets,initial,xy,weights,seed+trial)
            records.append({"source":name,"initial_area_units":int(weights@initial),**info})
            if weights@found>weights@best:
                best=found
        search_info={"implicit_extensions":records}
    chosen=labels[best]
    assert mask_pair_violations(chosen,mask,extent)==0
    counts=[int(np.sum(chosen[:,2]==t)) for t in range(len(mask))]
    if family=="hex":
        coefficient=Fraction(3*len(chosen),2*tiling.scale**2)
        constant,sqrt_coefficient,radical=Fraction(0),coefficient,3
        area_expression=f"({coefficient})*sqrt(3)"
        area=float(coefficient)*math.sqrt(3)
        area_fraction=None
    elif family=="regular-oct":
        o,s=counts
        constant=Fraction(3*s-2*o,N*N)
        sqrt_coefficient=Fraction(2*o-2*s,N*N)
        coefficient,radical=constant,2
        area_expression=f"({constant}) + ({sqrt_coefficient})*sqrt(2)"
        area=float(constant)+float(sqrt_coefficient)*math.sqrt(2)
        area_fraction=None
    else:
        coefficient=Fraction(int(weights@best),tiling.scale**2)
        constant,sqrt_coefficient,radical=coefficient,Fraction(0),1
        area_expression=str(coefficient)
        area=float(coefficient)
        area_fraction=str(coefficient)
    filename=f"erdos953-{family}-R{R:g}-N{N}-{mode}-{STAMP}.json"
    cert={"family":family,"R":str(Fraction(str(R))),"N":N,
          "parameters":tiling.parameters,"cells":chosen.tolist(),"type_counts":counts,
          "area_expression":area_expression,"area_fraction":area_fraction,
          "area_coefficient":str(coefficient),"area_radical":radical,
          "area_constant":str(constant),"area_sqrt_coefficient":str(sqrt_coefficient),
          "policy":"closed polygons strictly inside the open disk; every cross-cell distance avoids all positive integers",
          "search_mode":mode,"search_info":search_info,"finite_optimum_proved":False}
    (HERE/filename).write_text(json.dumps(cert,separators=(",",":")),encoding="utf-8")
    result={"family":family,"R":float(R),"N":N,"nodes":len(labels),"selected":len(chosen),
            "type_counts":counts,"area":area,"area_expression":area_expression,"certificate":filename,
            "seconds":time.perf_counter()-started,"mode":mode,"search_info":search_info,
            "finite_optimum_proved":False,"lean_formalized":False}
    print(json.dumps(result),flush=True)
    del mask,lookup,vertices
    gc.collect()
    return result


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--families",nargs="+",default=["oct","hex"])
    parser.add_argument("--radii",nargs="+",type=float,default=[1,1.5,2])
    parser.add_argument("--levels",nargs="+",type=int,default=[16,32])
    parser.add_argument("--sweeps",type=int,default=35)
    parser.add_argument("--patches",type=int,default=350)
    parser.add_argument("--mode",choices=["coarse","fine"],default="coarse")
    parser.add_argument("--parent")
    args=parser.parse_args()
    path=HERE/f"erdos953-alternative-tilings-results-{STAMP}.json"
    results=json.loads(path.read_text()) if path.exists() else []
    for R in args.radii:
        for family in args.families:
            parent=args.parent
            if parent is None:
                earlier=[r for r in results if r["family"]==family and r["R"]==R and r["N"]<min(args.levels)]
                if earlier:
                    parent=str(HERE/max(earlier,key=lambda r:r["area"])["certificate"])
            for N in args.levels:
                result=run_case(family,R,N,args.sweeps,args.patches,args.mode,parent)
                results=[r for r in results if (r["family"],r["R"],r["N"],r["mode"])!=(family,R,N,args.mode)]
                results.append(result)
                path.write_text(json.dumps(results,indent=2),encoding="utf-8")
                parent=str(HERE/result["certificate"])


if __name__=="__main__":
    main()
