"""Independent exact certificate audit for the two new polygon tilings.

Does not import the optimizer, its Minkowski hulls, masks, FFT, or Shapely.
Rebuilds tile vertices and uses both directions of vertex-to-segment minima.
Regular hexagons use the integer axial norm a^2+ab+b^2. Arithmetic in the
compiled kernels is integral and a checked bound excludes int64 overflow.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np
from numba import njit, prange, set_num_threads

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
set_num_threads(8)


def reconstruct(data):
    family,N=data["family"],int(data["N"])
    if family=="square":
        polys=[[(0,0),(1,0),(1,1),(0,1)]]
        shift=np.array([[1,0],[0,1]],dtype=np.int64)
        q=N
        metric=0
    elif family in ("oct","regular-oct"):
        d,cut,diamond=(10,3,3) if family=="oct" else (1000,292,293)
        assert 0<cut<=diamond<d/2
        if family=="regular-oct":
            # cut/d <= 1-1/sqrt(2) <= diamond/d, by exact squaring.
            # The rational polygons enclose the true regular cells.
            assert 2*(d-cut)**2>=d*d
            assert 2*(d-diamond)**2<=d*d
        polys=[[(cut,0),(d-cut,0),(d,cut),(d,d-cut),(d-cut,d),
                (cut,d),(0,d-cut),(0,cut)],[(0,-diamond),(diamond,0),(0,diamond),(-diamond,0)]]
        shift=np.array([[d,0],[0,d]],dtype=np.int64)
        q=d*N
        metric=0
    else:
        assert family=="hex"
        q=int(data["parameters"]["q"])
        polys=[[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]]
        shift=np.array([[2,-1],[1,1]],dtype=np.int64)
        metric=1
    nv=np.array(list(map(len,polys)),dtype=np.int64)
    vertices=np.zeros((len(polys),max(nv),2),dtype=np.int64)
    for t,p in enumerate(polys):
        vertices[t,:len(p)]=p
    return vertices,nv,shift,q,metric,polys


@njit(cache=True)
def nrm(x,y,metric):
    return x*x+y*y+(x*y if metric else 0)


@njit(cache=True)
def polygons_intersect(p,npv,z,nzv,dx,dy):
    for reverse in range(2):
        edges,points=(p,z) if reverse==0 else (z,p)
        ne,npnt=(npv,nzv) if reverse==0 else (nzv,npv)
        sx,sy=(dx,dy) if reverse==0 else (-dx,-dy)
        for j in range(ne):
            ex=edges[(j+1)%ne,0]-edges[j,0]
            ey=edges[(j+1)%ne,1]-edges[j,1]
            separated=True
            for i in range(npnt):
                cross=ex*(points[i,1]+sy-edges[j,1])-ey*(points[i,0]+sx-edges[j,0])
                if cross>=0:
                    separated=False; break
            if separated:
                return False
    return True


@njit(cache=True)
def polygon_interval4(p,npv,z,nzv,dx,dy,metric):
    hi=np.int64(0)
    lo4=np.int64(2**62)
    for i in range(npv):
        for j in range(nzv):
            hi=max(hi,nrm(p[i,0]-z[j,0]-dx,p[i,1]-z[j,1]-dy,metric))
    for reverse in range(2):
        points,edges=(p,z) if reverse==0 else (z,p)
        nv,ne=(npv,nzv) if reverse==0 else (nzv,npv)
        sx,sy=(-dx,-dy) if reverse==0 else (dx,dy)
        for i in range(nv):
            for j in range(ne):
                wx=points[i,0]+sx-edges[j,0]
                wy=points[i,1]+sy-edges[j,1]
                ex=edges[(j+1)%ne,0]-edges[j,0]
                ey=edges[(j+1)%ne,1]-edges[j,1]
                g=math.gcd(abs(ex),abs(ey))
                vx,vy=ex//g,ey//g
                length=nrm(vx,vy,metric)
                dot2=2*wx*vx+2*wy*vy+(wx*vy+wy*vx if metric else 0)
                if dot2<=0:
                    value=4*nrm(wx,wy,metric)
                elif dot2>=2*g*length:
                    value=4*nrm(wx-ex,wy-ey,metric)
                else:
                    assert dot2*dot2%length==0
                    value=4*nrm(wx,wy,metric)-dot2*dot2//length
                lo4=min(lo4,value)
    return (0 if polygons_intersect(p,npv,z,nzv,dx,dy) else lo4),hi


@njit(cache=True,parallel=True)
def independent_mask(vertices,nv,shift,q,metric,extent):
    nt=len(nv)
    width=2*extent+1
    result=np.zeros((nt,nt,width,width),dtype=np.uint8)
    for ii in prange(nt*nt*width*width):
        z=np.int64(ii)
        b=z%width-extent
        a=z//width%width-extent
        u=z//(width*width)%nt
        t=z//(width*width*nt)
        dx=a*shift[0,0]+b*shift[1,0]
        dy=a*shift[0,1]+b*shift[1,1]
        lo4,hi=polygon_interval4(vertices[t],nv[t],vertices[u],nv[u],dx,dy,metric)
        root=int(math.sqrt(hi))
        while (root+1)**2<=hi:
            root+=1
        while root*root>hi:
            root-=1
        k=root//q
        if k>=1 and lo4<=4*(k*q)**2:
            result[t,u,a+extent,b+extent]=1
    return result


@njit(cache=True,parallel=True)
def pair_checks(labels,mask,extent):
    bad=np.zeros(len(labels),dtype=np.int64)
    for ii in prange(len(labels)):
        i=np.int64(ii)
        for j in range(i+1,len(labels)):
            bad[i]+=mask[labels[i,2],labels[j,2],labels[j,0]-labels[i,0]+extent,
                         labels[j,1]-labels[i,1]+extent]
    return bad.sum()


def verify(path):
    data=json.loads(path.read_text())
    vertices,nv,shift,q,metric,polys=reconstruct(data)
    labels=np.array(data["cells"],dtype=np.int64)
    assert len(labels)>0 and len({tuple(map(int,p)) for p in labels})==len(labels)
    assert set(map(int,labels[:,2]))<=set(range(len(nv)))
    r=Fraction(data["R"])
    extent=int(np.ptp(labels[:,:2],axis=0).max())
    max_coordinate=(extent+2)*int(np.abs(shift).sum())+2*int(np.abs(vertices).max())
    # Primitive edges have coordinate magnitude <=1 and norm <=2.
    # This covers endpoint norms, dot squares, scaled norms, and root corrections.
    assert 128*max_coordinate**2<2**63
    for a,b,t in labels:
        cx,cy=int(a)*int(shift[0,0])+int(b)*int(shift[1,0]),int(a)*int(shift[0,1])+int(b)*int(shift[1,1])
        for x,y in polys[int(t)]:
            x,y=x+cx,y+cy
            assert (x*x+y*y+(x*y if metric else 0))*r.denominator**2<(q*r.numerator)**2
    for t,p in enumerate(polys):
        maximum=max((x-a)**2+(y-b)**2+((x-a)*(y-b) if metric else 0)
                    for x,y in p for a,b in p)
        assert maximum<q*q
    mask=independent_mask(vertices,nv,shift,q,metric,extent)
    assert pair_checks(labels,mask,extent)==0
    counts=[int(np.sum(labels[:,2]==t)) for t in range(len(nv))]
    twice_areas=[abs(sum(p[i][0]*p[(i+1)%len(p)][1]-p[i][1]*p[(i+1)%len(p)][0]
                        for i in range(len(p)))) for p in polys]
    # Axial coordinates have Jacobian sqrt(3)/2, Cartesian coordinates 1.
    coefficient=Fraction(sum(n*a for n,a in zip(counts,twice_areas)),(4 if metric else 2)*q*q)
    if data["family"]=="regular-oct":
        octagons,squares=counts
        constant=Fraction(3*squares-2*octagons,int(data["N"])**2)
        coefficient=Fraction(2*octagons-2*squares,int(data["N"])**2)
        assert str(constant)==data["area_coefficient"]==data["area_constant"]
        assert str(coefficient)==data["area_sqrt_coefficient"]
        radical=2
    else:
        assert str(coefficient)==data["area_coefficient"]
        constant=Fraction(0) if metric else coefficient
        coefficient=coefficient if metric else Fraction(0)
        radical=3 if metric else 1
    assert radical==data["area_radical"] and counts==data["type_counts"]
    if radical==3:
        root_lo,root_hi=Fraction(1732050807568877,10**15),Fraction(1732050807568878,10**15)
    elif radical==2:
        root_lo,root_hi=Fraction(1414213562373095,10**15),Fraction(1414213562373096,10**15)
    else:
        root_lo=root_hi=Fraction(1)
    if radical>1:
        assert root_lo*root_lo<radical<root_hi*root_hi
    lower=constant+coefficient*(root_lo if coefficient>=0 else root_hi)
    upper=constant+coefficient*(root_hi if coefficient>=0 else root_lo)
    return {"certificate":path.name,"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
            "status":"passed independent exact integer geometry",
            "selected":len(labels),"pair_checks":len(labels)*(len(labels)-1)//2,
            "area_constant":str(constant),"area_sqrt_coefficient":str(coefficient),"area_radical":radical,
            "area_lower_fraction":str(lower),"area_upper_fraction":str(upper),
            "integer_overflow_excluded":True,"lean_formalized":False}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("files",nargs="*")
    parser.add_argument("--output",default=str(HERE/f"erdos953-alternative-tilings-independent-audit-{STAMP}.json"))
    args=parser.parse_args()
    if args.files:
        paths=[Path(p) for p in args.files]
    else:
        rows=json.loads((HERE/f"erdos953-alternative-tilings-results-{STAMP}.json").read_text())
        paths=[HERE/r["certificate"] for r in rows]
    output=[]
    for path in paths:
        result=verify(path)
        output.append(result)
        print(json.dumps(result),flush=True)
        Path(args.output).write_text(json.dumps({"certificates_verified":len(output),"results":output},indent=2),encoding="utf-8")


if __name__=="__main__":
    main()
