"""Certified finite-window upper bounds for the square-cell conflict graph.

LP proposes a positive-definite trigonometric kernel. Nonnegative Fourier
weights imply PSD analytically; rational cosine intervals independently
certify negativity on EVERY allowed displacement, giving alpha<=1+K(0)/c.
These are finite GRID upper bounds, not finite-N upper bounds for M(R).
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import math
import time
import numpy as np
from scipy.optimize import linprog

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
COS_Q=2**24
WEIGHT_Q=10**7


def pi_bounds():
    def atan(d):
        s=sum((F((-1)**i,(2*i+1)*d**(2*i+1)) for i in range(32)),F(0))
        e=F(1,65*d**65)
        return s-e,s+e
    l,h=atan(5)
    L,H=atan(239)
    return 16*l-4*H,16*h-4*L


def ceil(x): return -((-x.numerator)//x.denominator)


def cosines(T):
    path=HERE/f"erdos953-grid-upper-cosines-T{T}-{STAMP}.json"
    pl,ph=pi_bounds()
    p=(pl+ph)/2
    table=[]
    for r in range(T//2+1):
        if r==0: low=high=COS_Q
        elif 2*r==T: low=high=-COS_Q
        elif 4*r==T: low=high=0
        else:
            x=2*p*r/T
            term,total=F(1),F(1)
            for k in range(1,32):
                term*=-x*x/F((2*k-1)*(2*k))
                total+=term
            error=x**64/math.factorial(64)+(ph-pl)*F(r,T)
            low=((total-error)*COS_Q).__floor__()
            high=ceil((total+error)*COS_Q)
        table.append((low,high))
    table=[table[min(r,T-r)] for r in range(T)]
    path.write_text(json.dumps({"T":T,"denominator":COS_Q,"intervals":table,
        "pi_bound":"Machin formula with 32 alternating terms",
        "cos_bound":"32 even Taylor terms with Lagrange remainder plus argument interval"},separators=(",",":")),encoding="utf-8")
    return np.array(table,dtype=np.int64),path.name


def edge(N,u,v):
    L=max(u-1,0)**2+max(v-1,0)**2
    U=(u+1)**2+(v+1)**2
    k=math.isqrt(U)//N
    return k>=1 and L<=N*N*k*k


def nonedges(N,R):
    B=math.floor(2*N*R)
    radius2=4*N*N*R*R
    return [(u,v) for u in range(B+1) for v in range(u+1)
            if (u or v) and u*u+v*v<=radius2 and not edge(N,u,v)]


def vertices(N,R):
    m=ceil(N*R)
    return [(i,j) for i in range(-m,m) for j in range(-m,m)
            if max(abs(i),abs(i+1))**2+max(abs(j),abs(j+1))**2 < N*N*R*R]


def product_upper(l,h,L,H):
    return np.maximum(np.maximum(l*L,l*H),np.maximum(h*L,h*H))


def exact_kernel_bound(ds,frequencies,units,table):
    worst=None
    worst_delta=None
    for u,v in ds:
        a,b=frequencies.T
        T=len(table)
        lu,hu=table[(a*u)%T].T
        lv,hv=table[(b*v)%T].T
        Lu,Hu=table[(b*u)%T].T
        Lv,Hv=table[(a*v)%T].T
        upper=product_upper(lu,hu,lv,hv)+product_upper(Lu,Hu,Lv,Hv)
        num=sum(int(x)*int(y) for x,y in zip(upper,units))
        if worst is None or num>worst: worst,worst_delta=num,(u,v)
    assert worst<0,(worst,worst_delta)
    # K(0)=sum(units)/WEIGHT_Q; negativity denominator is 2*COS_Q^2*WEIGHT_Q.
    bound=1+F(sum(int(u) for u in units)*2*COS_Q*COS_Q,-worst)
    return bound,worst,worst_delta


def solve(N,R):
    started=time.perf_counter()
    vs=vertices(N,R)
    ds=nonedges(N,R)
    row_bound=(N-1)*len(set(j for i,j in vs))
    common={"N":N,"R":str(R),"vertices":len(vs),"row_upper":min(row_bound,len(vs)),
            "nonedge_displacements":len(ds),"whole_closed_cells":True,
            "finite_grid_bound_only":True,"is_continuous_upper_at_this_N":False}
    if not ds:
        bound=min(1,len(vs))
        cert={**common,"kind":"complete_graph","integer_upper":bound,"area_upper_fraction":str(F(bound,N*N))}
    else:
        T=4*ceil(N*R)+4
        features=np.array([(a,b) for a in range(T//2+1) for b in range(a+1) if a or b],dtype=np.int32)
        table,cosfile=cosines(T)
        d=np.array(ds,dtype=np.int32)
        a,b=features.T
        u,v=d.T
        C=np.cos(2*np.pi*u[:,None]*a/T)*np.cos(2*np.pi*v[:,None]*b/T)
        C+=np.cos(2*np.pi*u[:,None]*b/T)*np.cos(2*np.pi*v[:,None]*a/T)
        C*=.5
        result=linprog(np.ones(len(features)),A_ub=C,b_ub=-np.ones(len(ds)),bounds=(0,None),
                       method="highs",options={"primal_feasibility_tolerance":1e-9})
        assert result.success,result.message
        weights=np.maximum(np.rint(result.x*WEIGHT_Q),0).astype(np.int64)
        support=weights>0
        feats,units=features[support],weights[support]
        kernel_bound,worst,worst_delta=exact_kernel_bound(ds,feats,units,table)
        integer_upper=min(kernel_bound.__floor__(),row_bound,len(vs))
        cert={**common,"kind":"positive_definite_cosine_kernel","T":T,"cosine_certificate":cosfile,
            "weight_denominator":WEIGHT_Q,"weights":[[int(a),int(b),int(w)] for (a,b),w in zip(feats,units)],
            "kernel_formula":"sum w_ab*(cos(2*pi*a*u/T)*cos(2*pi*b*v/T)+cos(2*pi*b*u/T)*cos(2*pi*a*v/T))/2",
            "negative_upper_numerator":str(worst),"negative_upper_denominator":str(2*COS_Q*COS_Q*WEIGHT_Q),
            "worst_displacement":list(worst_delta),"kernel_alpha_upper_fraction":str(kernel_bound),
            "integer_upper":integer_upper,"area_upper_fraction":str(F(integer_upper,N*N)),
            "solver_objective_diagnostic":float(result.fun),"frequencies_used":int(support.sum())}
    filename=f"erdos953-grid-upper-R{str(R).replace('/','_')}-N{N}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert,separators=(",",":")),encoding="utf-8")
    brief={k:v for k,v in cert.items() if k in common or k in ("kind","integer_upper","area_upper_fraction","frequencies_used")}
    brief.update(certificate=filename,seconds=time.perf_counter()-started)
    print(json.dumps(brief),flush=True)
    return brief


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--quick",action="store_true")
    args=parser.parse_args()
    cases=[(N,F(1)) for N in (2,3,4,6,8,12,16)]
    cases+=[(N,F(2)) for N in (4,8,12,16)]+[(N,F(4)) for N in (4,8)]+[(4,F(8))]
    if args.quick: cases=cases[:5]
    outputs=[]
    path=HERE/f"erdos953-square-grid-upper-results-{STAMP}.json"
    for N,R in cases:
        outputs.append(solve(N,R))
        path.write_text(json.dumps({"results":outputs,"infinite_density_upper":"0 for every fixed N>=2",
            "finite_graph_bounds_do_not_bound_M_at_fixed_N":True,
            "continuous_limit":"alpha_N(R)/N^2 tends to M(R) for each fixed R",
            "known_uniform_in_N_order":"alpha_N(R)<=C*N^2*sqrt(R) for N>=11,R>=1",
            "new_uniform_constant_or_logarithmic_improvement_proved":False,
            "lean_formalized":False},indent=2),encoding="utf-8")


if __name__=="__main__": main()
