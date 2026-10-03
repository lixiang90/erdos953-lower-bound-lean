"""A single explicit unbounded integer-distance-free set and dyadic limits.

The block construction has area growth Theta(sqrt(R)*(loglog R/log R)^3).
This is the order of this particular set, not a claim of sharpness for M(R).
Dyadic-square counts are exact and compressed, without materializing billions
of squares. The mathematical proof is in the accompanying research note.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import math
import random

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
BASE_AREA=Fraction(1,2048)


def integer_root(A,p):
    lo,hi=0,1<<((A.bit_length()+p-1)//p)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**p<=A:
            lo=mid
        else:
            hi=mid
    return hi if hi**p<=A else lo


def parameters(j):
    assert j>=6
    A=4**j//16
    n=2
    while (2*(n+1))**(2*(n+1))<=A:
        n+=1
    k=integer_root(A,2*n)
    assert 2*n<=k<9*n and k**(2*n)<=A<(k+1)**(2*n)
    assert (k-1)**(2*n)*16>A  # (k-1)^n > sqrt(A)/4.
    return k,n


def center(j,digits):
    k,n=parameters(j)
    assert len(digits)==n and all(0<=d<=k-2 for d in digits)
    return (2**j+sum(d*k**i for i,d in enumerate(digits)),
            3*4**j+8*k*sum(d*k**(2*i) for i,d in enumerate(digits)))


def block_area(j):
    k,n=parameters(j)
    return Fraction((k-1)**n,1024*k**3)


def ceil_div(a,b):
    return (a+b-1)//b


def grid_block_count(j,N):
    k,n=parameters(j)
    horizontal=max(0,2*ceil_div(N,8)-2)
    vertical=max(0,2*ceil_div(N,512*k**3)-2)
    return (k-1)**n*horizontal*vertical


def grid_base_count(N):
    return max(0,2*ceil_div(N,8)-2)*max(0,2*ceil_div(N,1024)-2)


def rectangle_conflict(first,second):
    # Tuples are center-x, center-y, full-height; full-width is always 1/4.
    x,y,e=first
    X,Y,E=second
    a,b=abs(y-Y),abs(x-X)
    halfheight=(e+E)/2
    minimum=max(Fraction(b)-Fraction(1,4),0)**2+max(Fraction(a)-halfheight,0)**2
    maximum=(Fraction(b)+Fraction(1,4))**2+(Fraction(a)+halfheight)**2
    k=math.isqrt(maximum.numerator//maximum.denominator)
    return k>=1 and minimum<=k*k


def verify_construction():
    rectangles=[(0,0,Fraction(1,512))]
    blocks=[]
    for j in range(6,11):
        k,n=parameters(j)
        eps=Fraction(1,256*k**3)
        points=[]
        for digits in product(range(k-1),repeat=n):
            x,y=center(j,digits)
            assert 2**j<=x<5*2**j/4
            assert 3*4**j<=y<Fraction(7,2)*4**j
            assert x+y+1<4**(j+1)
            points.append((x,y,eps))
        rectangles.extend(points)
        blocks.append((j,len(points)))
    pairs=0
    for i,first in enumerate(rectangles):
        for second in rectangles[i+1:]:
            assert not rectangle_conflict(first,second)
            pairs+=1
    rng=random.Random(953)
    for trial in range(1000):
        j=rng.randrange(7,150)
        i=rng.randrange(6,j)
        k,n=parameters(j)
        K,m=parameters(i)
        x,y=center(j,[rng.randrange(k-1) for _ in range(n)])
        X,Y=center(i,[rng.randrange(K-1) for _ in range(m)])
        b,a=x-X,y-Y
        assert b>=1 and b*b<=a<=32*b*b
    # Test the exact closed-cell index formula with direct rational intervals.
    for N in range(2,150):
        for half in (Fraction(1,8),Fraction(1,1024),Fraction(1,32768)):
            count=sum(Fraction(i,N)>-half and Fraction(i+1,N)<half
                      for i in range(-N,N))
            expected=max(0,2*ceil_div(N*half.numerator,half.denominator)-2)
            assert count==expected
    return {"explicit_rectangles":len(rectangles),"exact_rational_pairs":pairs,
            "random_arbitrary_precision_cross_block_checks":1000,
            "grid_interval_count_checks":148*3,"all_passed":True,"blocks":blocks}


def main():
    audit=verify_construction()
    cumulative=BASE_AREA
    growth=[]
    for j in range(6,201):
        k,n=parameters(j)
        area=block_area(j)
        cumulative+=area
        radius=4**(j+1)
        growth.append({"j":j,"k":k,"n":n,"rectangle_count":str((k-1)**n),
                       "radius":str(radius),"block_area":str(area),
                       "exact_area_inside_radius":str(cumulative),
                       "growth_exponent_float":math.log(float(cumulative))/math.log(radius)})
    J=12
    true_area=BASE_AREA+sum((block_area(j) for j in range(6,J+1)),Fraction(0))
    refinements=[]
    for m in (12,14,16,18,20,22,24,26,28,30,34,38,42):
        N=2**m
        count=grid_base_count(N)+sum(grid_block_count(j,N) for j in range(6,J+1))
        area=Fraction(count,N*N)
        assert area<=true_area
        refinements.append({"m":m,"N":N,"radius":4**(J+1),"square_count":str(count),
                            "exact_grid_area":str(area),"exact_limit_area":str(true_area),
                            "fraction_of_limit_float":float(area/true_area)})
    output={"definition":{"j_min":6,"horizontal_translation":"2^j",
                          "vertical_translation":"3*4^j","radius_for_complete_blocks":"4^(j+1)",
                          "base_rectangle":"(-1/8,1/8) x (-1/1024,1/1024)",
                          "component_width":"1/4","component_height":"1/(256*k_j^3)",
                          "limit":"increasing union of closed dyadic squares strictly contained in a component"},
            "audit":audit,"growth":growth,"dyadic_refinements":refinements,
            "status":"paper proof and exact arithmetic verification; not a full Lean formalization"}
    (HERE/f"erdos953-square-limit-construction-{STAMP}.json").write_text(json.dumps(output,indent=2),encoding="utf-8")
    fig,axes=plt.subplots(1,2,figsize=(12,4.5))
    axes[0].plot([g["j"] for g in growth],[g["growth_exponent_float"] for g in growth],color="#147baf")
    axes[0].axhline(.5,color="black",linestyle="--",label="Proved limiting exponent 1/2")
    axes[0].set_xlabel("Block index j; radius R_j=4^(j+1)")
    axes[0].set_ylabel("log(exact constructed area) / log(R_j)")
    axes[0].legend(fontsize=9)
    axes[0].grid(alpha=.2)
    axes[1].plot([r["m"] for r in refinements],[r["fraction_of_limit_float"] for r in refinements],"o-",color="#438a65")
    axes[1].axhline(1,color="black",linestyle="--")
    axes[1].set_xlabel("Dyadic resolution m; N=2^m")
    axes[1].set_ylabel("Exact grid area / explicit limit area")
    axes[1].set_title("Compressed square counts, fixed radius 4^13")
    axes[1].grid(alpha=.2)
    fig.tight_layout()
    fig.savefig(HERE/f"erdos953-square-limit-construction-{STAMP}.png",dpi=170)
    plt.close(fig)
    print(json.dumps({"audit":audit,"J12_limit_area":str(true_area),
                      "last_refinement":refinements[-1],"last_growth":{k:v for k,v in growth[-1].items()
                      if k in ("j","k","n","growth_exponent_float")}}))


if __name__=="__main__":
    main()
