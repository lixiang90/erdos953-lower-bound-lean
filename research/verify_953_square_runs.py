"""Self-contained, standard-library-only rational rectangle certificate check."""
from pathlib import Path
from fractions import Fraction
import argparse
import json
import math


def verify(data):
    N=data["coordinate_denominator"]
    R=Fraction(data["R"])
    rects=data["rectangles"]
    assert isinstance(N,int) and N>0
    rows={}
    cells=0
    for xlo,xhi,ylo,yhi in rects:
        assert all(isinstance(x,int) for x in (xlo,xhi,ylo,yhi))
        assert xhi>xlo and yhi==ylo+1
        assert (xhi-xlo)**2+(yhi-ylo)**2<N*N
        for x in (xlo,xhi):
            for y in (ylo,yhi):
                assert (x*x+y*y)*R.denominator**2<(N*R.numerator)**2
        rows.setdefault(ylo,[]).append((xlo,xhi))
        cells+=(xhi-xlo)*(yhi-ylo)
    for intervals in rows.values():
        intervals.sort()
        assert all(a[1]<=b[0] for a,b in zip(intervals,intervals[1:]))
    pairs=0
    for i,(a,b,c,d) in enumerate(rects):
        for e,f,g,h in rects[i+1:]:
            nx,ny=max(0,a-f,e-b),max(0,c-h,g-d)
            fx,fy=max(abs(a-f),abs(b-e)),max(abs(c-h),abs(d-g))
            lo,hi=nx*nx+ny*ny,fx*fx+fy*fy
            k=math.isqrt(hi)//N
            assert k<1 or lo>(k*N)**2
            pairs+=1
    area=Fraction(cells,N*N)
    assert area==Fraction(data["area_fraction"])
    return {"rectangles":len(rects),"exact_rational_rectangle_pairs":pairs,
            "area_fraction":str(area),"all_passed":True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("files",nargs="*")
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    files=[Path(p) for p in args.files] if args.files else sorted(here.glob("erdos953-square-runs-R2-N*-2026-10-03.json"))
    results=[]
    for path in files:
        results.append({"file":path.name,**verify(json.loads(path.read_text()))})
        print(json.dumps(results[-1]),flush=True)
    (here/"erdos953-square-runs-independent-audit-2026-10-03.json").write_text(json.dumps(results,indent=2),encoding="utf-8")


if __name__=="__main__":
    main()
