"""Independent exact audit of square-grid Fourier upper certificates.

Standard library only. Recomputes all graph nonedges, vertex counts, rational
cosine enclosures (a different term count and pi rounding), and kernel bounds.
The PSD implication and compact approximation are analytic proofs in the note.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import argparse
import hashlib
import json
import math

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"


def floor(x): return x.numerator//x.denominator
def ceil(x): return -((-x.numerator)//x.denominator)


def pi_interval():
    def a(d):
        s=sum((F((-1)**k,(2*k+1)*d**(2*k+1)) for k in range(40)),F(0))
        e=F(1,81*d**81)
        return s-e,s+e
    l,h=a(5)
    L,H=a(239)
    low,high=16*l-4*H,16*h-4*L
    Q=10**30
    return F(floor(low*Q),Q),F(ceil(high*Q),Q)


def check_cosines(path):
    data=json.loads(path.read_text())
    T,Q=data["T"],data["denominator"]
    assert T%4==0 and Q==2**24 and len(data["intervals"])==T
    pl,ph=pi_interval()
    p=(pl+ph)/2
    for r in range(T//2+1):
        lo,hi=data["intervals"][r]
        if r==0: assert lo==hi==Q
        elif 2*r==T: assert lo==hi==-Q
        elif 4*r==T: assert lo==hi==0
        else:
            x=F(2*r,T)*p
            # Direct factorial formula, not the generator recurrence.
            total=sum(((-1)**k*x**(2*k)/math.factorial(2*k) for k in range(36)),F(0))
            e=x**72/math.factorial(72)+F(r,T)*(ph-pl)
            assert F(lo,Q)<=total-e and total+e<=F(hi,Q)
    for r in range(T):
        assert data["intervals"][r]==data["intervals"][min(r,T-r)]
    return data


def graph_data(N,R):
    m=ceil(N*R)
    vs=[(i,j) for i in range(-m,m) for j in range(-m,m)
        if max(abs(i),abs(i+1))**2+max(abs(j),abs(j+1))**2<N*N*R*R]
    ds=[]
    B=floor(2*N*R)
    for u in range(B+1):
        for v in range(u+1):
            if u==v==0 or u*u+v*v>4*N*N*R*R: continue
            lower=max(u-1,0)**2+max(v-1,0)**2
            upper=(u+1)**2+(v+1)**2
            # Largest integer-distance candidate in the complete interval.
            k=math.isqrt(upper)//N
            if k<1 or lower>N*N*k*k: ds.append((u,v))
    return vs,ds


def coefficient_up(table,T,a,b,u,v):
    def prod(r,s):
        l,h=table[r%T]
        L,H=table[s%T]
        return max(l*L,l*H,h*L,h*H)
    return prod(a*u,b*v)+prod(b*u,a*v)


def check_cliques(report):
    rows=json.loads((HERE/f"erdos953-square-grid-clique-upper-results-{STAMP}.json").read_text())["results"]
    checked=[]
    pairs=0
    for row in rows:
        path=HERE/row["certificate"]
        data=json.loads(path.read_text())
        N,R=data["N"],F(data["R"])
        vs,unused=graph_data(N,R)
        assert len(vs)==data["vertices"]
        Q=data["weight_denominator"]
        assert Q==10**6
        coverage=[0]*len(vs)
        total=0
        count=0
        for C,w in data["weighted_cliques"]:
            assert isinstance(w,int) and w>0 and C and len(set(C))==len(C)
            assert all(isinstance(v,int) and 0<=v<len(vs) for v in C)
            for v in C: coverage[v]+=w
            for a,b in combinations(C,2):
                u,v=abs(vs[a][0]-vs[b][0]),abs(vs[a][1]-vs[b][1])
                lower=max(u-1,0)**2+max(v-1,0)**2
                upper=(u+1)**2+(v+1)**2
                k=math.isqrt(upper)//N
                assert k>=1 and lower<=N*N*k*k
                count+=1
            total+=w
        assert all(c>=Q for c in coverage)
        assert F(total,Q)==F(data["total_weight_fraction"])
        assert total//Q==data["integer_upper"]
        assert F(total//Q,N*N)==F(data["area_upper_fraction"])
        checked.append({"N":N,"R":str(R),"integer_upper":total//Q,
            "grid_area_upper":data["area_upper_fraction"],"clique_pairs_checked":count,
            "vertices_covered":len(vs),"sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"all_passed":True})
        pairs+=count
    report["clique_certificates"]=checked
    report["clique_pairs_checked"]=pairs
    return report


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--cliques-only",action="store_true")
    args=parser.parse_args()
    report_path=HERE/f"erdos953-square-grid-upper-independent-audit-{STAMP}.json"
    if args.cliques_only:
        report=json.loads(report_path.read_text())
        assert report["all_passed"]
        rows=json.loads((HERE/f"erdos953-square-grid-upper-results-{STAMP}.json").read_text())["results"]
        for r,a in zip(rows,report["certificates"]):
            assert hashlib.sha256((HERE/r["certificate"]).read_bytes()).hexdigest()==a["sha256"]
        for table in report["cosine_certificates"]:
            assert hashlib.sha256((HERE/table["file"]).read_bytes()).hexdigest()==table["sha256"]
        report=check_cliques(report)
        report_path.write_text(json.dumps(report,indent=2),encoding="utf-8")
        print(json.dumps({"all_passed":True,"new_clique_certificates":len(report["clique_certificates"]),
                          "exact_clique_pairs":report["clique_pairs_checked"]}))
        return
    source=HERE/f"erdos953-square-grid-upper-results-{STAMP}.json"
    results=json.loads(source.read_text())
    cosine_cache={}
    report={"all_passed":False,"certificates":[],"method":"standard-library arbitrary precision rational and integer arithmetic",
            "finite_graph_bounds_only":True,"lean_formalized":False}
    constraints=0
    for row in results["results"]:
        path=HERE/row["certificate"]
        data=json.loads(path.read_text())
        N,R=data["N"],F(data["R"])
        vs,ds=graph_data(N,R)
        assert len(vs)==data["vertices"] and len(ds)==data["nonedge_displacements"]
        row_bound=(N-1)*len(set(j for i,j in vs))
        assert data["row_upper"]==min(row_bound,len(vs))
        if data["kind"]=="complete_graph":
            assert not ds
            upper=min(1,len(vs))
        else:
            cospath=HERE/data["cosine_certificate"]
            if cospath.name not in cosine_cache: cosine_cache[cospath.name]=check_cosines(cospath)
            trig=cosine_cache[cospath.name]
            T,Q=trig["T"],trig["denominator"]
            assert T==data["T"]
            weights=data["weights"]
            assert len({(a,b) for a,b,w in weights})==len(weights)
            assert all(0<=b<=a<=T//2 and (a or b) and isinstance(w,int) and w>0 for a,b,w in weights)
            worst=max(sum(w*coefficient_up(trig["intervals"],T,a,b,u,v) for a,b,w in weights) for u,v in ds)
            assert worst<0 and worst==int(data["negative_upper_numerator"])
            assert data["weight_denominator"]==10**7
            assert int(data["negative_upper_denominator"])==2*Q*Q*10**7
            kernel_upper=1+F(sum(w for a,b,w in weights)*2*Q*Q,-worst)
            assert kernel_upper==F(data["kernel_alpha_upper_fraction"])
            upper=min(floor(kernel_upper),row_bound,len(vs))
        assert upper==data["integer_upper"]
        assert F(upper,N*N)==F(data["area_upper_fraction"])
        constraints+=len(ds)
        report["certificates"].append({"N":N,"R":str(R),"integer_upper":upper,
            "grid_area_upper":str(F(upper,N*N)),"nonedge_constraints_checked":len(ds),
            "sha256":hashlib.sha256(path.read_bytes()).hexdigest(),"all_passed":True})
    report["cosine_certificates"]=[{"file":name,"sha256":hashlib.sha256((HERE/name).read_bytes()).hexdigest()} for name in cosine_cache]
    report["nonedge_constraints_checked"]=constraints
    report["all_passed"]=True
    path=report_path
    path.write_text(json.dumps(report,indent=2),encoding="utf-8")
    print(json.dumps({"all_passed":True,"graphs":len(report["certificates"]),"nonedge_constraints":constraints,
                      "cosine_tables":len(cosine_cache),"audit":path.name}))


if __name__=="__main__": main()
