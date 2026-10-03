"""Rational fractional-clique-cover upper bounds for finite square graphs."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import argparse
import json
import math
import random
import time
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from erdos953_square_grid_upper import vertices,edge

HERE=Path(__file__).resolve().parent
STAMP="2026-10-03"
Q=10**6


def adjacency(N,vs):
    coords=np.array(vs,dtype=np.int32)
    u=np.abs(coords[:,0,None]-coords[:,0])
    v=np.abs(coords[:,1,None]-coords[:,1])
    L=np.maximum(u-1,0)**2+np.maximum(v-1,0)**2
    U=(u+1)**2+(v+1)**2
    roots=np.array([math.isqrt(k)//N for k in range(int(U.max())+1)],dtype=np.int32)
    k=roots[U]
    graph=(k>=1)&(L<=N*N*k*k)
    assert not np.diag(graph).any() and (graph==graph.T).all()
    return [int.from_bytes(row.tobytes(),"little") for row in np.packbits(graph,axis=1,bitorder="little")]


def bits(mask):
    out=[]
    while mask:
        b=mask&-mask
        out.append(b.bit_length()-1)
        mask-=b
    return out


def partition(adj,rng):
    remain=(1<<len(adj))-1
    cover=[]
    while remain:
        candidates=remain
        clique=[]
        while candidates:
            choices=bits(candidates)
            sample=rng.sample(choices,min(20,len(choices)))
            v=max(sample,key=lambda i:(adj[i]&candidates).bit_count())
            clique.append(v)
            candidates&=adj[v]
        for v in clique: remain&=~(1<<v)
        cover.append(tuple(sorted(clique)))
    return cover


def solve(N,R):
    started=time.perf_counter()
    vs=vertices(N,R)
    adj=adjacency(N,vs)
    rng=random.Random(953000+N*100+int(R))
    cliques=set()
    lengths=[]
    for rep in range(8):
        cover=partition(adj,rng)
        lengths.append(len(cover))
        cliques.update(cover)
    cliques=sorted(cliques)
    rr,cc=[],[]
    for i,C in enumerate(cliques):
        for v in C: rr.append(v);cc.append(i)
    matrix=coo_matrix((-np.ones(len(rr)),(rr,cc)),shape=(len(vs),len(cliques))).tocsr()
    result=linprog(np.ones(len(cliques)),A_ub=matrix,b_ub=-np.ones(len(vs)),bounds=(0,None),method="highs")
    assert result.success,result.message
    units=np.maximum(np.ceil(result.x*Q),0).astype(np.int64)
    chosen=[(list(C),int(w)) for C,w in zip(cliques,units) if w>0]
    coverage=[0]*len(vs)
    for C,w in chosen:
        for v in C: coverage[v]+=w
        for a,b in combinations(C,2):
            assert edge(N,abs(vs[a][0]-vs[b][0]),abs(vs[a][1]-vs[b][1]))
    for v,c in enumerate(coverage):
        if c<Q: chosen.append(([v],Q-c))
    total=sum(w for C,w in chosen)
    upper=total//Q
    cert={"N":N,"R":str(R),"vertices":len(vs),"weight_denominator":Q,
          "weighted_cliques":chosen,"total_weight_fraction":str(F(total,Q)),
          "integer_upper":upper,"area_upper_fraction":str(F(upper,N*N)),
          "partition_counts":lengths,"all_vertices_covered":True,
          "finite_graph_upper_only":True,"is_continuous_upper_at_this_N":False}
    filename=f"erdos953-grid-clique-upper-R{R}-N{N}-{STAMP}.json"
    (HERE/filename).write_text(json.dumps(cert,separators=(",",":")),encoding="utf-8")
    row={k:v for k,v in cert.items() if k!="weighted_cliques"}
    row.update(certificate=filename,cliques=len(chosen),seconds=time.perf_counter()-started)
    print(json.dumps(row),flush=True)
    return row


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--extra",action="store_true")
    args=parser.parse_args()
    path=HERE/f"erdos953-square-grid-clique-upper-results-{STAMP}.json"
    rows=json.loads(path.read_text())["results"] if args.extra else []
    cases=((F(1),(24,32)),) if args.extra else ((F(1),(4,6,8,12,16)),(F(2),(8,12,16)))
    for R,Ns in cases:
        for N in Ns:
            rows.append(solve(N,R))
            path.write_text(json.dumps({"results":rows,"finite_graph_upper_only":True},indent=2),encoding="utf-8")


if __name__=="__main__": main()
