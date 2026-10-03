"""Independent, standard-library-only audit of the infinite enlargement.

No optimizer, numerical geometry or construction-generator imports. Finite
closed-rectangle distance intervals are verified with arbitrary precision
integers. Universal tail arguments are written out in the accompanying note;
this script checks their exact rational constants, not a formal Lean proof.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import math

HERE = Path(__file__).resolve().parent
STAMP = "2026-10-03"


def root(A, p):
    lo, hi = 0, 1 << ((A.bit_length()+p-1)//p)
    while hi-lo > 1:
        m = (lo+hi)//2
        if m**p <= A: lo = m
        else: hi = m
    return hi if hi**p <= A else lo


def params(j):
    A, n = 4**j//16, 2
    while (2*n+2)**(2*n+2) <= A: n += 1
    k = root(A, 2*n)
    assert 2*n <= k < 9*n
    assert k**(2*n) <= A < (k+1)**(2*n)
    return k, n


def points(j, k, n):
    B = 2**j
    return [(B+sum(d*k**i for i,d in enumerate(ds)),
             3*B*B+8*k*sum(d*k**(2*i) for i,d in enumerate(ds)))
            for ds in product(range(k-1), repeat=n)]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def check_polygon(path):
    data = json.loads(path.read_text(encoding="utf-8"))
    Q, vs = data["coordinate_denominator"], data["vertices"]
    bottom, top = map(F, data["vertical_strip"])
    cy = -9*Q//32
    for i, (x,y) in enumerate(vs):
        assert x*x+(y-cy)**2 < Q*Q//4
        assert bottom*Q < y < top*Q
        assert cross(vs[i-1],vs[i],vs[(i+1)%len(vs)]) > 0
    old = [(sx*F(1,8)*Q,sy*F(1,1024)*Q) for sx in (-1,1) for sy in (-1,1)]
    for p in old:
        for a,b in zip(vs,vs[1:]+vs[:1]): assert cross(a,b,p) > 0
    area = F(sum(x*Y-y*X for (x,y),(X,Y) in zip(vs,vs[1:]+vs[:1])),2*Q*Q)
    assert area == F(data["area_fraction"])
    assert area > F(7,10) > F(1,432)
    return {"certificate":path.name,"sha256":sha(path),"area_fraction":str(area),
            "vertices":len(vs),"contains_original_base":True,
            "strictly_inside_half_unit_disk_and_strip":True}


def universal_constants():
    cap, delta = F(1,256), F(1,512)
    cross_lower = F(4,9)-64*(cap+delta)
    cross_upper = 2*(1-cap-delta)-F(16,9)
    assert cross_lower == F(5,72) > 0 and cross_upper > 0
    assert cap*cap > delta*delta and (1-delta)**2 > cap*cap
    vlo, vhi = F(81,512), F(369,512)
    base_lower = F(95,96)**2-6*(vlo+delta)
    base_upper = 2*(1-delta-vhi)-F(25,48)*F(97,96)**2
    assert base_lower > 0 and base_upper > 0
    assert vlo*vlo > delta*delta and (1-delta)**2 > vhi*vhi
    # All old-source integer epsilon annuli miss the narrower central strip.
    eps, old_halfheight = F(1,64), F(1,32768)
    top, bottom = F(9,64), F(-45,64)
    ring_lower = F(507,512)**2-6*(top+old_halfheight+eps)
    ring_upper = 2*(1-eps+bottom-old_halfheight)-F(25,48)*F(517,512)**2
    assert ring_lower > 0 and ring_upper > 0
    assert (top+old_halfheight)**2 > eps**2
    assert (1-eps)**2 > (-bottom+old_halfheight)**2
    # The old base itself has no annulus intersecting this central witness.
    # The norm estimate uses the extreme corner of this narrower strip:
    # x^2=1/4-(27/64)^2, y^2=(45/64)^2 => 145/256.
    assert F(145,256) < F(25,32)**2
    assert F(25,32)+F(1,7) < 1-eps
    outer = F(1,2048)+F(129,256)*F(65,64)+F(22,7)*F(65,64)**2
    assert outer < 4
    assert F(7,24)**2+F(3,1024)**2 < F(63,64)**2
    assert F(256,27)*F(1,524288) == F(1,55296)
    return {"cross_lower":str(cross_lower),"cross_upper":str(cross_upper),
            "enlarged_base_lower":str(base_lower),"enlarged_base_upper":str(base_upper),
            "all_integer_epsilon_ring_base_lower":str(ring_lower),
            "all_integer_epsilon_ring_base_upper":str(ring_upper),
            "all_future_blocks_included_by_analytic_proof":True}


def phase_bounds(X,Y,U,V,B,h):
    """Uniform future-source bound, independent of numerical search output."""
    bmin,amin=B-abs(X),3*B*B-abs(Y)
    assert bmin>U and amin>V
    C=(F(7,2)+F(abs(Y),B*B))/(1-F(abs(X),B))**2
    D=(F(5,4)+F(abs(X),B))**2/(3-F(abs(Y),B*B))
    u,v=U/bmin,V/amin
    lo=(1-u)**2/C/(2*(1+v)+D*(1+u)**2/(2*amin*(1-v)))-h
    hi=D*(1+u)**2/(2*(1-v))+h
    return lo,hi


def integer_boxes(boxes,S):
    assert all((z*S).denominator==1 for b in boxes for z in b)
    return [tuple(int(z*S) for z in b) for b in boxes]


def band_conflict(r,s,S,E):
    xl,xr,yl,yr=r
    al,ar,bl,br=s
    dx,dy=max(al-xr,xl-ar,0),max(bl-yr,yl-br,0)
    DX,DY=max(abs(xl-ar),abs(xr-al)),max(abs(yl-br),abs(yr-bl))
    L,U=dx*dx+dy*dy,DX*DX+DY*DY
    m=math.isqrt(U//(S*S))
    return any(k>=1 and L<=(k*S+E)**2 and U>=(k*S-E)**2 for k in (m,m+1))


def check_hole_addition(new_boxes):
    path=HERE/f"erdos953-Ainfty-all-ring-hole-extension-{STAMP}.json"
    data=json.loads(path.read_text())
    added=[tuple(map(F,b)) for b in data["added_rectangles"]]
    eps=F(data["epsilon_against_preexisting_set"])
    assert eps==F(1,512)
    S=math.lcm(512,*(z.denominator for box in new_boxes+added for z in box))
    sources=integer_boxes(new_boxes,S)
    candidates=integer_boxes(added,S)
    area=F(0)
    cursor=0
    for group,(X,Y) in zip(data["window_groups"],points(6,4,2)):
        assert group["center"]==[X,Y] and group["first_rectangle"]==cursor
        lo,hi=phase_bounds(X,Y,F(2,5)+F(1,6),F(1,8)+F(1,512),2**14,F(1,512))
        assert [str(lo),str(hi)]==group["tail_phase_bounds"]
        end=cursor+group["rectangle_count"]
        group_area=F(0)
        for box,r in zip(added[cursor:end],candidates[cursor:end]):
            xl,xr,yl,yr=box
            assert X-F(2,5)<=xl<xr<=X+F(2,5)
            assert Y+F(1,256)<=yl<yr<=Y+F(1,8)
            assert lo-(yr-Y)>eps and hi-(yl-Y)<1-eps
            for s in sources:
                assert not band_conflict(r,s,S,S//512)
                # Strict disjoint interiors are needed for adding areas.
                assert min(r[1],s[1])<=max(r[0],s[0]) or min(r[3],s[3])<=max(r[2],s[2])
            group_area+=(xr-xl)*(yr-yl)
        assert group_area==F(group["area_fraction"])
        area+=group_area
        cursor=end
    assert len(data["window_groups"])==9 and cursor==len(added)
    for i,r in enumerate(candidates):
        for s in candidates[i+1:]:
            assert min(r[1],s[1])<=max(r[0],s[0]) or min(r[3],s[3])<=max(r[2],s[2])
            assert not band_conflict(r,s,S,S//512)
    assert F(16,25)+F(31,256)**2<(1-eps)**2
    assert area==F(data["area_fraction"])
    return {"certificate":path.name,"sha256":sha(path),"rectangles":len(added),
            "exact_source_pairs":len(added)*len(sources),
            "exact_added_pairs":len(added)*(len(added)-1)//2,"windows":9,"added_area_fraction":str(area),
            "all_integer_epsilon_annuli_missed":True,"epsilon":"1/512",
            "all_future_scales_excluded_by_uniform_phase_bound":True,
            "added_rectangles_mutually_integer_distance_free":True,
            "new_set_contains_A_infinity_plus":True}


def check_ring_cells():
    path=HERE/f"erdos953-Ainfty-all-integer-ring-cells-{STAMP}.json"
    data=json.loads(path.read_text())
    assert data["finite_prefix_last"]==11 and data["all_future_first"]==12
    sources=[(F(-1,8),F(1,8),F(-1,1024),F(1,1024))]
    for j in range(6,12):
        k,n=params(j)
        half=F(1,512*k**3)
        sources.extend((x-F(1,8),x+F(1,8),y-half,y+half) for x,y in points(j,k,n))
    all_boxes=[tuple(map(F,b)) for w in data["windows"] for g in w["cell_groups"] for b in g["boxes"]]
    S=math.lcm(32768,*(z.denominator for b in sources+all_boxes for z in b))
    iboxes=integer_boxes(sources,S)
    count=0
    for w in data["windows"]:
        X,Y=w["center"]
        ul,ur,vl,vr=map(F,w["offset_window"])
        lo,hi=phase_bounds(X,Y,max(abs(ul),abs(ur))+F(1,8),
                          max(abs(vl),abs(vr))+F(1,32768),2**12,F(1,32768))
        for g in w["cell_groups"]:
            eps=F(g["epsilon"])
            assert [str(lo),str(hi)]==g["tail_phase_interval"]
            for vals in g["boxes"]:
                box=tuple(map(F,vals))
                assert X+ul<=box[0]<box[1]<=X+ur and Y+vl<=box[2]<box[3]<=Y+vr
                a,b=lo-(box[3]-Y)-eps,hi-(box[2]-Y)+eps
                assert -((-a.numerator)//a.denominator)>b.numerator//b.denominator
                candidate=integer_boxes([box],S)[0]
                assert not any(band_conflict(candidate,s,S,int(eps*S)) for s in iboxes)
                count+=1
    return {"certificate":path.name,"sha256":sha(path),"entire_cells":count,
            "exact_source_pairs":count*len(sources),"all_positive_integer_radii_included":True,
            "all_future_scales_included":True,"pixel_counts_used_as_proof":False}


def main():
    result = json.loads((HERE/f"erdos953-Ainfty-ring-extension-results-{STAMP}.json").read_text())
    report = {"all_passed":False,"method":"independent arbitrary-precision integers and rational constants",
              "lean_formalized":False,"finite_optimum_proved":False,"blocks":[]}
    total_pairs = total_points = 0
    new_boxes=[(F(-1,2),F(1,2),F(-23,32),F(5,32))]
    for block in result["blocks"]:
        path = HERE/block["certificate"]
        data = json.loads(path.read_text())
        j, D, hs = data["j"], data["height_denominator"], data["height_numerators"]
        k,n = params(j)
        assert (k,n) == (data["k"],data["n"])
        ps = points(j,k,n)
        assert len(hs) == len(ps) == (k-1)**n
        for (x,y),h in zip(ps,hs):
            assert F(1,36*k**3) <= F(h,D) <= F(1,256)
            assert F(1,9)+F(h,D)**2 < 1
            assert 2**j <= x < F(5,4)*2**j
            assert 3*4**j <= y < F(7,2)*4**j
            assert x*x <= y <= 3*x*x and 48*x*x <= 25*y
            assert x+y+1 < 4**(j+1)
        S = 6*D
        pairs = 0
        min_lower = min_upper = None
        for i,(x,y) in enumerate(ps):
            for l in range(i+1,len(ps)):
                X,Y = ps[l]
                a,b = abs(Y-y),abs(X-x)
                assert 0 < b*b <= a <= 8*k*k*(k-1)*b*b
                hsum = hs[i]+hs[l]
                assert 9*a*hsum <= D*(3*b-1)**2
                L = (2*D*(3*b-1))**2+(6*D*a-3*hsum)**2
                U = (2*D*(3*b+1))**2+(6*D*a+3*hsum)**2
                low, high = L-(a*S)**2, ((a+1)*S)**2-U
                assert low > 0 and high > 0
                min_lower = low if min_lower is None else min(low,min_lower)
                min_upper = high if min_upper is None else min(high,min_upper)
                pairs += 1
        area = F(sum(hs),3*D)
        assert area == F(data["area_fraction"]) == F(block["extended_area_fraction"])
        assert F(data["uniform_area_fraction"]) == F(len(ps),108*k**3)
        total_pairs += pairs
        total_points += len(ps)
        new_boxes.extend((x-F(1,6),x+F(1,6),y-F(h,2*D),y+F(h,2*D)) for (x,y),h in zip(ps,hs))
        report["blocks"].append({"j":j,"rectangles":len(ps),"pairs":pairs,
            "sha256":sha(path),"area_fraction":str(area),
            "min_squared_lower_gap":str(F(min_lower,S*S)),
            "min_squared_upper_gap":str(F(min_upper,S*S)),"all_integer_distances_excluded":True})
    report["base"] = check_polygon(HERE/result["base"]["certificate"])
    safe_path = HERE/f"erdos953-Ainfty-all-integer-safe-base-{STAMP}.json"
    if safe_path.exists(): report["epsilon_1_over_64_base"] = check_polygon(safe_path)
    report["all_integer_ring_cells"]=check_ring_cells()
    report["additional_hole_extension"]=check_hole_addition(new_boxes)
    report["universal_constants"] = universal_constants()
    report["finite_rectangles"] = total_points
    report["finite_exact_pairs"] = total_pairs
    report["all_passed"] = True
    out = HERE/f"erdos953-Ainfty-ring-extension-independent-audit-{STAMP}.json"
    out.write_text(json.dumps(report,indent=2),encoding="utf-8")
    print(json.dumps({"all_passed":True,"rectangles":total_points,"exact_pairs":total_pairs,
                      "analytic_tail_constants":report["universal_constants"],"output":out.name}))


if __name__ == "__main__": main()
