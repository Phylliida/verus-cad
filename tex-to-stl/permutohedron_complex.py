#!/usr/bin/env python3
"""STL for the SageMath PolyhedralComplex PPP = [P1..P8]:
2 permutohedra (P1 at origin, P2 at (2,2,2)) + 6 connector cells P3..P8.
Pure-python convex hulls + binary STL (per-piece, assembled, exploded)."""
import itertools, struct, math, os
from collections import defaultdict

def permutoedre4(v=(0,0,0)):
    bases=[[0,1,2],[0,1,-2],[0,-1,2],[0,-1,-2]]
    pts=[]
    for base in bases:
        for tau in sorted(set(itertools.permutations(base))):
            pts.append((v[0]+tau[0], v[1]+tau[1], v[2]+tau[2]))
    return pts

P=[None]*9
P[1]=permutoedre4((0,0,0))
P[2]=permutoedre4((2,2,2))
P[3]=[[0,1,2],[1,0,2],[-1,0,2],[0,-1,2],[2,0,3],[0,2,3],[1,-1,3],[-1,1,3],[1,0,4],[0,1,4],[1,2,4],[2,1,4]]
P[4]=[[1,2,0],[2,1,0],[0,1,-2],[1,0,-2],[0,2,-1],[2,0,-1],[1,2,-2],[2,1,-2],[1,3,-1],[3,1,-1],[2,3,0],[3,2,0]]
P[5]=[[0,1,2],[0,2,1],[-2,1,2],[-2,2,1],[-2,0,1],[-2,1,0],[-1,0,2],[-1,2,0],[-1,1,3],[-1,3,1],[0,2,3],[0,3,2]]
P[6]=[[1,2,0],[0,2,1],[-1,2,0],[0,2,-1],[1,3,-1],[-1,3,1],[2,3,0],[0,3,2],[1,4,2],[2,4,1],[0,4,1],[1,4,0]]
P[7]=[[0,-2,1],[0,-1,2],[1,-2,0],[1,0,2],[2,-1,0],[2,0,1],[1,-2,2],[1,-1,3],[2,-2,1],[2,0,3],[3,-1,1],[3,0,2]]
P[8]=[[2,0,1],[2,1,0],[3,0,2],[3,2,0],[4,1,2],[4,2,1],[3,1,-1],[4,0,1],[4,1,0],[3,-1,1],[2,-1,0],[2,0,-1]]

def sub(a,b):return (a[0]-b[0],a[1]-b[1],a[2]-b[2])
def cross(u,v):return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def dot(u,v):return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def nrm(u):return math.sqrt(dot(u,u))

def hull_triangles(V, eps=1e-7):
    V=[tuple(map(float,p)) for p in V]; n=len(V); seen=set(); tris=[]
    for i in range(n):
        for j in range(i+1,n):
            for k in range(j+1,n):
                nr=cross(sub(V[j],V[i]),sub(V[k],V[i])); L=nrm(nr)
                if L<1e-9: continue
                nr=(nr[0]/L,nr[1]/L,nr[2]/L); d=dot(nr,V[i])
                s=[dot(nr,V[m])-d for m in range(n)]
                if not(max(s)<=eps or min(s)>=-eps): continue
                if min(s)>=-eps: nr=(-nr[0],-nr[1],-nr[2]); d=-d
                key=tuple(round(x,5) for x in nr)+(round(d,5),)
                if key in seen: continue
                seen.add(key)
                on=[m for m in range(n) if abs(dot(nr,V[m])-d)<1e-5]
                ctr=tuple(sum(V[m][t] for m in on)/len(on) for t in range(3))
                e1=None
                for m in on:
                    dv=sub(V[m],ctr)
                    if nrm(dv)>1e-9: e1=tuple(x/nrm(dv) for x in dv); break
                e2=cross(nr,e1)
                order=sorted(on,key=lambda m:math.atan2(dot(sub(V[m],ctr),e2),dot(sub(V[m],ctr),e1)))
                for a in range(1,len(order)-1):
                    tris.append((V[order[0]],V[order[a]],V[order[a+1]]))
    return tris

def write_stl(path,tris):
    with open(path,"wb") as f:
        f.write(b"\0"*80); f.write(struct.pack("<I",len(tris)))
        for a,b,c in tris:
            nr=cross(sub(b,a),sub(c,a)); L=nrm(nr) or 1.0; nr=(nr[0]/L,nr[1]/L,nr[2]/L)
            for v in (nr,a,b,c): f.write(struct.pack("<3f",*v))
            f.write(struct.pack("<H",0))

os.makedirs("permutohedron_out",exist_ok=True)
all_tris=[]; piece_tris={}
allpts=[p for i in range(1,9) for p in P[i]]
cc=tuple(sum(q[t] for q in allpts)/len(allpts) for t in range(3))
exploded=[]
print("piece  hull-verts  facets  triangles")
for i in range(1,9):
    tris=hull_triangles(P[i])
    piece_tris[i]=tris; all_tris+=tris
    hv=set(); 
    for t in tris:
        for v in t: hv.add(tuple(round(x,4) for x in v))
    # facet count via distinct planes
    planes=set()
    for a,b,c in tris:
        nr=cross(sub(b,a),sub(c,a)); L=nrm(nr) or 1; nr=tuple(round(x/L,4) for x in nr)
        planes.add(nr+(round(dot(nr,a),3),))
    write_stl(f"permutohedron_out/P{i}.stl",tris)
    pc=tuple(sum(q[t] for q in P[i])/len(P[i]) for t in range(3))
    off=tuple(0.2*(pc[t]-cc[t]) for t in range(3))
    exploded+=[tuple((v[0]+off[0],v[1]+off[1],v[2]+off[2]) for v in tri) for tri in tris]
    name={1:"permutohedron(0,0,0)",2:"permutohedron(2,2,2)"}.get(i,f"connector P{i}")
    print(f"  P{i}   {len(hv):3d}        {len(planes):3d}     {len(tris):4d}   {name}")
write_stl("permutohedron_out/complex_assembled.stl",all_tris)
write_stl("permutohedron_out/complex_exploded.stl",exploded)
print(f"\nwrote permutohedron_out/P1..P8.stl + complex_assembled.stl + complex_exploded.stl")
print(f"total triangles assembled: {len(all_tris)}")
