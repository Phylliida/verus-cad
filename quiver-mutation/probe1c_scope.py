#!/usr/bin/env python3
"""Is the extracted degree-4 conservation law global, or twin-hub-specific?"""
import random, re

def mutate(B,k):
    n=len(B); Bp=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i==k or j==k: Bp[i][j]=-B[i][j]
            else: Bp[i][j]=B[i][j]+(abs(B[i][k])*B[k][j]+B[i][k]*abs(B[k][j]))//2
    return Bp
def skew(entries,n):
    B=[[0]*n for _ in range(n)]
    for (i,j,v) in entries: B[i][j]=v; B[j][i]=-v
    return B
def upper(B): return tuple(B[i][j] for i in range(4) for j in range(i+1,4))

# parse the invariant from the extraction output
terms=[]
names={"b01":0,"b02":1,"b03":2,"b12":3,"b13":4,"b23":5}
import sys
for line in open(sys.argv[1]):
    m=re.match(r"\s+([+-]\d+) \* (.+)",line)
    if not m: continue
    coef=int(m.group(1)); t=[0]*6; s=[0]*6
    for factor in m.group(2).split("*|") if False else re.findall(r"\|?b\d\d\|?(?:\^\d)?",m.group(2)):
        pass
    # simpler: tokenize on '*' respecting |..|
    expr=m.group(2)
    for tok in re.findall(r"\|b\d\d\|(?:\^\d)?|b\d\d",expr):
        if tok.startswith("|"):
            var=tok[1:4]; e=int(tok[-1]) if "^" in tok else 1
            t[names[var]]+=e
        else:
            t[names[tok]]+=1; s[names[tok]]^=1
    terms.append((coef,tuple(t),tuple(s)))
print(f"parsed {len(terms)} terms")

def evalf(pt):
    tot=0
    for coef,t,s in terms:
        v=coef
        for i in range(6):
            if t[i]:
                v*=abs(pt[i])**t[i]
                if s[i] and pt[i]<0: v=-v
                if s[i] and pt[i]==0: v=0; break
        tot+=v
    return tot

# sanity: values on twin-hub templates
def tmpl_twin(c): return skew([(0,1,1),(1,2,1),(0,3,1),(3,2,1),(0,2,c)],4)
print("tmpl values c=3..7:",[evalf(upper(tmpl_twin(c))) for c in range(3,8)])

# test 1: GLOBAL invariance on random rank-4 pairs
random.seed(3)
viol=0; tot=8000
for _ in range(tot):
    B=skew([(i,j,random.randint(-8,8)) for i in range(4) for j in range(i+1,4)],4)
    k=random.randrange(4)
    if evalf(upper(mutate(B,k)))!=evalf(upper(B)): viol+=1
print(f"global random pairs: {viol}/{tot} violations")

# test 2: invariance on the OTHER gadget families' orbits
for name, T in [("mixed-sign-hubs", skew([(0,1,1),(1,2,1),(0,3,1),(3,2,-1),(0,2,5)],4)),
                ("arm2",            skew([(0,1,1),(1,2,1),(0,3,2),(3,2,1),(0,2,5)],4)),
                ("random-walk-seeded", skew([(0,1,2),(1,2,-1),(0,3,1),(3,2,1),(0,2,7),(1,3,1)],4))]:
    viol=0; tot2=0; B=T
    random.seed(5)
    for _ in range(4000):
        k=random.randrange(4)
        B1=mutate(B,k)
        if max(abs(e).bit_length() for row in B1 for e in row)>1200: B=T; continue
        if evalf(upper(B1))!=evalf(upper(B)): viol+=1
        tot2+=1; B=B1
    print(f"{name} orbit walk: {viol}/{tot2} violations")
