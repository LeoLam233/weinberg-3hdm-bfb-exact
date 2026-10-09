"""Convex moment outer relaxation, implemented by LP eigenvector cuts.
This is NOT asserted exact for the physical orbit or the complete SOS cone.
Every displayed moment inequality has an elementary Gram/Cauchy origin.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from weinberg import Model,PAIRS,search

def blocks(y):
    a,b,c,u,v=np.split(y,5)
    R=np.diag(a).astype(complex);T=R.copy();Z=R.copy()
    for t,(i,j) in enumerate(PAIRS):
        R[i,j]=R[j,i]=b[t]
        T[i,j]=T[j,i]=2*c[t]-b[t]
        Z[i,j]=u[t]+1j*v[t];Z[j,i]=Z[i,j].conjugate()
    return [R,T,Z]+[np.array([[c[t],u[t]+1j*v[t]],[u[t]-1j*v[t],c[t]]]) for t in range(3)]
BASIS=[blocks(e) for e in np.eye(15)]
def cut(block,v):
    return np.array([np.vdot(v,b[block]@v).real for b in BASIS])
def relax(model,maxiter=180,tol=1e-8,neutral=False):
    costs=np.r_[.5*model.a,model.b,model.c,model.d.real,-model.d.imag]
    cuts=[]
    for k,B in enumerate(blocks(np.zeros(15))):
        for v in np.eye(len(B)): cuts.append(cut(k,v))
        for i in range(len(B)):
            for j in range(i+1,len(B)):
                for z in [1,-1,1j,-1j]:
                    v=np.zeros(len(B),complex);v[i]=1;v[j]=z
                    cuts.append(cut(k,v))
    for t in range(3):
        v=np.zeros(15);v[3+t]=1;v[6+t]=-1;cuts.append(v)
    eq=np.r_[np.ones(3),np.full(3,2),np.zeros(9)].reshape(1,-1)
    rhs=[1]
    if neutral:
        more=np.zeros((3,15))
        for j in range(3):more[j,3+j]=1;more[j,6+j]=-1
        eq=np.vstack((eq,more));rhs += [0]*3
    for it in range(maxiter):
        out=linprog(costs,A_ub=-np.array(cuts),b_ub=np.zeros(len(cuts)),A_eq=eq,b_eq=rhs,bounds=[(-1,1)]*15,method='highs',options={'threads':1})
        if not out.success: raise RuntimeError(out.message)
        worst=0.;added=0
        for k,B in enumerate(blocks(out.x)):
            w,U=np.linalg.eigh(B);worst=min(worst,float(w[0]))
            for j in np.where(w<-tol)[0]:
                cuts.append(cut(k,U[:,j]));added+=1
        if added==0:break
    return {'lower_bound':float(out.fun),'moment':out.x.tolist(),'min_psd_eigenvalue':worst,'iterations':it+1,'converged_to_tolerance':bool(worst>=-tol)}

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1];rng=np.random.default_rng(31865);records=[]
    for i in range(60):
        m=Model(rng.uniform(.1,2,3),rng.uniform(-2,2,3),rng.uniform(-2,2,3),rng.normal(size=3)+1j*rng.normal(size=3))
        r=relax(m);p=search(m,seed=i,starts=12)
        row={'index':i,'a':m.a.tolist(),'b':m.b.tolist(),'c':m.c.tolist(),'d_real':m.d.real.tolist(),'d_imag':m.d.imag.tolist(),'relaxation':r,'physical_min_found':p['value'],'gap':p['value']-r['lower_bound'],'physical_K_eigenvalues':np.linalg.eigvalsh(p['K']).tolist()}
        records.append(row)
        if row['gap']>1e-4:print('gap',i,row['gap'],flush=True)
    report={'seed':31865,'models':len(records),'interpretation':'diagnostic outer relaxation; physical minimum is an upper bound only','max_gap':max(r['gap'] for r in records),'records':records}
    (root/'results/moment_probe.json').write_text(json.dumps(report,indent=2))
    print('models',len(records),'max gap',report['max_gap'],'large gaps',sum(r['gap']>1e-4 for r in records))
