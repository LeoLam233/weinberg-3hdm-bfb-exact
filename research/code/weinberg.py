"""Weinberg 3HDM quartic. Numerical probes only; no certification by optimization."""
from __future__ import annotations
from dataclasses import dataclass
import numpy as np
from numpy.typing import NDArray
from scipy.optimize import minimize

PAIRS=((0,1),(0,2),(1,2))
@dataclass
class Model:
    a: NDArray
    b: NDArray
    c: NDArray
    d: NDArray
    def matrix(self):
        L=np.zeros((9,9),dtype=float)
        L[:3,:3]=np.diag(self.a)
        for t,(i,j) in enumerate(PAIRS):
            L[i,j]=L[j,i]=self.b[t]
            u,v=np.real(self.d[t]),np.imag(self.d[t])
            L[3+2*t:5+2*t,3+2*t:5+2*t]=[[self.c[t]+u,-v],[-v,self.c[t]-u]]
        return L
    def value(self,K):
        r=np.real(np.diag(K))
        return float(.5*np.dot(self.a,r*r)+sum(self.b[t]*r[i]*r[j]+self.c[t]*abs(K[i,j])**2+np.real(self.d[t]*K[i,j]**2) for t,(i,j) in enumerate(PAIRS)))

def hvec(K):
    return np.array(list(np.real(np.diag(K)))+[x for i,j in PAIRS for x in (np.sqrt(2)*K[i,j].real,np.sqrt(2)*K[i,j].imag)])
def hmat(k):
    K=np.diag(np.asarray(k[:3],dtype=complex))
    for t,(i,j) in enumerate(PAIRS):
        K[i,j]=(k[3+2*t]+1j*k[4+2*t])/np.sqrt(2)
        K[j,i]=np.conj(K[i,j])
    return K

def unpack(x,nrows=2):
    n=3*nrows
    return np.asarray(x[:n]).reshape(nrows,3)+1j*np.asarray(x[n:]).reshape(nrows,3)
def pack(Phi):
    return np.r_[Phi.real.ravel(),Phi.imag.ravel()]

def objective(x,L,nrows=2):
    P=unpack(x,nrows)
    norm=float(np.vdot(P,P).real)
    if norm<1e-24:
        return 1e40,np.zeros_like(x)
    K=P.conj().T@P; k=hvec(K); Z=hmat(L@k)
    f=float(.5*k@L@k)
    G=2*P@Z/norm**2-4*f*P/norm**3
    return f/norm**2,pack(G)

def search(model,seed=0,starts=12,nrows=2):
    rng=np.random.default_rng(seed);L=model.matrix();best=None
    for _ in range(starts):
        x=rng.normal(size=6*nrows);x/=np.linalg.norm(x)
        out=minimize(objective,x,args=(L,nrows),method='BFGS',jac=True,options={'gtol':2e-10,'maxiter':1200})
        if best is None or out.fun<best.fun: best=out
    P=unpack(best.x,nrows);P/=np.linalg.norm(P)
    K=P.conj().T@P
    return {'value':float(best.fun),'K':K,'Phi':P,'gradient':float(np.linalg.norm(objective(best.x,L,nrows)[1])),'solver_success':bool(best.success)}
