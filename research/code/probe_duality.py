"""Executed post-COMMIT. Tests the candidate charged rank-two dual identity."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import check_grad
from weinberg import *
root=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(260609)
records=[];gradient_errors=[]
for q in range(24):
    model=Model(rng.uniform(.2,2,3),rng.uniform(-2,1,3),rng.uniform(-1,2,3),rng.normal(size=3)+1j*rng.normal(size=3))
    L=model.matrix();x=rng.normal(size=12)
    gradient_errors.append(check_grad(lambda x:objective(x,L)[0],lambda x:objective(x,L)[1],x))
    out=search(model,seed=q,starts=8);K=out['K'];ev,U=np.linalg.eigh(K)
    rec={'index':q,'minimum_found':out['value'],'K_eigenvalues':ev.tolist(),'gradient':out['gradient']}
    rec.update({key:np.asarray(getattr(model,key)).tolist() for key in ('a','b','c')})
    rec['d_real']=model.d.real.tolist();rec['d_imag']=model.d.imag.tolist()
    if ev[1]>1e-6 and abs(np.linalg.det(L))>1e-9:
        z=U[:,0];P=np.outer(z,z.conj());R=np.linalg.inv(L)
        RI=hmat(R@hvec(np.eye(3)));RP=hmat(R@hvec(P))
        B=np.trace(RI).real;A=np.trace(RP).real;p=np.trace(P@RP).real;D=B*p-A*A
        lam=p/D;mu=-A/D;Krec=lam*RI+mu*RP
        rec['dual']={'a':A,'b':B,'p':p,'D':D,'lambda':lam,'mu':mu,'value_residual':abs(out['value']-lam/2),'reconstruction_residual':float(np.linalg.norm(K-Krec)),'kernel_vector_residual':float(np.linalg.norm((A*RP-p*RI)@z))}
    records.append(rec)
result={'purpose':'floating-point diagnostic, not global or exact certification','seed':260609,'models':24,'starts_per_model':8,'max_finite_difference_gradient_error':max(gradient_errors),'rank2_cases':sum('dual' in r for r in records),'records':records}
(root/'results/duality_probe.json').write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
print('worst dual residuals:',{key:max(r['dual'][key] for r in records if 'dual'in r) for key in ['value_residual','reconstruction_residual','kernel_vector_residual']})
