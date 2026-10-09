"""Generic two-spectrum reconstruction, FLOATING diagnostic only.
Roots are searched, not isolated completely. Genericity is not certified here.
"""
from pathlib import Path
import json,numpy as np
from scipy.optimize import root
from weinberg import Model,PAIRS,hvec,hmat,search
P=Path(__file__).resolve().parents[1]
def spectra(a,e,d,g,grid=13):
 a,e,d,g=map(np.asarray,(a,e,d,g)); out=[]
 def B(th):
  ds=np.array([th[0],th[1],th[1]-th[0]])
  off=(e+np.real(d*np.exp(1j*ds)))/2
  return np.array([[a[0]/2,off[0],off[1]],[off[0],a[1]/2,off[2]],[off[1],off[2],a[2]/2]])
 def make(th,J):
  J=list(J); M=B(th)[np.ix_(J,J)]; gg=g[J]
  try:v=np.linalg.solve(M,gg)
  except np.linalg.LinAlgError:return None
  if abs(v.sum())<1e-11 or abs(gg@v)<1e-11:return None
  rr=np.zeros(3);rr[J]=v/v.sum()
  if min(rr[J])<-1e-7:return None
  phase=np.r_[0,th];w=np.sqrt(np.maximum(rr,0))*np.exp(.5j*phase)
  PP=np.outer(w.conj(),w)
  den=g@rr
  if abs(den)<1e-10:return None
  return {'r':rr,'phase':phase,'P':PP,'value':float(rr@B(th)@rr/den**2),'support':J}
 def grad(th):
  M=B(th)
  try:rr=np.linalg.solve(M,g)
  except np.linalg.LinAlgError:return [1e15,1e15]
  den=g@rr
  if abs(den)<1e-13:return [1e15,1e15]
  rr/=den;q=-np.imag(d*np.exp(1j*np.array([th[0],th[1],th[1]-th[0]])))
  return np.array([rr[0]*rr[1]*q[0]-rr[1]*rr[2]*q[2],rr[0]*rr[2]*q[1]+rr[1]*rr[2]*q[2]])
 for i in range(3):
  r=np.eye(3)[i];out.append({'r':r,'phase':np.zeros(3),'P':np.diag(r),'value':float(a[i]/2/g[i]**2),'support':[i]})
 for k,(i,j) in enumerate(PAIRS):
  for shift in [0,np.pi]:
   phase=np.zeros(3);phase[j]=-np.angle(d[k])+shift
   q=make(phase[1:]-phase[0],(i,j))
   if q is not None:out.append(q)
 seen=[]
 for t in np.linspace(-np.pi,np.pi,grid,endpoint=False):
  for u in np.linspace(-np.pi,np.pi,grid,endpoint=False):
   ans=root(grad,[t,u],tol=3e-11)
   th=(ans.x+np.pi)%(2*np.pi)-np.pi
   if np.max(np.abs(grad(th)))>1e-7:continue
   if any(np.linalg.norm(np.angle(np.exp(1j*(th-z))))<2e-6 for z in seen):continue
   seen.append(th);q=make(th,[0,1,2])
   if q is not None and min(q['r'])>1e-6:out.append(q)
 return out

def candidates(model,grid=13):
 L=model.matrix();RR=np.linalg.inv(L);AR=RR[:3,:3];gg=AR@np.ones(3);bb=gg.sum();delta=model.c**2-np.abs(model.d)**2
 prim=spectra(model.a,model.b+model.c,model.d,np.ones(3),grid)
 dual=spectra(2*np.diag(AR),np.array([2*(AR[i,j]+model.c[k]/delta[k])for k,(i,j)in enumerate(PAIRS)]),-2*model.d/delta,gg,grid)
 cand=[{'value':q['value'],'K':q['P'],'kind':'neutral','support':q['support']}for q in prim]
 RI=hmat(RR@hvec(np.eye(3)))
 for q in dual:
  PP=q['P'];RP=hmat(RR@hvec(PP));alpha=np.trace(RI@PP).real;pp=np.trace(RP@PP).real;D=bb*pp-alpha*alpha
  if abs(D)<1e-10:continue
  K=(pp*RI-alpha*RP)/D
  if np.min(np.linalg.eigvalsh(K))<-1e-7 or np.linalg.norm(K@PP)>1e-6:continue
  cand.append({'value':pp/2/D,'K':K,'kind':'charged','support':q['support'],'kernel_residual':float(np.linalg.norm(K@PP))})
 return cand
if __name__=='__main__':
 records=json.loads((P/'results/duality_probe.json').read_text())['records'];out=[]
 for rec in records[:12]:
  model=Model(np.array(rec['a']),np.array(rec['b']),np.array(rec['c']),np.array(rec['d_real'])+1j*np.array(rec['d_imag']))
  cc=candidates(model,grid=13);best=min(cc,key=lambda q:q['value']);item={'index':rec['index'],'spectrum_minimum_found':best['value'],'direct_field_minimum_found':rec['minimum_found'],'difference':best['value']-rec['minimum_found'],'winning_kind':best['kind'],'winning_support':best['support'],'physical_candidate_count':len(cc),'max_candidate_value_identity_error':max(abs(model.value(v['K'])-v['value'])for v in cc)};out.append(item)
  (P/'results/generic_spectrum_probe.json').write_text(json.dumps({'scope':'Floating diagnostic; no complete root isolation or global optimality certification','models':out},indent=2));print(item,flush=True)
