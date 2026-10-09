"""Analyze the executed rational neutral test case; floating root recovery is diagnostic."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
from pathlib import Path
import sympy as s,numpy as np,json
from scipy.optimize import root,minimize
P=Path(__file__).resolve().parents[1];data=json.loads((P/'results/envelope_input.json').read_text());x,y=s.symbols('x y',real=True)
N,W,F,G=[s.sympify(data[k],locals={'x':x,'y':y}) for k in ['N','W','F','G']]
a=np.array([float(s.sympify(k))for k in data['a']]);e=np.array([float(s.sympify(k))for k in data['e']]);d=np.array([complex(s.sympify(k))for k in data['d']]);g=np.ones(3)
funs=s.lambdify((x,y),[N,W,F,G],'numpy')
def BM(th):
 phases=np.array([th[0],th[1],th[1]-th[0]])
 off=(e+np.real(d*np.exp(1j*phases)))/2
 return np.array([[a[0]/2,off[0],off[1]],[off[0],a[1]/2,off[2]],[off[1],off[2],a[2]/2]])
def radial(th):
 B=BM(th);h=np.linalg.solve(B,g);return h/np.sum(h)
def grad(th):
 r=radial(th);q=-np.imag(d*np.exp(1j*np.array([th[0],th[1],th[1]-th[0]])))
 return np.array([r[0]*r[1]*q[0]-r[1]*r[2]*q[2],r[0]*r[2]*q[1]+r[1]*r[2]*q[2]])
sols=[]
for t in np.linspace(-np.pi,np.pi,19,endpoint=False):
 for u in np.linspace(-np.pi,np.pi,19,endpoint=False):
  q=root(grad,[t,u],tol=1e-11)
  th=(q.x+np.pi)%(2*np.pi)-np.pi
  if np.max(np.abs(grad(th)))>1e-8:continue
  if any(np.linalg.norm(np.angle(np.exp(1j*(th-v['theta']))))<1e-6 for v in sols):continue
  r=radial(th);val=float(r@BM(th)@r)
  sols.append({'theta':th.tolist(),'tan_half':np.tan(th/2).tolist(),'r':r.tolist(),'value':val,'physical':bool(np.min(r)>-1e-8),'full_support':bool(np.min(np.abs(r))>1e-7),'gradient_residual':float(np.max(np.abs(grad(th))))})
sols.sort(key=lambda v:v['value'])
factors=s.factor_list(s.sympify(data['clean_x_resultant'],locals={'x':x}),x)[1]
for sol in sols:
 tx=sol['tan_half'][0];match=[]
 for f,m in factors:
  p=s.Poly(f,x);coeff=np.array([float(v)for v in p.all_coeffs()]);coeff/=np.max(np.abs(coeff));res=abs(np.polyval(coeff,tx))/(1+abs(tx))**p.degree()
  if res<1e-7:match.append(p.degree())
 sol['x_factor_degrees']=match
 print(sol)
# Independent constrained minimization in simplex plus phases.
def obj(v):
 rr=np.array([v[0],v[1],1-v[0]-v[1]]);return rr@BM(v[2:])@rr
rng=np.random.default_rng(110927);best=None
for _ in range(80):
 rr=rng.dirichlet(np.ones(3));v=np.r_[rr[:2],rng.uniform(-np.pi,np.pi,2)]
 ans=minimize(obj,v,method='SLSQP',constraints=[{'type':'ineq','fun':lambda q:1-q[0]-q[1]}],bounds=[(0,1),(0,1),(None,None),(None,None)],options={'ftol':1e-13,'maxiter':500})
 if best is None or ans.fun<best.fun:best=ans
out={'stationary_candidates':sols,'count':len(sols),'independent_simplex_minimum':float(best.fun),'independent_point':best.x.tolist(),'qualification':'Floating diagnostic. Neither all roots nor global minimum certified.'}
(P/'results/envelope_analysis.json').write_text(json.dumps(out,indent=2));print('best independent',best.fun,best.x)
