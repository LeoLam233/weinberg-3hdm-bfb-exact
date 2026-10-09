"""Floating deformations of singular and zero-boundary quartics.
These probes do NOT implement formal infinitesimals or certify root coverage.
"""
from pathlib import Path
import json
import numpy as np
from weinberg import Model,search
from generic_spectrum_probe import candidates
P=Path(__file__).resolve().parents[1]
z=np.zeros(3)
coeff=np.array([1,-2,3,-2,1,2,3,-1,2,1,2,-2,3,1,-3],dtype=float)/50
Qmod=Model(2+coeff[:3],2+coeff[3:6],coeff[6:9],coeff[[9,11,13]]+1j*coeff[[10,12,14]])
uniform_delta_bound=float(.5*np.abs(coeff[:3]).sum()+.25*np.abs(coeff[3:]).sum())
assert uniform_delta_bound<.5
bases=[
 ('identically_zero',Model(z.copy(),z.copy(),z.copy(),z.copy().astype(complex)),0.),
 ('constant_trace_square',Model(np.ones(3)*2,np.ones(3)*2,z.copy(),z.copy().astype(complex)),1.),
 ('charged_zero_boundary',Model(np.ones(3)*(1+7/30),np.ones(3)*(-1+7/30),np.ones(3),np.ones(3,dtype=complex)/2),0.)]
res={'scope':'Finite real-epsilon, floating roots and BFGS diagnostics only','Q_coefficient_perturbation':coeff.tolist(),'Q_uniform_bounds':[1-uniform_delta_bound,1+uniform_delta_bound],'records':[]}
for j,(name,base,m0) in enumerate(bases):
 for k,eps in enumerate([.2,.05,.01]):
  model=Model(base.a+eps*Qmod.a,base.b+eps*Qmod.b,base.c+eps*Qmod.c,base.d+eps*Qmod.d)
  cc=candidates(model,grid=13);best=min(cc,key=lambda q:q['value'])
  direct=search(model,seed=609001+11*j+k,starts=12)
  item={'model':name,'epsilon':eps,'spectrum_minimum_found':best['value'],'direct_minimum_found':direct['value'],'difference':best['value']-direct['value'],'minimum_minus_base_divided_by_epsilon':(best['value']-m0)/eps,'winning_kind':best['kind'],'winning_support':best['support'],'direct_gradient_norm':direct['gradient'],'physical_candidates_found':len(cc)}
  assert abs(item['difference'])<2e-7
  assert 1-uniform_delta_bound-2e-7<item['minimum_minus_base_divided_by_epsilon']<1+uniform_delta_bound+2e-7
  res['records'].append(item)
  (P/'results/singular_probe.json').write_text(json.dumps(res,indent=2));print(item,flush=True)
