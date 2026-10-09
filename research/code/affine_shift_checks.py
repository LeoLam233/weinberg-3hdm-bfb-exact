"""Independent normalization/covariance test: f -> f+h (tr K)^2."""
from pathlib import Path
import json
import sympy as s
import numpy as np
from weinberg import Model
from hexagon_numeric import full_candidates
P=Path(__file__).resolve().parents[1]
h,be,a,p=s.symbols('h beta a p');k=1+2*h*be;D=be*p-a*a
bp=be/k;ap=a/k;pp=p-2*h*a*a/k;Dp=s.factor(bp*pp-ap*ap)
assert s.factor(Dp-D/k)==0
assert s.factor(pp/(2*Dp)-p/(2*D)-h)==0
# R_h I=RI/k; R_h P=RP-2h*a*RI/k. Coefficients of RI and RP agree in K.
coeff_RI=s.factor((pp/k+ap*2*h*a/k)/Dp);coeff_RP=s.factor(-ap/Dp)
assert s.factor(coeff_RI-p/D)==0 and s.factor(coeff_RP+a/D)==0
assert s.factor(pp/ap**2-(k*k*p/a**2-2*h*k))==0
records=json.loads((P/'results/duality_probe.json').read_text())['records'];out=[]
for rec in records[:4]:
    for shift in [1.0,-.5]:
        model=Model(np.array(rec['a'])+2*shift,np.array(rec['b'])+2*shift,np.array(rec['c']),np.array(rec['d_real'])+1j*np.array(rec['d_imag']))
        candidates,diag=full_candidates(model);best=min(candidates,key=lambda x:x['value'])
        expected=rec['minimum_found']+shift;err=abs(best['value']-expected)
        assert err<1e-7
        out.append({'model_index':rec['index'],'shift':shift,'spectrum_minimum':best['value'],'expected_from_unshifted_direct_field_value':expected,'absolute_difference':err,'constructor':best['constructor']})
res={'arbitrary_symbolic_identity':'Sherman-Morrison: beta_h=beta/k, a_h=a/k, p_h=p-2h*a^2/k, D_h=D/k; K_h=K; E_h=E+h','k':'1+2h*beta','dual_quotient_transform':'nu_h=k^2 nu-2hk','numerical_checks_scope':'independent rerun of sextic spectrum after positive/negative shifts; reference uses unshifted direct field minimum plus known exact constant','cases':out}
(P/'results/affine_shift_checks.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
