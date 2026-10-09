"""Post-COMMIT exact construction of primal and dual two-phase envelopes.
A probe of generic instances, not all-coupling certification.
"""
from pathlib import Path
import sympy as s,json,time
from envelope_probe import envelope,x,y
root=Path(__file__).resolve().parents[1];Q=s.Rational
A=s.Matrix([[Q(4,5),-2,-1],[-2,Q(2,5),-Q(6,5)],[-1,-Q(6,5),Q(3,10)]])
c=[Q(4,5),-Q(9,10),Q(9,5)]
d=[-Q(2,5)+4*s.I/5,-Q(1,10)+2*s.I/5,Q(3,10)-19*s.I/10]
pairs=[(0,1),(0,2),(1,2)];R=A.inv();g=list(R*s.ones(3,1));delta=[s.factor(c[k]**2-s.re(d[k])**2-s.im(d[k])**2)for k in range(3)]
ap=[A[i,i]for i in range(3)]; ep=[A[i,j]+c[k]for k,(i,j)in enumerate(pairs)]
ad=[2*R[i,i]for i in range(3)];ed=[2*(R[i,j]+c[k]/delta[k])for k,(i,j)in enumerate(pairs)];dd=[-2*d[k]/delta[k]for k in range(3)]
for name,aa,ee,ds,gg in [('primal',ap,ep,d,[1,1,1]),('dual',ad,ed,dd,g)]:
 t0=time.time();N,W,F,G=envelope(aa,ee,ds,gg);t1=time.time();res=s.Poly(s.resultant(F.as_expr(),G.as_expr(),y),x);fac=s.factor_list(res)[1];base=s.Poly(s.resultant(N.as_expr(),W.as_expr(),y),x);clean=res.sqf_part().exquo(s.gcd(res.sqf_part(),base.sqf_part()));
 out={'role':name,'a':[str(k)for k in aa],'e':[str(k)for k in ee],'d':[str(k)for k in ds],'g':[str(k)for k in gg],'N':str(N.as_expr()),'W':str(W.as_expr()),'F':str(F.as_expr()),'G':str(G.as_expr()),'build_seconds':t1-t0,'elimination_seconds':time.time()-t1,'resultant_degree':res.degree(),'factor_degrees':[(p.degree(),m)for p,m in fac],'clean_resultant':str(clean.as_expr()),'clean_factors':[{'degree':p.degree(),'polynomial':str(p.as_expr()),'real_root_count':p.count_roots(-s.oo,s.oo)}for p,m in s.factor_list(clean)[1]],'model_A':str(A),'model_c':[str(k)for k in c],'model_d':[str(k)for k in d]}
 (root/f'results/{name}_weighted_envelope.json').write_text(json.dumps(out,indent=2,default=int)); print(name,'seconds',time.time()-t0,'factor degrees',out['factor_degrees'],'real',[ (v['degree'],v['real_root_count'])for v in out['clean_factors']],flush=True)
