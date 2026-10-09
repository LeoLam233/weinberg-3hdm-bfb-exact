"""Exact recovery of a generic full-support sextic critical set in the recorded neutral example."""
from pathlib import Path
import sympy as s,json,time
P=Path(__file__).resolve().parents[1];j=json.loads((P/'results/envelope_input.json').read_text());x,y,v=s.symbols('x y v',real=True)
N,W,F,G=[s.sympify(j[k],locals={'x':x,'y':y}) for k in ['N','W','F','G']]
q=next(p for p,m in s.factor_list(s.Poly(s.sympify(j['clean_x_resultant'],locals={'x':x}),x))[1] if p.degree()==6)
# Low-degree factors after dividing the radial cofactor factors.
f=next(p.as_expr()for p,m in s.factor_list(s.Poly(F,x,y))[1] if p.degree_list()==(4,4))
g=next(p.as_expr()for p,m in s.factor_list(s.Poly(G,x,y))[1] if p.degree_list()==(4,4))
t=time.time();ss=s.subresultants(f,g,y)
def modq(E):
 return s.Poly(E,y).from_dict({mon:s.rem(co,q.as_expr(),x)for mon,co in s.Poly(E,y).terms()},y).as_expr()
last=None
for h in ss:
 hh=s.Poly(modq(h),y)
 print('subres degree',s.degree(h,y),'reduced degree',hh.degree(),flush=True)
 if not hh.is_zero:last=hh
assert last.degree()==1
u_num=-last.nth(0);u_den=last.nth(1)
# Invert in the quotient field Q[x]/q. Keep the expression small.
u=s.rem(u_num*s.invert(u_den,q.as_expr(),x),q.as_expr(),x)
assert s.rem(s.Poly(f,y).eval(u),q.as_expr(),x)==0
assert s.rem(s.Poly(g,y).eval(u),q.as_expr(),x)==0
nv=s.rem(s.Poly(N,y).eval(u),q.as_expr(),x);wv=s.rem(s.Poly(W,y).eval(u),q.as_expr(),x)
val=s.rem(nv*s.invert(wv,q.as_expr(),x),q.as_expr(),x)
vp=s.Poly(s.resultant(q.as_expr(),s.together(v-val),x),v).clear_denoms()[1].primitive()[1]
sols=[]
for (lo,hi),mul in q.intervals(eps=s.Rational(1,10**20)):
 xx=(lo+hi)/2; yy=s.N(u.subs(x,xx),18);vv=s.N(val.subs(x,xx),18)
 sols.append({'x_interval':[str(lo),str(hi)],'y_approx':str(yy),'value_approx':str(vv)})
out={'seconds':time.time()-t,'q_sextic':str(q.as_expr()),'y_as_polynomial_mod_q':str(u),'value_as_polynomial_mod_q':str(val),'critical_value_polynomial':str(vp.as_expr()),'value_polynomial_degree':vp.degree(),'exact_substitution_checks':True,'root_intervals':sols,'scope':'This generic neutral test case only. Not a universal degree-six proof; not full charged/degenerate coverage.'}
(P/'results/subresultant_probe.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:z for k,z in out.items()if not k.endswith('polynomial_mod_q')},indent=2))
