"""Exact three-current / hexagon reduction; symbolic certificate and examples."""
from pathlib import Path
import json
import sympy as s
P=Path(__file__).resolve().parents[1]
I=s.I; Q=s.Rational
t,u=s.symbols('t u',real=True)
def phase_parts(t,u):
 dt=1+t*t;du=1+u*u
 ct=(1-t*t)/dt;st=2*t/dt;cu=(1-u*u)/du;su=2*u/du
 return [ct,cu,cu*ct+su*st],[st,su,su*ct-cu*st]
def current_matrix(a,e,d):
 return s.Matrix([[e[1]*d[0],-e[0]*d[1],a[0]*d[2]-d[1]*s.conjugate(d[0])],
                  [e[2]*d[0],d[0]*d[2]-a[1]*d[1],e[0]*d[2]],
                  [a[2]*d[0]-d[1]*s.conjugate(d[2]),-e[2]*d[1],e[1]*d[2]]])
def phase_polynomial(coeff,t=t,u=u):
 A,B,C=coeff
 Ar,Ai=s.re(A),s.im(A);Br,Bi=s.re(B),s.im(B);Cr,Ci=s.re(C),s.im(C)
 return s.expand((Ai*(1-t*t)+2*Ar*t)*(1+u*u)+(Bi*(1-u*u)+2*Br*u)*(1+t*t)+Ci*((1-t*t)*(1-u*u)+4*t*u)+2*Cr*(u*(1-t*t)-t*(1-u*u)))
def polynomials(a,e,d,g):
 M=current_matrix(a,e,d)
 f=phase_polynomial(g[0]*M[1,:]-g[1]*M[0,:]);h=phase_polynomial(g[0]*M[2,:]-g[2]*M[0,:])
 return s.Poly(f,t,u).clear_denoms()[1].primitive()[1].as_expr(),s.Poly(h,t,u).clear_denoms()[1].primitive()[1].as_expr()
# Identity 2B j = Im(M * [exp(i theta2),exp(i theta3),exp(i(theta3-theta2))]).
a=s.symbols('a0:3',real=True);e=s.symbols('e0:3',real=True);dx=s.symbols('x0:3',real=True);dy=s.symbols('y0:3',real=True)
d=[dx[k]+I*dy[k]for k in range(3)];cs,ss=phase_parts(t,u)
B=s.diag(*[x/2 for x in a]);curr=[dx[k]*ss[k]+dy[k]*cs[k]for k in range(3)]
for k,(i,j)in enumerate(((0,1),(0,2),(1,2))):B[i,j]=B[j,i]=(e[k]+dx[k]*cs[k]-dy[k]*ss[k])/2
j=s.Matrix([curr[2],-curr[1],curr[0]])
M=current_matrix(a,e,d)
H=s.Matrix([sum(s.re(M[k,l])*ss[l]+s.im(M[k,l])*cs[l] for l in range(3)) for k in range(3)])
for expression in 2*B*j-H:
 assert s.Poly(s.together(expression).as_numer_denom()[0],t,u,*a,*e,*dx,*dy).is_zero
records=[]
examples=[('reference_neutral',[Q(3,2),Q(5,3),Q(7,4)],[Q(1,3),-Q(2,5),Q(3,7)],[Q(2,3)+I/5,Q(3,5)-I/7,-Q(4,7)+I/3],[1,1,1]),
('mixed_weights',[Q(3,2),Q(5,3),Q(7,4)],[Q(1,3),-Q(2,5),Q(3,7)],[Q(2,3)+I/5,Q(3,5)-I/7,-Q(4,7)+I/3],[2,-1,3])]
for name,aa,ee,dd,gg in examples:
 F,G=polynomials(aa,ee,dd,gg)
 common=s.gcd(F,G);assert common==1
 resultant=s.resultant(F,G,u)
 R,rem=s.div(resultant,1+t*t,t);assert rem==0
 R=s.Poly(R,t).clear_denoms()[1].primitive()[1];assert R.degree()<=6
 fac=s.factor_list(resultant)
 # Universal nonreal base points; no physical phase is removed by this division.
 for z in [I,-I]:assert s.simplify(F.subs({t:z,u:z}))==0 and s.simplify(G.subs({t:z,u:z}))==0
 item={'name':name,'F':str(F),'G':str(G),'gcd':'1','sextic':str(R.as_expr()),'sextic_degree':R.degree(),'resultant_factor_degrees_multiplicities':[(s.degree(v,t),k)for v,k in fac[1]],'sextic_real_root_count':R.count_roots(-s.oo,s.oo),'loop_imaginary_part':str(s.im(dd[0]*dd[2]*s.conjugate(dd[1])))}
 # Compare with the independently obtained adjugate-envelope sextic.
 if name=='reference_neutral':
  old=65532894182001*t**6-846134370496944*t**5+2404104611159391*t**4+2245261288159824*t**3-463362875655073*t**2-249992387249952*t-20785328196111
  assert s.Poly(old,t).monic()==R.monic()
  item['matches_prior_adjugate_elimination_sextic_exactly']=True
 records.append(item)
res={'identity_scope':'arbitrary real symbolic alpha/e/Re d/Im d and rational phase charts','two_B_current_identity':'exact polynomial zero in all parameters','examples':records,'status':'new reduction under audit; no stand-alone full-criterion claim from this script'}
# Convert SymPy integers before JSON serialization.
(P/'results/hexagon_spectrum_probe.json').write_text(json.dumps(res,indent=2,default=lambda x:int(x)if isinstance(x,s.Integer)else str(x)))
print(json.dumps(res,indent=2,default=str))
