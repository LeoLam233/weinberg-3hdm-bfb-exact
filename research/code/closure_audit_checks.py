"""Exact destructive/reconstruction checks for the analytic criterion.
This is not a formal proof assistant and does not implement the full criterion.
"""
from pathlib import Path
import json
import sympy as s
P=Path(__file__).resolve().parents[1]
Q=s.Rational; I=s.I
out={}
# The fifteen inverse-operator coordinates really give independent weighted data.
z=s.symbols('G11 G22 G33 G12 G13 G23 c12 c13 c23 x12 x13 x23 y12 y13 y23')
G11,G22,G33,G12,G13,G23,*_=z
G=s.Matrix([[G11,G12,G13],[G12,G22,G23],[G13,G23,G33]])
alpha=[2*G[i,i] for i in range(3)]
e=[2*(G[i,j]+z[6+k]) for k,(i,j) in enumerate(((0,1),(0,2),(1,2)))]
dxy=[2*z[k] for k in range(9,15)]
g=list(G*s.ones(3,1))
J=s.Matrix(alpha+e+dxy+g).jacobian(z)
assert J.det()!=0
out['dual_parameter_jacobian_determinant']=str(J.det())
# First-jet-preserving radial variations. Coordinate-free proof uses arbitrary S.
r=s.Matrix([Q(1,9),Q(2,9),Q(1,3)]); g=s.Matrix([2,-1,3])
assert (g.T*r)[0]==1
U=s.Matrix([[1,-3],[2,0],[0,2]])
assert g.T*U==s.zeros(1,2)
S=r.row_join(U);h1,h2,h3=s.symbols('h1 h2 h3')
H=S.inv().T*s.Matrix([[0,0,0],[0,h1,h2],[0,h2,h3]])*S.inv()
assert s.simplify(H*r)==s.zeros(3,1)
assert s.simplify(U.T*H*U)==s.Matrix([[h1,h2],[h2,h3]])
out['radial_first_jet_preserving_variation']='Hr=0 and U^T H U=arbitrary symmetric 2x2, exact rational test'
# Exact full parameter-gradient rank at a diagnostic point, primal and mixed g.
a=s.symbols('a0:3');ee=s.symbols('e0:3');dx=s.symbols('dx0:3');dy=s.symbols('dy0:3')
x,y,t,u=s.symbols('x y t u',real=True)
ct=(1-t*t)/(1+t*t);st=2*t/(1+t*t);cu=(1-u*u)/(1+u*u);su=2*u/(1+u*u)
cs=[ct,cu,cu*ct+su*st];ss=[st,su,su*ct-cu*st]
rvec=s.Matrix([x,y,1-x-y]);bb=s.diag(*[q/2 for q in a])
for k,(i,j) in enumerate(((0,1),(0,2),(1,2))):bb[i,j]=bb[j,i]=(ee[k]+dx[k]*cs[k]-dy[k]*ss[k])/2
params=a+ee+dx+dy
jet_records=[]
for weights in (s.ones(3,1),s.Matrix([2,-1,3])):
 den=(weights.T*rvec)[0];num=(rvec.T*bb*rvec)[0];f=num/den**2
 jets=[s.diff(f,v) for v in (x,y,t,u)]
 mat=s.Matrix(jets).jacobian(params).subs({x:Q(1,6),y:Q(1,3),t:Q(2,3),u:-Q(1,2)})
 piv=mat.rref()[1];assert len(piv)==4
 minor=mat[:,list(piv)].det();assert minor!=0
 jet_records.append({'g':list(map(str,weights)),'rank':4,'pivot_columns':list(piv),'minor':str(minor)})
out['first_jet_rank_examples']=jet_records
# Euler/projective division identity: exact full-bidegree sample.
T0,T1,U0,U1=s.symbols('T0 T1 U0 U1')
mon=[T0**(4-i)*T1**i*U0**(4-j)*U1**j for i in range(5) for j in range(5)]
N=sum(((7*k+3)%19-9)*v for k,v in enumerate(mon));W=sum(((11*k+5)%23-11)*v for k,v in enumerate(mon))
raw=s.expand(W*s.diff(N,T1)-N*s.diff(W,T1));F,rem=s.div(raw,T0,T0,T1,U0,U1);assert rem==0
raw2=s.expand(W*s.diff(N,U1)-N*s.diff(W,U1));GG,rem=s.div(raw2,U0,T0,T1,U0,U1);assert rem==0
assert s.expand(T1*F+W*s.diff(N,T0)-N*s.diff(W,T0))==0
assert s.expand(U1*GG+W*s.diff(N,U0)-N*s.diff(W,U0))==0
out['projective_chart_identities']='exact divisibility and reciprocal-chart identities, all four charts'
# Exact A4 neutral moment gap, using explicit radicals, no floating sign decision.
rho=s.sqrt(10)/5;aa=Q(1,20);ev=rho-aa
R=s.eye(3)*(1-rho)+s.ones(3)*rho
Z=s.eye(3)
z12=(3+I)/5;z13=s.conjugate(z12);z23=z12
for (i,j),v in zip(((0,1),(0,2),(1,2)),(z12,z13,z23)):Z[i,j]=v;Z[j,i]=s.conjugate(v)
assert Z.charpoly().as_expr().expand()==s.expand((Z.charpoly().gen-Q(11,5))*(Z.charpoly().gen-(2+s.sqrt(3))/5)*(Z.charpoly().gen-(2-s.sqrt(3))/5))
assert Q(1,2)<rho<1
norm=3+6*rho
cost=s.simplify((3*aa/2+3*ev*rho+3*(-Q(2,5)))/norm)
assert s.simplify(cost-3*aa*(Q(1,2)-rho)/norm)==0
# 2rho-5/4>0 follows by squaring: 4rho^2 -25/16 =3/80>0.
assert s.simplify(4*rho**2-Q(25,16))==Q(3,80)
out['neutral_moment_gap']={'normalization':str(norm),'cost_exact':str(cost),'cost_negative':True,'uniform_minimum_coefficient_positive':'2 sqrt(10)/5 - 5/4 > 0','phase_flux':str(s.simplify(z12*z23*s.conjugate(z13)))}
# Bounded-root residue diagnostics: selected branches, collisions, removable poles.
t=s.symbols('epsilon',positive=True);X=s.symbols('X')
tests=[
 ('colliding_plus',(X-1)**2-t,1+s.sqrt(t),1),
 ('colliding_minus',(X-1)**2-t,1-s.sqrt(t),1),
 ('two_limits_minus',((X-2)**2-t)*((X+3)**2-t**2),-3+t,-3),
 ('two_limits_plus',((X-2)**2-t)*((X+3)**2-t**2),2-s.sqrt(t),2),
 ('bounded_pole_cancellation',t*X**2-X+1,(1-s.sqrt(1-4*t))/(2*t),1),
 ('common_epsilon_power',t**2*((X-2)**2-t),2+s.sqrt(t),2)]
res=[]
for name,poly,branch,expected in tests:
 assert s.simplify(poly.subs(X,branch))==0
 pp=s.Poly(s.expand(poly),t);power=min(k[0] for k,c in pp.terms())
 q=s.expand(poly/t**power).subs(t,0)
 lim=s.limit(branch,t,0,dir='+');assert lim==expected and s.simplify(q.subs(X,lim))==0
 roots=s.Poly(q,X).sqf_part().real_roots();roots=list(dict.fromkeys(roots));mids=[(roots[k]+roots[k+1])/2 for k in range(len(roots)-1)]
 bin_=sum(1 for m in mids if s.limit(branch-m,t,0,dir='+')>0)
 assert roots[bin_]==expected
 res.append({'name':name,'normalized_residue_polynomial':str(q),'selected_limit':str(lim),'number_of_distinct_real_residue_roots':len(roots)})
out['selected_bounded_root_residue_tests']=res
e0,e1=s.symbols('e0 e1',positive=True);branch=s.sqrt(1+e0)+e1/e0
assert s.limit(s.limit(branch,e1,0,dir='+'),e0,0,dir='+')==1
assert s.limit(branch,e0,0,dir='+')==s.oo
out['nested_limit_order_test']={'latest_first':'1','reverse_first_limit':'infinity; invalid order'}
# Dominance bound for the full fifteen independent perturbations.
assert 3*Q(1,2)+12*Q(1,4)==Q(9,2)
out['coefficient_monomial_uniform_l1_bound']='9/2'
(P/'results/closure_audit_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
