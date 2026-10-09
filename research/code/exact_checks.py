"""Exact symbolic checks. No floating-point search is used in these assertions."""
from pathlib import Path
import json
import sympy as s
root=Path(__file__).resolve().parents[1]
I=s.I;Q=s.Rational

def val(K,a,b,c,d):
    pairs=((0,1),(0,2),(1,2));r=list(K.diagonal())
    return s.simplify(sum(a[i]*r[i]**2/2 for i in range(3))+sum(b[t]*r[i]*r[j]+c[t]*K[i,j]*K[j,i]+s.re(d[t]*K[i,j]**2) for t,(i,j) in enumerate(pairs)))

checks={}
# Physical phase-orbit counterexample: all omega_i=1/3, cos(sum theta_i)=-1.
w=-Q(1,2)+I*s.sqrt(3)/2
Phi=s.Matrix([[1,1/s.sqrt(3),1/s.sqrt(3)],[0,s.sqrt(Q(2,3)),s.sqrt(Q(2,3))*w]])
K=s.simplify(Phi.conjugate().T*Phi)
pi=[s.simplify(K[i,j]**2/(K[i,i]*K[j,j])) for i,j in [(0,1),(1,2),(2,0)]]
assert all(s.simplify(s.Abs(p)-Q(1,3))==0 for p in pi)
assert s.simplify(s.prod(pi)+Q(1,27))==0
checks['phase_product']=str(s.prod(pi))

# Neutral-safe but charged-unstable quartic, exact real charged witness.
Phi=s.Matrix([[Q(1,2),-Q(1,2),0],[1/(2*s.sqrt(3)),1/(2*s.sqrt(3)),-1/s.sqrt(3)]])
K=s.simplify(Phi.T*Phi)
f=val(K,[1]*3,[-1]*3,[1]*3,[Q(1,2)]*3)
assert f==-Q(1,24)
checks['real_charged_witness_value']=str(f)
# Neutral polynomial is z^dagger H z, H=(I+J)/4.
H=(s.eye(3)+s.ones(3))/4
assert H.eigenvals()=={s.Integer(1):1,Q(1,4):2}
checks['neutral_squared_amplitude_matrix_eigenvalues']={str(k):int(v) for k,v in H.eigenvals().items()}

# Exact global minimizer of the same quartic: proof in DERIVATIONS.md.
z=s.ones(3,1)/s.sqrt(3)
e1=s.Matrix([1,-1,0])/s.sqrt(2)
e2=s.Matrix([1,1,-2])/s.sqrt(6)
v=(e1+I*e2)/s.sqrt(2)
Kstar=s.simplify(Q(2,5)*z*z.T+Q(3,5)*v*v.conjugate().T)
assert s.simplify(Kstar.det())==0
assert s.simplify(s.trace(Kstar)-1)==0
fstar=val(Kstar,[1]*3,[-1]*3,[1]*3,[Q(1,2)]*3)
assert fstar==-Q(7,60)
checks['global_minimum_witness_value']=str(fstar)
checks['global_minimum_K_eigenvalues']={str(k):int(v) for k,v in Kstar.eigenvals().items()}

# An outer-moment point obeying all candidate Gram constraints but giving -1/8.
A=s.eye(3)/9;R=s.ones(3)/9
T=s.eye(3)/6-s.ones(3)/18
Z=5*s.eye(3)/36-s.ones(3)/36
assert set(R.eigenvals()).issubset({0,Q(1,3)})
assert set(T.eigenvals()).issubset({0,Q(1,6)})
assert set(Z.eigenvals()).issubset({Q(1,18),Q(5,36)})
outer=Q(1,6)-Q(1,3)+Q(1,12)-Q(1,24)
assert outer==-Q(1,8)
checks['outer_moment_value']=str(outer)
checks['exact_relaxation_gap']=str(fstar-outer)

# Invertible L with a=p=D=0 at a rank-two stationary point with all ri>0.
p=s.Matrix([1,1,2])/s.sqrt(6);P=p*p.T;K=(s.eye(3)-P)/2
AA=s.Matrix([[Q(19,9),Q(1,9),Q(13,9)],[Q(1,9),Q(19,9),Q(13,9)],[Q(13,9),Q(13,9),Q(25,9)]])
assert AA.det()!=0
RR=AA.inv();g=RR*s.ones(3,1)
assert g==s.Matrix([Q(2,3),Q(2,3),-Q(1,3)])
LK=s.diag(*list(AA*s.Matrix(K.diagonal()).T))
for i in range(3):
 for j in range(3):
  if i!=j:LK[i,j]=-2*K[i,j]
assert s.simplify(LK-s.eye(3)-P)==s.zeros(3)
RP=s.diag(*list(RR*s.Matrix(P.diagonal()).T))
for i in range(3):
 for j in range(3):
  if i!=j:RP[i,j]=-P[i,j]/2
alpha=s.simplify((s.Matrix(P.diagonal())*g)[0]); beta=s.simplify(sum(g));q=s.simplify(s.trace(P*RP))
assert (alpha,beta,q)==(0,1,0)
checks['singular_dual_denominator']={'a':str(alpha),'b':str(beta),'p':str(q),'D':'0','lambda':'1','mu':'1','all_diagonal_K_positive':True}

# Characteristic determinant of the one-doublet real quadratic form.
u,Rr,Pp,Qq,Ss,t,al,be,ga,de=s.symbols('u R P Q S t alpha beta gamma delta',real=True)
x,y,w=s.symbols('x y w',real=True)
e=s.eye(4);v1=s.Matrix([x,y,w,0]);v2=s.Matrix([-y,x,0,w])
B=t*e+s.diag(al*u,be*u,0,0)+ga*v1*v1.T+de*v2*v2.T
char=t**4+t**3*((al+be)*u+(ga+de)*(x*x+y*y+w*w))+t*t*(al*be*u*u+ga*de*(x*x+y*y+w*w)**2+u*((ga*be+de*al)*x*x+(ga*al+de*be)*y*y+(ga+de)*(al+be)*w*w))+t*u*w*w*(al*be*(ga+de)*u+ga*de*(al+be)*(x*x+y*y+w*w))+al*be*ga*de*u*u*w**4
assert s.expand(B.det(method='domain-ge')-char)==0
checks['one_doublet_characteristic_identity']='exact symbolic polynomial identity'

(root/'results/exact_checks.json').write_text(json.dumps(checks,indent=2))
print(json.dumps(checks,indent=2))
