"""Exact sparse-kernel, zero-value, and formal-deformation identities.
Separate from floating root searches.
"""
from pathlib import Path
import json
import sympy as s
P=Path(__file__).resolve().parents[1]
Q=s.Rational;I=s.I
out={}
a,b,c,u,v,w=s.symbols('a b c u v w')
A=s.Matrix([[a,u,v],[u,b,w],[v,w,c]]);G=A.inv();g=G*s.ones(3,1);beta=sum(g);pp=G[0,0];al=g[0]
DD=s.factor(beta*pp-al**2)
assert s.factor(DD-(b+c-2*w)/A.det())==0
KD=s.simplify((pp*g-al*G[:,0])/DD)
expect=s.Matrix([0,(c-w)/(b+c-2*w),(b-w)/(b+c-2*w)])
assert s.simplify(KD-expect)==s.zeros(3,1)
assert s.factor(pp/(2*DD)-(b*c-w*w)/(2*(b+c-2*w)))==0
out['arbitrary_sparse_kernel_identity']={'D':'(b+c-2w)/det(A)','K_diagonal':list(map(str,expect)),'value':'(b*c-w*w)/(2*(b+c-2w))'}
# Exact negative and boundary minima with all off-diagonal penalties positive.
base=s.Matrix([[3,2,2],[2,1,-2],[2,-2,1]])
for label,shift in [('negative',Q(0)),('zero',Q(1,4))]:
 AA=base+2*shift*s.ones(3);GG=AA.inv();gg=GG*s.ones(3,1);be=sum(gg);p=GG[0,0];al=gg[0];D=s.simplify(be*p-al**2)
 kk=s.simplify((p*gg-al*GG[:,0])/D);value=s.simplify(p/(2*D))
 assert kk==s.Matrix([0,Q(1,2),Q(1,2)]) and value==-Q(1,4)+shift
 out[label+'_model']={'A':[[str(AA[i,j])for j in range(3)]for i in range(3)],'g':list(map(str,gg)),'p':str(p),'D':str(D),'value':str(value),'K_diagonal':list(map(str,kk))}
cc=[1,2,3];ds=[Q(1,3)+I/5,Q(1,7)-I/2,Q(2,5)+I/3]
assert all(s.simplify(cc[k]**2-ds[k]*s.conjugate(ds[k]))>0 for k in range(3))
x,y=s.symbols('x y',real=True);r=s.Matrix([x,y,1-x-y]);basef=s.expand((r.T*base*r)[0]/2)
# f >= -1/4 + x(5/2-3x/4), since the omitted square is nonnegative.
bound=-Q(1,4)+x*(Q(5,2)-Q(3,4)*x)
assert s.expand(basef-bound-Q(3,4)*(2*y-(1-x))**2)==0
out['global_face_minimum_proof_identity']='f_diagonal+1/4 = r1*(5/2-3*r1/4) + (3/4)*(r2-r3)^2; off-diagonal terms nonnegative'
# Singular B with nonsingular W must not be lost by dividing by det(B).
B=3*s.eye(3)-s.ones(3);gg=s.ones(3,1);adj=B.adjugate();W=(gg.T*adj*gg)[0];n=adj*gg
assert B.det()==0 and W!=0 and n/sum(n)==s.ones(3,1)/3
out['singular_B_valid_radial_stationary']={'detB':'0','W':str(W),'r':['1/3']*3,'nu':'0'}
# Exact multi-infinitesimal winning face for the zero-boundary example.
E=s.symbols('e0:16');a2=Q(3,2)+2*E[0]+E[2];a3=Q(3,2)+2*E[0]+E[3];b23=-Q(3,2)+2*E[0]+E[6]
den=a2+a3-2*b23;mm=s.factor((a2*a3-b23*b23)/(2*den))
rem=s.factor(mm-E[0]);assert not rem.has(E[0])
assert s.factor(rem-((Q(3,2)*(E[2]+E[3]+2*E[6])+E[2]*E[3]-E[6]**2)/(2*(6+E[2]+E[3]-2*E[6]))))==0
rr2=s.factor((a3-b23)/den);rr3=s.factor((a2-b23)/den)
limit_m=mm;limit_r=s.Matrix([0,rr2,rr3])
for eps in reversed(E):
 limit_m=s.simplify(s.limit(limit_m,eps,0,dir='+'))
 limit_r=limit_r.applyfunc(lambda z:s.simplify(s.limit(z,eps,0,dir='+')))
assert limit_m==0 and limit_r==s.Matrix([0,Q(1,2),Q(1,2)])
out['formal_zero_boundary_branch']={'minimum':str(mm),'minimum_minus_e0':str(rem),'r2':str(rr2),'r3':str(rr3),'successive_limit_value':'0','successive_limit_K_diagonal':['0','1/2','1/2'],'scope':'exact branch; global persistence follows from the strict off-diagonal and inward-radial margins described in the proof'}
# Independent A+iB determinant and energy identities behind the -7/60 test.
r1,r2,r3,x12,x13,x23,z1,z2,z3=s.symbols('r1 r2 r3 x12 x13 x23 z1 z2 z3',real=True)
AA=s.Matrix([[r1,x12,x13],[x12,r2,x23],[x13,x23,r3]])
BB=s.Matrix([[0,z3,-z2],[-z3,0,z1],[z2,-z1,0]]);zz=s.Matrix([z1,z2,z3]);KK=AA+I*BB
assert s.expand(KK.det()-AA.det()+(zz.T*AA*zz)[0])==0
f=sum(KK[i,i]**2/2 for i in range(3))
for i,j in ((0,1),(0,2),(1,2)):
 f+=-KK[i,i]*KK[j,j]+KK[i,j]*KK[j,i]+s.re(KK[i,j]**2)/2
rhs=Q(3,4)*s.trace(AA*AA)+Q(1,4)*sum(AA[i,i]**2 for i in range(3))+Q(1,2)*(zz.T*zz)[0]-s.trace(AA)**2/2
assert s.expand(f-rhs)==0
out['real_skew_determinant_identity']='det(A+iB)=det(A)-z^T A z'
out['real_skew_energy_identity']='f=3/4 tr(A^2)+1/4 sum A_ii^2+1/2 |z|^2-1/2(tr A)^2'
(P/'results/face_and_infinitesimal_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
