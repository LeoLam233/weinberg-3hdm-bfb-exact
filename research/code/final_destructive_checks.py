"""Exact adversarial checks for the current/sextic and charged reductions.
All checks are finite symbolic identities; they supplement, not replace, coverage proofs.
"""
from pathlib import Path
import json
import sympy as s
PTH=Path(__file__).resolve().parents[1]
I=s.I;Q=s.Rational
t,u=s.symbols('t u', real=True)
T0,T1,U0,U1=s.symbols('T0 T1 U0 U1')
pairs=((0,1),(0,2),(1,2))
def Cmat(a,e,d):
    return s.Matrix([[e[1]*d[0],-e[0]*d[1],a[0]*d[2]-d[1]*s.conjugate(d[0])],
    [e[2]*d[0],d[0]*d[2]-a[1]*d[1],e[0]*d[2]],
    [a[2]*d[0]-d[1]*s.conjugate(d[2]),-e[2]*d[1],e[1]*d[2]]])
def poly(row):
    A,B,C=row
    return s.expand((s.im(A)*(1-t*t)+2*s.re(A)*t)*(1+u*u)+(s.im(B)*(1-u*u)+2*s.re(B)*u)*(1+t*t)+s.im(C)*((1-t*t)*(1-u*u)+4*t*u)+2*s.re(C)*(u*(1-t*t)-t*(1-u*u)))
def homogeneous(p):
    return s.Poly(p,t,u).terms() and s.expand(sum(c*T1**i*T0**(2-i)*U1**j*U0**(2-j) for (i,j),c in s.Poly(p,t,u).terms()))
examples=[('one_phase_at_infinity',[3,4,5],[1,1,-Q(3,2)],[1-I,-1+2*I,-1-I/2],[-1,I,-I],{T0:0,T1:1,U0:1,U1:1}),
('two_phases_at_infinity',[3,4,5],[1,1,-5],[1-I,2+I,3+I],[-1,-1,1],{T0:0,T1:1,U0:0,U1:1})]
output={'phase_chart_checks':[]}
for name,a,e,d,ph,point in examples:
    C=Cmat(a,e,d);F=poly(C[1,:]-C[0,:]);G=poly(C[2,:]-C[0,:])
    assert s.gcd(F,G).is_number
    FH,GH=homogeneous(F),homogeneous(G)
    assert FH.subs(point)==0 and GH.subs(point)==0
    curr=[s.im(d[k]*ph[k]) for k in range(3)]
    j=s.Matrix([curr[2],-curr[1],curr[0]]); assert j==s.ones(3,1)
    B=s.diag(*[Q(x,2) for x in a])
    for k,(ii,jj) in enumerate(pairs): B[ii,jj]=B[jj,ii]=(e[k]+s.re(d[k]*ph[k]))/2
    assert B*s.ones(3,1)==s.ones(3,1)
    assert (s.ones(1,3)*B*s.ones(3,1))[0]/9==Q(1,3)
    assert s.im(d[0]*d[2]*s.conjugate(d[1]))!=0
    out={'name':name,'F':str(F),'G':str(G),'gcd':str(s.gcd(F,G)),'projective_coordinates':{str(k):v for k,v in point.items()},'current':str(j),'value':'1/3','loop_product':str(s.expand(d[0]*d[2]*s.conjugate(d[1]))),'real_root_preserved_by_reciprocal_chart':True}
    # Reciprocal chart polynomials evaluate at the correct finite point.
    FF=s.expand(t**2*F.subs(t,1/t));GG=s.expand(t**2*G.subs(t,1/t))
    if point[U0]==0:
        FF=s.expand(u**2*FF.subs(u,1/u));GG=s.expand(u**2*GG.subs(u,1/u));uv=0
    else:uv=1
    assert FF.subs({t:0,u:uv})==GG.subs({t:0,u:uv})==0
    output['phase_chart_checks'].append(out)
# D=0 remains possible even when the invariant complex loop has nonzero imaginary part.
A=s.Matrix([[19,1,13],[1,19,13],[13,13,25]])/9;G=A.inv()
g=G*s.ones(3,1);beta=sum(g)
z=s.Matrix([1,1,2])/s.sqrt(6);PP=z*z.T
cc=[-Q(1,2)]*3;dd=[I/5,-I/20,I/20]
def R(X):
    Y=s.diag(*(G*s.Matrix([X[i,i] for i in range(3)])))
    for k,(ii,jj) in enumerate(pairs):
        Y[ii,jj]=cc[k]*X[ii,jj]+s.conjugate(dd[k])*s.conjugate(X[ii,jj]);Y[jj,ii]=s.conjugate(Y[ii,jj])
    return s.simplify(Y)
RI=R(s.eye(3));RP=R(PP);K=s.simplify(RI+RP)
assert K*PP==s.zeros(3) and s.trace(K)==1
pa=s.simplify(s.trace(PP*RI));pp=s.simplify(s.trace(PP*RP));D=s.simplify(beta*pp-pa*pa)
assert pa==pp==D==0 and beta==1
x=s.symbols('x');cp=K.charpoly(x).as_expr()
assert s.factor(cp)==x*(600*x*x-600*x+149)/600
assert all(s.simplify(cc[k]**2-abs(dd[k])**2)>0 for k in range(3))
# Since LK=I+P, the exact potential value is tr(K(I+P))/2=1/2.
loop=s.expand((2*dd[0])*(2*dd[2])*s.conjugate(2*dd[1]));assert s.im(loop)!=0
output['D_zero_with_nonreal_loop']={'A':str(A),'G1':str(g),'K':str(K),'a':'0','p':'0','D':'0','beta':'1','eigenvalues':['0','1/2 - 1/(10*sqrt(6))','1/2 + 1/(10*sqrt(6))'],'characteristic_polynomial':str(s.factor(cp)),'weighted_dual_loop':str(loop),'charged_stationarity':'LK=I+P; f=1/2','all_inverse_off_blocks_invertible':True}
# Universal purity identity in a real self-adjoint vector space.
pa,pp,bb,b2,a2,p2=s.symbols('a p beta beta2 a2 p2',real=True)
DD=bb*pp-pa**2
assert s.expand((pp/DD)**2*b2+2*(pp/DD)*(-pa/DD)*a2+(-pa/DD)**2*p2-(pp**2*b2-2*pp*pa*a2+pa**2*p2)/DD**2)==0
c,dx,dy,xr,xi=s.symbols('c dx dy xr xi',real=True);d=dx+I*dy;xx=xr+I*xi;delta=c*c-dx*dx-dy*dy
rx=(c*xx-s.conjugate(d)*s.conjugate(xx))/delta
rrx=s.expand_complex((c*rx-s.conjugate(d)*s.conjugate(rx))/delta)
expected=((c*c+dx*dx+dy*dy)*xx-2*c*s.conjugate(d)*s.conjugate(xx))/delta**2
assert s.simplify(rrx-expected)==0
# Rank/kernel obligation is necessary before invoking purity.
assert s.trace((s.eye(3)/3)**2)==Q(1,3) and (s.eye(3)/3).det()!=0
bad=s.diag(-Q(1,4),0,Q(5,4));assert s.trace(bad**2)==Q(13,8)
output['purity_checks']={'arbitrary_scalar_identity':True,'arbitrary_complex_inverse_square_block_identity':True,'warning':'purity <= 1 does not enforce rank <= 2 without the separately proved kernel identity','full_rank_counterexample':'I/3 has purity 1/3','indefinite_rank_two_counterexample':'diag(-1/4,0,5/4) has purity 13/8'}
# Universal fixed base points and degree-eight resultant upper bound are checked at symbolic row-coefficient level.
AA=s.symbols('ar ai br bi cr ci',real=True);BB=s.symbols('dr di er ei fr fi',real=True)
F=poly([AA[0]+I*AA[1],AA[2]+I*AA[3],AA[4]+I*AA[5]])
H=poly([BB[0]+I*BB[1],BB[2]+I*BB[3],BB[4]+I*BB[5]])
for zz in [I,-I]:
    assert s.expand(F.subs({t:zz,u:zz}))==s.expand(H.subs({t:zz,u:zz}))==0
# Full symbolic resultant is inexpensive enough for six coefficients per row.
res=s.resultant(F,H,u);quot,rem=s.div(res,t*t+1,t)
assert s.expand(rem)==0 and s.degree(quot,t)<=6
output['universal_sextic']={'arbitrary_two_harmonic_rows':True,'degree_after_exact_base_factor_division':int(s.degree(quot,t)),'base_points':'(i,i),(-i,-i)','remainder':'0'}
(PTH/'results/final_destructive_checks.json').write_text(json.dumps(output,indent=2))
print(json.dumps(output,indent=2))
