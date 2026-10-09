"""Different-error, exact field-space and exceptional-jet identities."""
from pathlib import Path
import sympy as s
import json
OUT=Path(__file__).resolve().parents[1]
I=s.I;Q=s.Rational
pairs=((0,1),(0,2),(1,2))
a=s.symbols('a0:3',real=True);b=s.symbols('b0:3',real=True);c=s.symbols('c0:3',real=True)
dx=s.symbols('dx0:3',real=True);dy=s.symbols('dy0:3',real=True);d=[dx[k]+I*dy[k]for k in range(3)]
x=s.symbols('x0:6',real=True);y=s.symbols('y0:6',real=True)
Phi=s.Matrix(2,3,[x[k]+I*y[k]for k in range(6)]);K=Phi.conjugate().T*Phi
A=s.diag(*a)
for k,(ii,jj)in enumerate(pairs):A[ii,jj]=A[jj,ii]=b[k]
LK=s.diag(*(A*s.Matrix([K[i,i]for i in range(3)])))
f=sum(a[i]*K[i,i]**2/2 for i in range(3))
for k,(ii,jj)in enumerate(pairs):
    f+=b[k]*K[ii,ii]*K[jj,jj]+c[k]*K[ii,jj]*K[jj,ii]+(d[k]*K[ii,jj]**2+s.conjugate(d[k])*K[jj,ii]**2)/2
    LK[ii,jj]=c[k]*K[ii,jj]+s.conjugate(d[k])*K[jj,ii];LK[jj,ii]=s.conjugate(LK[ii,jj])
assert s.expand(f-s.trace(K*LK)/2)==0
fieldgrad=2*Phi*LK
for k in range(6):
    i,j=divmod(k,3)
    assert s.expand(s.diff(f,x[k])-s.re(s.expand_complex(fieldgrad[i,j])))==0
    assert s.expand(s.diff(f,y[k])-s.im(s.expand_complex(fieldgrad[i,j])))==0
# Euler normalization fixes lambda=2f on tr(K)=1.
assert s.expand(sum(x[k]*s.diff(f,x[k])+y[k]*s.diff(f,y[k])for k in range(6))-4*f)==0
# An explicit symbolic right inverse for the value + radial first-jet map on a=0.
# delta B=(ell 1^T+1 ell^T)/2 gives delta p=(ell.r)(1.r).
r=s.Matrix(s.symbols('r0:3',real=True));ell=s.Matrix(s.symbols('l0:3',real=True));one=s.ones(3,1)
DB=(ell*one.T+one*ell.T)/2
assert s.expand((r.T*DB*r)[0]-(ell.T*r)[0]*(one.T*r)[0])==0
# For tangent v with sum v=0, derivative at sum r=1 is ell.v:
v1,v2=s.symbols('v1 v2');v=s.Matrix([v1,v2,-v1-v2]);rr=s.Matrix([r[0],r[1],1-r[0]-r[1]])
assert s.expand(2*(v.T*DB*rr)[0]-(ell.T*v)[0])==0
# Phase jets: arbitrary current variations on a spanning tree 12,23.
r1,r2,r3=s.symbols('R1 R2 R3',nonzero=True)
phasejet=s.Matrix([[-r1*r2,r2*r3],[0,-r2*r3]])
assert s.factor(phasejet.det())==r1*r2**2*r3
# Common p shift with g held fixed is an allowed weighted coefficient direction.
# delta alpha_i=2eta and delta e_ij=2eta gives delta B=eta J.
eta=s.symbols('eta');J=eta*s.ones(3)
assert s.expand((rr.T*J*rr)[0]-eta)==0
# Rephasing covariance is exact in rational unit phases, all symbolic couplings/fields.
ph=[Q(3,5)+4*I/5,Q(5,13)+12*I/13,Q(8,17)+15*I/17]
DK=s.diag(*ph).conjugate()*K*s.diag(*ph)
fd=sum(a[i]*DK[i,i]**2/2 for i in range(3))
for k,(ii,jj)in enumerate(pairs):
    phase=s.conjugate(ph[ii])*ph[jj];dp=d[k]*s.conjugate(phase)**2
    fd+=b[k]*DK[ii,ii]*DK[jj,jj]+c[k]*DK[ii,jj]*DK[jj,ii]+(dp*DK[ii,jj]**2+s.conjugate(dp)*DK[jj,ii]**2)/2
assert s.expand(fd-f)==0
res={'full_field_scope':'12 real independent field coordinates, all 15 symbolic real couplings','energy_operator_identity':True,'real_field_derivative_identities_checked':12,'Euler_degree_four_identity':True,'radial_value_jet_right_inverse':'delta B=(ell 1^T+1 ell^T)/2; on sum r=1, delta p=ell.r','phase_tree_jet_minor':'r1*r2^2*r3, nonzero on full support','constant_shift_with_g_fixed':'delta alpha=2 eta, delta e=2 eta, delta d=0; p -> p+eta on sum r=1','rephasing_covariance':'exact rational unit phases, arbitrary symbolic fields/couplings'}
(OUT/'results/field_and_genericity_checks.json').write_text(json.dumps(res,indent=2))
print(json.dumps(res,indent=2))
