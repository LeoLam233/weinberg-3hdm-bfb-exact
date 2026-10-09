"""Structured neutral/dual-neutral bivariate rational envelopes.
The all-parameter and singular-stratum coverage is NOT established by this file.
"""
from pathlib import Path
import json,time
import sympy as s
x,y=s.symbols('x y', real=True)

def envelope(a,e,d,g=(1,1,1)):
    ax=1+x*x;ay=1+y*y
    cx,sx=(1-x*x)/ax,2*x/ax
    cy,sy=(1-y*y)/ay,2*y/ay
    phases=[(cx,sx),(cy,sy),(cx*cy+sx*sy,sy*cx-cy*sx)]
    off=[]
    for k,(co,si) in enumerate(phases):
        off.append((e[k]+s.re(d[k])*co-s.im(d[k])*si)/2)
    z12,z13,z23=off
    m1,m2,m3=[v/2 for v in a]
    det=m1*m2*m3+2*z12*z13*z23-m1*z23*z23-m2*z13*z13-m3*z12*z12
    adj=s.Matrix([[m2*m3-z23*z23,z13*z23-m3*z12,z12*z23-m2*z13],[z13*z23-m3*z12,m1*m3-z13*z13,z12*z13-m1*z23],[z12*z23-m2*z13,z12*z13-m1*z23,m1*m2-z12*z12]])
    gg=s.Matrix(g);w=(gg.T*adj*gg)[0]
    N=s.Poly(s.cancel(det*ax**2*ay**2),x,y)
    W=s.Poly(s.cancel(w*ax**2*ay**2),x,y)
    gcd=s.gcd(N,W);N=N.exquo(gcd);W=W.exquo(gcd)
    Fx=N.diff(x)*W-N*W.diff(x);Fy=N.diff(y)*W-N*W.diff(y)
    chart=s.Poly(ax*ay,x,y)
    def strip(P):
        while True:
            q=s.gcd(P,chart)
            if q.total_degree()==0:break
            P=P.exquo(q)
        return P.clear_denoms()[1].primitive()[1]
    return N,W,strip(Fx),strip(Fy)

if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 a=[s.Rational(3,2),s.Rational(5,3),s.Rational(7,4)]
 e=[s.Rational(1,3),s.Rational(-2,5),s.Rational(3,7)]
 d=[s.Rational(2,3)+s.I/5,s.Rational(3,5)-s.I/7,s.Rational(-4,7)+s.I/3]
 t=time.time();N,W,F,G=envelope(a,e,d)
 inputs={'a':[str(v)for v in a],'e':[str(v)for v in e],'d':[str(v)for v in d],'normalization':'neutral f= r^T B(theta) r; r_1+r_2+r_3=1','N':str(N.as_expr()),'W':str(W.as_expr()),'F':str(F.as_expr()),'G':str(G.as_expr()),'N_degrees':N.degree_list(),'W_degrees':W.degree_list(),'F_degrees':F.degree_list(),'G_degrees':G.degree_list(),'build_seconds':time.time()-t,'resultant_status':'NOT STARTED'}
 (root/'results/envelope_input.json').write_text(json.dumps(inputs,indent=2))
 print('built',time.time()-t,'degrees',N.degree_list(),W.degree_list(),F.degree_list(),G.degree_list(),flush=True)
 inputs['resultant_status']='RUNNING';(root/'results/envelope_input.json').write_text(json.dumps(inputs,indent=2))
 t=time.time();R=s.Poly(s.resultant(F.as_expr(),G.as_expr(),y),x)
 inputs['resultant_status']='COMPUTED';inputs['resultant_seconds']=time.time()-t;inputs['resultant_degree']=R.degree();inputs['resultant']=str(R.as_expr());inputs['resultant_factor_degrees']=[(p.degree(),mult) for p,mult in s.factor_list(R)[1]]
 (root/'results/envelope_input.json').write_text(json.dumps(inputs,indent=2))
 print('resultant',time.time()-t,'degree',R.degree(),'factors',inputs['resultant_factor_degrees'],flush=True)
