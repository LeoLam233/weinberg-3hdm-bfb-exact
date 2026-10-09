"""Floating implementation of the sextic/current criterion on four charts.
NOT an exact sign/real-root engine. The theorem does not rely on floating output.
"""
from pathlib import Path
import itertools,json
import numpy as np
from numpy.polynomial import polynomial as pol
from scipy.optimize import root
from weinberg import Model,PAIRS,hvec,hmat
P=Path(__file__).resolve().parents[1]

def trig_coefficients(z):
    A,B,C=z; Ar,Ai=A.real,A.imag;Br,Bi=B.real,B.imag;Cr,Ci=C.real,C.imag
    return np.array([[Ai+Ci+Bi,2*(Ar-Cr),-Ai-Ci+Bi],
                     [2*(Br+Cr),4*Ci,2*(Br-Cr)],
                     [Ai-Ci-Bi,2*(Ar+Cr),-Ai+Ci-Bi]],float)

def sylvester_resultant(F,G):
    a,b,c=F[2],F[1],F[0];d,e,f=G[2],G[1],G[0];z=np.zeros(3)
    M=[[a,b,c,z],[z,a,b,c],[d,e,f,z],[z,d,e,f]]
    ans=np.zeros(9)
    for perm in itertools.permutations(range(4)):
        sgn=(-1)**sum(perm[i]>perm[j] for i in range(4)for j in range(i+1,4))
        prod=np.array([sgn],float)
        for i in range(4):prod=pol.polymul(prod,M[i][perm[i]])
        ans[:len(prod)]+=prod
    return ans

def phase_roots(a,e,d,g):
    M=np.array([[e[1]*d[0],-e[0]*d[1],a[0]*d[2]-d[1]*d[0].conjugate()],
                [e[2]*d[0],d[0]*d[2]-a[1]*d[1],e[0]*d[2]],
                [a[2]*d[0]-d[1]*d[2].conjugate(),-e[2]*d[1],e[1]*d[2]]])
    F0=trig_coefficients(g[0]*M[1]-g[1]*M[0]);G0=trig_coefficients(g[0]*M[2]-g[2]*M[0]);out=[]
    remainders=[]
    for flip_t,flip_u in itertools.product((False,True),repeat=2):
        F=F0.copy();G=G0.copy()
        if flip_t:F=F[:,::-1];G=G[:,::-1]
        if flip_u:F=F[::-1,:];G=G[::-1,:]
        F/=np.max(np.abs(F));G/=np.max(np.abs(G))
        res=sylvester_resultant(F,G);sextic,rem=pol.polydiv(res,np.array([1.,0.,1.]))
        remainders.append(float(np.max(np.abs(rem))))
        if np.max(np.abs(sextic))<1e-14:continue
        sextic=pol.polytrim(sextic,tol=1e-13*np.max(np.abs(sextic)))
        tr=pol.polyroots(sextic)
        for tt in tr:
            if abs(tt.imag)>2e-6 or abs(tt.real)>1.0001:continue
            tv=float(tt.real);ff=np.array([pol.polyval(tv,row)for row in F]);gg=np.array([pol.polyval(tv,row)for row in G])
            use=ff if np.linalg.norm(ff)>np.linalg.norm(gg)else gg
            for uu in pol.polyroots(pol.polytrim(use,tol=1e-13)):
                if abs(uu.imag)>2e-6 or abs(uu.real)>1.0001:continue
                def fun(z):
                    t,u=z;return [sum(pol.polyval(t,row)*u**k for k,row in enumerate(F)),sum(pol.polyval(t,row)*u**k for k,row in enumerate(G))]
                sol=root(fun,[tv,float(uu.real)],tol=1e-12)
                tv2,uv2=sol.x
                if np.max(np.abs(fun(sol.x)))>2e-8 or abs(tv2)>1.0002 or abs(uv2)>1.0002:continue
                th2=2*np.arctan2(1.,tv2)if flip_t else 2*np.arctan2(tv2,1.)
                th3=2*np.arctan2(1.,uv2)if flip_u else 2*np.arctan2(uv2,1.)
                th=np.array([th2,th3]);th=(th+np.pi)%(2*np.pi)-np.pi
                if any(np.linalg.norm(np.angle(np.exp(1j*(th-old))))<2e-6 for old in out):continue
                out.append(th)
    return out,remainders

def weighted_spectrum(a,e,d,g):
    a,e,d,g=map(np.asarray,(a,e,d,g));out=[]
    for i in range(3):out.append({'r':np.eye(3)[i],'theta':np.zeros(3),'value':float(a[i]/(2*g[i]**2)),'support':[i]})
    for k,(i,j) in enumerate(PAIRS):
        for sign in [-1.,1.]:
            off=(e[k]+sign*abs(d[k]))/2;bi=a[i]/2;bj=a[j]/2
            n=np.array([bj*g[i]-off*g[j],bi*g[j]-off*g[i]]);W=bj*g[i]**2-2*off*g[i]*g[j]+bi*g[j]**2
            if abs(W)<1e-12 or abs(n.sum())<1e-12:continue
            rr=n/n.sum()
            if min(rr)<=1e-8:continue
            r=np.zeros(3);r[[i,j]]=rr;theta=np.zeros(3);theta[j]=np.angle(sign*d[k].conjugate()/abs(d[k]))
            out.append({'r':r,'theta':theta,'value':float((bi*bj-off**2)/W),'support':[i,j]})
    phases,rems=phase_roots(a,e,d,g)
    for th in phases:
        angles=np.array([th[0],th[1],th[1]-th[0]]);curr=np.imag(d*np.exp(1j*angles));j=np.array([curr[2],-curr[1],curr[0]])
        if abs(j.sum())<1e-10:continue
        r=j/j.sum()
        if min(r)<=1e-8 or abs(g@r)<1e-9:continue
        B=np.diag(a/2)
        for k,(i,l)in enumerate(PAIRS):B[i,l]=B[l,i]=(e[k]+np.real(d[k]*np.exp(1j*angles[k])))/2
        out.append({'r':r,'theta':np.r_[0,th],'value':float(r@B@r/(g@r)**2),'support':[0,1,2]})
    for v in out:
        w=np.sqrt(v['r'])*np.exp(.5j*v['theta']);v['P']=np.outer(w.conj(),w)
    return out,{'real_phase_roots_found':len(phases),'maximum_base_factor_remainder':max(rems)}

def full_candidates(model):
    R=np.linalg.inv(model.matrix());G=R[:3,:3];g=G@np.ones(3);beta=sum(g);delta=model.c**2-abs(model.d)**2
    ns,nd=weighted_spectrum(model.a,model.b+model.c,model.d,np.ones(3))
    ds,dd=weighted_spectrum(2*np.diag(G),np.array([2*(G[i,j]+model.c[k]/delta[k])for k,(i,j)in enumerate(PAIRS)]),-2*model.d/delta,g)
    candidates=[{'value':v['value'],'K':v['P'],'constructor':'neutral','support':v['support']}for v in ns]
    RI=hmat(R@hvec(np.eye(3)))
    purity_errors=[];kernel_errors=[]
    for v in ds:
        PP=v['P'];RP=hmat(R@hvec(PP));aa=float(g@v['r']);pp=float(np.trace(PP@RP).real);D=beta*pp-aa*aa
        if abs(D)<1e-12:continue
        K=(pp*RI-aa*RP)/D
        # Scalar purity filter reconstructed independently from three scalar products.
        b2=float(np.trace(RI@RI).real);a2=float(np.trace(RI@RP).real);p2=float(np.trace(RP@RP).real)
        purity=(pp*pp*b2-2*pp*aa*a2+aa*aa*p2)/(D*D)
        direct_purity=float(np.trace(K@K).real)
        purity_errors.append(abs(purity-direct_purity));kernel_errors.append(float(np.linalg.norm(K@PP)))
        if purity>1+2e-7:continue
        # These redundant tests diagnose implementation/numerical error; not substitutes for proof.
        if np.linalg.norm(K@PP)>2e-6 or np.min(np.linalg.eigvalsh(K))<-2e-7:continue
        candidates.append({'value':float(pp/(2*D)),'K':K,'constructor':'charged-dual','support':v['support'],'purity':purity})
    return candidates,{'primal':nd,'dual':dd,'max_purity_identity_error':max(purity_errors,default=0.),'max_kernel_residual':max(kernel_errors,default=0.)}

if __name__=='__main__':
    records=json.loads((P/'results/duality_probe.json').read_text())['records'];out=[]
    for rec in records[:12]:
        model=Model(np.array(rec['a']),np.array(rec['b']),np.array(rec['c']),np.array(rec['d_real'])+1j*np.array(rec['d_imag']))
        cc,diag=full_candidates(model);best=min(cc,key=lambda c:c['value'])
        item={'index':rec['index'],'sextic_spectrum_minimum_found':best['value'],'direct_field_minimum_found':rec['minimum_found'],'difference':float(best['value']-rec['minimum_found']),'winning_constructor':best['constructor'],'winning_support':best['support'],'winning_eigenvalues':np.linalg.eigvalsh(best['K']).tolist(),'physical_candidates_found':len(cc),'diagnostics':diag}
        assert abs(item['difference'])<2e-7
        out.append(item);(P/'results/hexagon_numeric.json').write_text(json.dumps({'scope':'Floating diagnostic; no exact real-root/sign isolation','models':out},indent=2));print(item,flush=True)
