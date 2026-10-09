# Exact destructive examples and route history

These results are internal derivations, not literature quotations. They are
supplementary to the unchanged W3-BFB-EXACT contract. The main theorem is in
`THEOREM.md`; no collection of these examples alone constitutes its completion.
Pair order is 12,13,23 throughout.

## 1. Neutral positivity misses a charged instability

Take \(a=(1,1,1), b=(-1,-1,-1), c=(1,1,1), d=(1/2,1/2,1/2)\).
For a neutral matrix \(K_{ij}=\bar w_iw_j\), set \(z_i=w_i^2\). Then
\[
 f_N=\tfrac14 z^\dagger(I+J)z>0\quad(z\ne0),
\]
since the eigenvalues of \((I+J)/4\) are \(1,1/4,1/4\).
Nevertheless the real doublets given as columns of
\[
 \Phi=\begin{pmatrix}
 1/2&-1/2&0\\1/(2\sqrt3)&1/(2\sqrt3)&-1/\sqrt3
 \end{pmatrix}
\]
have \(\operatorname{tr}K=1\) and \(f=-1/24\). Both statements are exact
symbolic checks in `exact_checks.py`.

### The complete minimum of this benchmark is -7/60

Write \(K=A+iB\), with \(A\) real symmetric and \(B\) real antisymmetric;
write \(B\) as the cross-product matrix of a real vector \(z\), up to the
irrelevant sign convention. Direct expansion gives
\[
 \det K=\det A-z^TAz,
\]
\[
 f=\tfrac34\operatorname{tr}A^2+\tfrac14\sum_iA_{ii}^2
       +\tfrac12|z|^2-\tfrac12,
 \qquad \operatorname{tr}A=1.
\]
Because \(K\succeq0\), also \(A\succeq0\). Let its eigenvalues be
\(t,u,v\), with \(t\) largest. Then \(t\ge1/3\) and the rank constraint gives
\(tuv=z^TAz\le t|z|^2\), hence \(|z|^2\ge uv\). Also
\(\sum A_{ii}^2\ge1/3\) and \(uv\le(1-t)^2/4\). Therefore
\[
 f\ge\tfrac34t^2+\tfrac12(1-t)^2-\tfrac5{12}
  =\tfrac54(t-\tfrac25)^2-\tfrac7{60}.
\]
The cancellation when \(uv=0\) remains valid because \(t>0\).
Let \(z_0=(1,1,1)^T/\sqrt3\),
\(e_1=(1,-1,0)^T/\sqrt2\),
\(e_2=(1,1,-2)^T/\sqrt6\), and \(v_0=(e_1+ie_2)/\sqrt2\). Then
\[
 K_*=\tfrac25z_0z_0^T+\tfrac35v_0v_0^\dagger
\]
has eigenvalues \((0,2/5,3/5)\), diagonal entries \(1/3\), and achieves
\(-7/60\). Thus the lower bound and attainment match exactly. The determinant
and energy decompositions were independently checked with arbitrary symbolic
entries in `face_and_infinitesimal_checks.py`.

## 2. The simple moment relaxation is not complete

Introduce proposed second-moment coordinates
\(A_i=r_i^2\), \(B_{ij}=r_ir_j\), \(C_{ij}=|K_{ij}|^2\),
\(D_{ij}=K_{ij}^2\), or their convex mixtures. Necessary block-PSD constraints use matrices \(R,T,Z\) with diagonals
\(A_i\) and off-diagonals respectively \(B_{ij},2C_{ij}-B_{ij},D_{ij}\),
together with \(B_{ij}\ge C_{ij}\ge|D_{ij}|\). Here \(R\) is a radial
Gram matrix, \(Z\) is the squared complex Gram matrix, and \(T\) is the
Gram matrix of the real Pauli/Bloch vectors of the rank-one two-by-two matrices
\(\Phi_i\Phi_i^\dagger\). Indeed their dot product is
\(2|K_{ij}|^2-r_ir_j\). These necessary constraints survive convex mixtures.
The following point obeys all of them:
\[
 A_i=B_{ij}=1/9,\quad C_{ij}=1/36,\quad D_{ij}=-1/36.
\]
The three matrices are \(R=J/9\), \(T=I/6-J/18\), and
\(Z=5I/36-J/36\), all positive semidefinite. The matrix with off-diagonals
\(C_{ij}\) is \((R+T)/2=I/12+J/36\) and is positive semidefinite as well. The normalization is
\(\sum A_i+2\sum B_{ij}=1\). In the model of Section 1 its objective is
\(-1/8\), strictly below the true minimum \(-7/60\), by \(1/120\).
Thus these necessary moment constraints omit joint physical compatibility.
Adding \(7(\operatorname{tr}K)^2/60\) makes the physical form nonnegative while
this outer point still has negative objective.

This refutes this particular block-moment completion, not every convex lift,
SOS certificate or higher-order relaxation. The stronger global theorem was
obtained by changing representation rather than calling this gap exhaustion.

## 3. Fixed-radius phase convexity does not justify global interchange

For fixed positive amplitudes, the three-phase quadratic objective has an exact
complex correlation-matrix relaxation. If an extreme Hermitian correlation
matrix of size three had rank \(r\ge2\), Hermitian perturbations on its support
would have dimension \(r^2>3\). A nonzero perturbation could preserve all three
diagonal constraints, with both small signs remaining positive semidefinite.
This contradicts extremality. Thus all extreme matrices have rank one.

The radial variables cannot simply be merged into this exact phase relaxation.
An exact neutral outer-moment example is in `closure_audit_checks.py`. It uses
\(\rho=\sqrt{10}/5\), \(a=1/20\), \(e=\rho-1/20\), and cyclic
\(d_{12}=d_{23}=-3/5+i/5\), \(d_{13}=\bar d_{12}\).
The A4 neutral conditions give a nonnegative form (pair boundary
\(a+e-|d|=0\), uniform coefficient \(2\rho-5/4>0\)). A relaxed point with
radial off-diagonals \(\rho\), phase entries \((3+i)/5\) cyclically, and
normalization \(3+6\rho\) has objective
\[
 -13/120+\sqrt{10}/30<0.
\]
The phase loop prevents a physical radial/phase decomposition. The A4 neutral
characterization is imported at its neutral scope from Buskin–Ivanov,
arXiv:2104.11428; the displayed radical signs and outer matrices were checked
exactly. This auxiliary route is not used as a premise of the main theorem.

## 4. Singular charged denominator with a nonreal loop

This is a negative control against assuming that invertible \(L\) and a
nonreal phase loop automatically imply \(D_P\ne0\).
Let
\[
 A=\tfrac19\begin{pmatrix}19&1&13\\1&19&13\\13&13&25\end{pmatrix},
 \quad G=A^{-1},\quad g=(2/3,2/3,-1/3)^T,\quad\beta=1.
\]
Specify the inverse operator \(R\) by this diagonal block \(G\), off-diagonal
scalar coefficients \(c^R=(-1/2,-1/2,-1/2)\), and complex coefficients
\(d^R=(i/5,-i/20,i/20)\), using
\((RX)_{ij}=c^R_{ij}X_{ij}+\bar d^R_{ij}\bar X_{ij}\).
All blocks are invertible. Equivalently the original operator has
\[
 c=(-50/21,-200/99,-200/99),\quad
 d=(-20i/21,20i/99,-20i/99).
\]
Let \(z=(1,1,2)^T/\sqrt6\), \(P=zz^T\), and
\[
 K=RI+RP=
 \begin{pmatrix}
 5/12&-1/12-i/30&-1/6+i/60\\
 -1/12+i/30&5/12&-1/6-i/60\\
 -1/6-i/60&-1/6+i/60&1/6
 \end{pmatrix}.
\]
Then \(KP=0\), \(\operatorname{tr}K=1\), and its eigenvalues are
\(0,1/2\pm1/(10\sqrt6)\), so it is physical. Yet
\[
 a_P=p_P=D_P=0,\quad LK=I+P,\quad f(K)=1/2.
\]
The weighted dual loop is \((2d^R_{12})(2d^R_{23})\overline{2d^R_{13}}=-i/250\),
not real. The point is genuinely exceptional. Its existence is why the
pole-zero genericity lemma and the positive infinitesimal completion are
load-bearing. `final_destructive_checks.py` checks the entire construction.

## 5. Sparse kernels and exact zero-boundary recovery

For
\(A=\begin{pmatrix}a&u&v\\u&b&w\\v&w&c\end{pmatrix}\) and kernel
\(P=e_1e_1^T\), the dual reconstruction simplifies identically to
\[
 D_P=\frac{b+c-2w}{\det A},\quad
 K=\operatorname{diag}\left(0,\frac{c-w}{b+c-2w},
                              \frac{b-w}{b+c-2w}\right),
 \quad f(K)=\frac{bc-w^2}{2(b+c-2w)}.
\]
This agrees with independent two-radius minimization.

Take
\[
 A_0=\begin{pmatrix}3&2&2\\2&1&-2\\2&-2&1\end{pmatrix},\quad
 c=(1,2,3),\quad d=(1/3+i/5,1/7-i/2,2/5+i/3).
\]
All \(c_{ij}>|d_{ij}|\), so off-diagonal Gram terms are nonnegative. With
\(r_1+r_2+r_3=1\),
\[
 \tfrac12r^TA_0r+\tfrac14
 =r_1(\tfrac52-\tfrac34r_1)+\tfrac34(r_2-r_3)^2.
\]
The exact minimum is \(-1/4\) at \(K=\operatorname{diag}(0,1/2,1/2)\).
Adding \((\operatorname{tr}K)^2/4\) gives a zero-boundary example with
\(p_P=0\) but \(D_P=-4/25\ne0\). Thus dividing by the candidate value or by
\(p_P\) would lose a legitimate boundary direction.

Under the full formal deformation of the zero model, let
\[
 b=3/2+2\epsilon_0+\epsilon_2,\quad
 c=3/2+2\epsilon_0+\epsilon_3,\quad
 w=-3/2+2\epsilon_0+\epsilon_6.
\]
The winning face remains strictly admissible and has
\[
 m_\epsilon=\frac{bc-w^2}{2(b+c-2w)},\quad
 r_2=\frac{c-w}{b+c-2w},\quad r_3=\frac{b-w}{b+c-2w}.
\]
Its excess over \(\epsilon_0\) starts with
\((\epsilon_2+\epsilon_3+2\epsilon_6)/8\). Its successive residue is
\(m=0\), \(K=\operatorname{diag}(0,1/2,1/2)\).
For global persistence, the strict margins \(c_{ij}>|d_{ij}|\) remain positive.
At fixed \(x=r_1\), unconstrained elimination of \(r_2\) gives
\(m(x)=m(0)+Lx+Qx^2\). At the undeformed point \(L=5/2\), \(Q=-3/4\),
so \(L+\min(Q,0)>0\) persists infinitesimally. The face minimizer stays inside
the face. Thus \(x=0\) remains globally minimizing; the exact residue check is
not merely a locally chosen algebraic branch.

## 6. Phase infinity and residue-order negative controls

Two exact full-support stationary configurations in
`final_destructive_checks.py` have, respectively,
\((\theta_2,\theta_3)=(\pi,\pi/2)\) and \((\pi,\pi)\). Both have
\(r=(1,1,1)/3\), \(\nu=1/3\), nonreal loop invariant and coprime phase forms.
The finite standard tangent chart misses them; the reciprocal charts recover
them exactly. Their complete coefficients and polynomials are in the JSON.

Selected-root residue tests include \(1\pm\sqrt\epsilon\), colliding branches
with distinct residue classes, a common power of \(\epsilon\), and
\((1-\sqrt{1-4\epsilon})/(2\epsilon)\to1\). For a nested example,
\(\sqrt{1+\epsilon_0}+\epsilon_1/\epsilon_0\) has residue one when
\(\epsilon_1\) is removed first; removing \(\epsilon_0\) first diverges.
These tests motivated the explicit selected-root, latest-infinitesimal-first
procedure in the theorem.

## 7. Independent affine-shift identity

For \(f_h=f+h(\operatorname{tr}K)^2\), operator inversion gives the
Sherman–Morrison relation
\[
 R_h=R-\frac{2h}{1+2h\beta}\,RI\otimes RI.
\]
Writing \(k=1+2h\beta\), it follows that
\[
 \beta_h=\beta/k,\quad a_h=a/k,\quad
 p_h=p-2ha^2/k,\quad D_h=D/k,
\]
\[
 K_h=K,\qquad E_h=E+h,\qquad\nu_h=k^2\nu-2hk.
\]
The exact symbolic identities were checked separately. Eight reruns of the
sextic prototype at positive and negative shifts agree with this transformation;
four are strictly positive examples. This is a normalization/covariance check,
not an additional independent global optimization theorem.

## 8. Other executed routes and their dispositions

The direct one-doublet route writes the remaining doublet as a real four-vector
\(x\). At fixed first two doublets the potential is
\(A_{12}+x^TBx+(a_3/2)\|x\|^4\). For \(a_3>0\), nonnegativity for all \(x\)
is equivalent to \(A_{12}\ge0\) and
\(B+\sqrt{2a_3A_{12}}I_4\succeq0\); for \(a_3=0\), require \(B\succeq0\)
and \(A_{12}\ge0\). Its structured four-by-four determinant was checked
symbolically. This route did not independently remove all remaining orientations.
It is a valid optional alternative reduction, not a missing premise of the
completed two-spectrum route.

The earlier adjugate-envelope approach produced higher-degree phase equations.
In one rational test, exact elimination and a subresultant gave the same sextic
as the later current reduction, including a rational polynomial for the other
phase modulo that sextic. The old route is retained as different-error evidence;
the general sextic theorem comes from the arbitrary-parameter current identity,
not from extrapolating that example.

An initial sixty-case moment LP experiment exceeded a tool limit before retaining
its final batch state. Later smaller moment probes completed and are recorded.
No claim is made that the interrupted sixty-case batch ran to completion or that
its volatile state was recovered. The convex-gap conclusions above rest on exact
analytic constructions, not on that incomplete batch.
