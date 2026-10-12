# A two-spectrum sextic criterion for the complex Weinberg 3HDM

**Research object:** W3-BFB-EXACT. **Original analytic draft:** 9 October 2026. **Integrated F002 manuscript revision:** 12 October 2026. **Status:** author-side prepublication revision; not human peer reviewed.

This revision integrates the original analytic argument, the confirmed corrections in `docs/ERRATA.md`, and the subsequently completed F002 Lean statements. The original research draft and frozen formal source remain unchanged. Formal verification and review status must be read from `verification/RELEASE_STATUS.json` and `docs/SCOPE.md`, not from superseded historical draft-status language. “Exact” denotes mathematical real-closed-field arithmetic, signs, finite-root interfaces and residue operations; neither the floating-point prototype nor this formal development is a compiled exact solver. The formal F002 layer gives an input-derived finite *program syntax and refinement theorem* under semantic exact-operation interfaces, not a verified concrete root-isolation backend. References to repository files are relative to the repository root.

## 1. Statement, normalization and geometric core

For three columns \(\Phi_i\in\mathbb C^2\), put
\(K_{ij}=\Phi_i^\dagger\Phi_j\), \(r_i=K_{ii}\), and consider
\[
f(K)=\frac12\sum_{i=1}^3a_i r_i^2+
\sum_{i<j}\{b_{ij}r_ir_j+c_{ij}|K_{ij}|^2+
\operatorname{Re}(d_{ij}K_{ij}^2)\}. \tag{1}
\]
The nine coefficients \(a_i,b_{ij},c_{ij}\) are real and the three \(d_{ij}\)
are arbitrary complex numbers. Pair order is always \(12,13,23\).
No restriction to real couplings, nonzero couplings or neutral fields is made.

Homogeneity reduces the question to the normalized Gram domain
\[
\mathcal D=\{K=K^\dagger\succeq0:\operatorname{tr}K=1,
\operatorname{rank}K\le2\},\qquad m=\min_{K\in\mathcal D}f(K). \tag{2}
\]
This is exactly the physical domain: every such matrix has a two-row Gram
factor. Rank one represents aligned, electrically neutral doublets; rank two
represents charge-breaking directions. Missing doublets occur as support faces.

**The geometric core is the one-dimensional kernel of a rank-two Gram matrix.**
A charged stationary point can be reconstructed from a rank-one projector onto
that kernel. Its kernel problem has the same phase-current algebra as a neutral
configuration, with transformed couplings and a weighted normalization:

```text
                       physical Gram matrices, tr K = 1
                         /                         \
               rank one /                           \ rank two
                       v                             v
                 neutral projector          one-dimensional kernel P
                       |                             |
                 primal spectrum            inverse-operator spectrum
                       \                             /
                        \--- same sextic engine ----/
                                   |
                    finite physical candidate values
                                   |
                    signs / minimum / field witness
```

The Gram-domain and constrained-stationarity framework is established prior
work, not a novelty claim here [MN15]. The new proposed reduction is the explicit
common sextic engine, its inverse-operator charged reconstruction, and their
complete algebraic treatment of exceptional inputs.

### Theorem (universal exact criterion)

Apply the fifteen-coordinate positive infinitesimal deformation in Section 7 to
(1). Apply the explicit spectrum construction of Sections 2–4 to the deformed
couplings, in the indicated real closed ordered field. Let \(\mathscr C_\epsilon\)
be the retained candidate values and \(m_\epsilon=\min\mathscr C_\epsilon\).
There are at most thirty distinct retained values, before removal of duplicate
values and after identifying the discrete doublet-sign copies. The set is
nonempty. Then
\[
\begin{array}{rcl}
 f\ge0\text{ on }\mathcal D
 &\Longleftrightarrow&m_\epsilon>0,\\[2pt]
 f>0\text{ on }\mathcal D
 &\Longleftrightarrow&m_\epsilon>2\epsilon_0,\\[2pt]
 m<0&\Longleftrightarrow&m_\epsilon<0,\\[2pt]
 m=0&\Longleftrightarrow&0<m_\epsilon<2\epsilon_0,\\[2pt]
 m&=&\operatorname{st}(m_\epsilon).
\end{array} \tag{3}
\]
Here signs are exact ordered-field signs, not tests at a small floating-point
number. A minimizing retained matrix has a bounded successive residue \(K_0\)
with \(K_0\in\mathcal D\) and \(f(K_0)=m\). Section 8 gives a terminating
algebraic residue procedure and an explicit two-row Gram factor. Thus a negative
or zero field direction is recovered when applicable.

For ordinary coefficients in a nonempty Zariski-open set, the same two spectra
can be used without deformation: their physical minimum is exactly \(m\).
The deformation is the unconditional prescription, including all singular
operators, real-coupling loci, flat directions, vanishing couplings, stationary
continua and denominator degeneracies. It is not a numerical regularization.

The effective-algorithm statement is relative to exact arithmetic, equality/order, finite-real-root and bounded-residue interfaces on finite input-derived requests. On explicitly represented rational/algebraic inputs, implementing those interfaces is a separate engineering task; no verified backend is supplied here. Nothing asserts computable access to arbitrary uncomputable real coefficients. The uniform input-to-program refinement proved in F002 is recorded in Section 8.1 below.

## 2. The common weighted spectrum

Input data are \(\alpha_i,e_{ij}\in F\), \(d_{ij}\in F(i)\), and
\(g_i\in F\), where \(F\) is real closed. Temporarily assume generic data in
the precise sense justified in Section 6. In particular all \(g_i\) are nonzero.

For ordinary real phases set \(q_i=e^{i\theta_i}\), \(q_1=1\). Over a general
real closed field, \(q_i\) means a point on the algebraic unit circle, not a
transcendental exponential. Set
\[
 B_{ii}=\alpha_i/2,\qquad
 B_{ij}=\frac12[e_{ij}+\operatorname{Re}(d_{ij}q_j\bar q_i)],\quad i<j,
\]
\[
 Q(r,q)=\frac{r^TB(q)r}{(g^Tr)^2},\qquad
 r_i\ge0,\quad \mathbf1^Tr=1,\quad g^Tr\ne0. \tag{4}
\]
The procedure below produces every projective stationary point of (4), with
support recorded, up to sign copies of the underlying complex amplitudes.
Retain all branches, not only the smallest value of this auxiliary quotient.
Negative \(g^Tr\) is allowed.

### 2.1 One-element supports

For each \(i\), include
\[
 r=e_i,\qquad \nu=\frac{\alpha_i}{2g_i^2}. \tag{5}
\]
Inactive phases are irrelevant.

### 2.2 Two-element supports

For every pair \(i<j\) and each \(\sigma\in\{-1,+1\}\), set
\[
 q_j\bar q_i=\sigma\frac{\bar d_{ij}}{|d_{ij}|},\quad
 A_i=\alpha_i/2,\quad A_j=\alpha_j/2,\quad
 h=\frac{e_{ij}+\sigma|d_{ij}|}{2},
\]
\[
 n=(A_jg_i-hg_j,\ A_ig_j-hg_i)^T,\quad
 W=A_jg_i^2-2hg_ig_j+A_ig_j^2. \tag{6}
\]
If the displayed denominators are nonzero, set
\[
 (r_i,r_j)=n/(n_i+n_j),\quad r_k=0,
 \qquad \nu=\frac{A_iA_j-h^2}{W}. \tag{7}
\]
Retain only strictly positive \(r_i,r_j\) and \(g^Tr\ne0\). There are at most
six such candidates. Do not divide by \(A_iA_j-h^2\): zero values are legitimate.
Generic data ensure \(d_{ij}\ne0\) and \(W\ne0\); Section 7 covers their failures.

To prove coverage, phase stationarity on a two-element support gives (6).
Radial stationarity of the homogeneous quotient gives
\(B_Jr_J=\nu(g_J^Tr_J)g_J\). The adjugate of the two-by-two matrix yields (7).
This argument does not assume that \(B_J\) is invertible.

### 2.3 Full support: currents eliminate amplitudes

Define
\[
 s_{12}=\operatorname{Im}(d_{12}q_2),\quad
 s_{13}=\operatorname{Im}(d_{13}q_3),\quad
 s_{23}=\operatorname{Im}(d_{23}q_3\bar q_2),
\quad j=(s_{23},-s_{13},s_{12})^T. \tag{8}
\]
The two phase derivatives vanish exactly when
\[
 r_1r_2s_{12}=r_2r_3s_{23}=-r_1r_3s_{13}. \tag{9}
\]
If all \(r_i>0\) and
\[
 \operatorname{Im}(d_{12}d_{23}\bar d_{13})\ne0, \tag{10}
\]
the common current in (9) cannot vanish. Indeed vanishing forces every
\(d_{ij}q_j\bar q_i\) to be real, whereas their invariant loop product is
\(d_{12}d_{23}\bar d_{13}\). Consequently
\[
 r=\frac{j}{\mathbf1^Tj}. \tag{11}
\]
This eliminates the radial variables before polynomial elimination.

Let
\[
 C=\begin{pmatrix}
 e_{13}d_{12}&-e_{12}d_{13}&\alpha_1d_{23}-d_{13}\bar d_{12}\\
 e_{23}d_{12}&d_{12}d_{23}-\alpha_2d_{13}&e_{12}d_{23}\\
 \alpha_3d_{12}-d_{13}\bar d_{23}&-e_{23}d_{13}&e_{13}d_{23}
 \end{pmatrix},\qquad z=(q_2,q_3,q_3\bar q_2)^T. \tag{12}
\]
A direct identity is
\[
                         2B(q)j(q)=\operatorname{Im}(Cz). \tag{13}
\]
For example, the cross term in the first component follows from
\(\operatorname{Re}v\operatorname{Im}u-
\operatorname{Re}u\operatorname{Im}v=\operatorname{Im}(u\bar v)\).
The other two components follow by the same complex multiplication. The full
identity has also been checked as a polynomial identity with every coupling
symbolic, independently of numerical stationary-point searches.

Put
\[
 h^{(2)}=g_1C_{2\bullet}-g_2C_{1\bullet},\qquad
 h^{(3)}=g_1C_{3\bullet}-g_3C_{1\bullet}. \tag{14}
\]
The remaining radial conditions are precisely
\[
 \operatorname{Im}(h^{(2)}z)=0,\qquad
 \operatorname{Im}(h^{(3)}z)=0. \tag{15}
\]
Indeed stationarity of (4) requires \(Br=\nu(g^Tr)g\); (11) and (13) reduce
this to proportionality of \(\operatorname{Im}(Cz)\) and \(g\). Conversely,
(15), positive (11), and \(g^Tr\ne0\) imply this proportionality. Multiplication
by \(r^T\) determines its coefficient and gives exactly (4). Thus the retained
roots are actual stationary points, not merely solutions of necessary equations.

### 2.4 Two biquadratics and a sextic

Use projective half-angle coordinates
\[
 q_2=\frac{1-t^2+2it}{1+t^2},\qquad
 q_3=\frac{1-u^2+2iu}{1+u^2}. \tag{16}
\]
For any complex row \((A,B,C)\), define the explicit real polynomial
\[
\begin{split}
 P_{A,B,C}(t,u)={}&[\operatorname{Im}A(1-t^2)+2\operatorname{Re}A\,t](1+u^2)\\
 &+[\operatorname{Im}B(1-u^2)+2\operatorname{Re}B\,u](1+t^2)\\
 &+\operatorname{Im}C[(1-t^2)(1-u^2)+4tu]\\
 &+2\operatorname{Re}C[u(1-t^2)-t(1-u^2)].
\end{split} \tag{17}
\]
Then (15) is exactly \(F(t,u)=G(t,u)=0\), where
\(F=P_{h^{(2)}}\), \(G=P_{h^{(3)}}\). Each has bidegree at most \((2,2)\).
Both have the fixed nonreal base points \((i,i)\) and \((-i,-i)\). Therefore
\[
 S(t)=\frac{\operatorname{Res}_u(F,G)}{1+t^2} \tag{18}
\]
is an exact polynomial quotient of degree at most six. The numerator is the
ordinary four-by-four Sylvester determinant of two quadratics in \(u\).
No physical real phase is removed by the denominator in (18).

Bihomogenize both polynomials to bidegree \((2,2)\) in
\(([T_0:T_1],[U_0:U_1])\). Use all four affine charts, obtained by reversing
the coefficient order in \(t\), \(u\), or both. In every chart isolate all real
roots of (18), specialize the two quadratics at each root, and isolate all real
roots of their gcd. Keep only common roots of the original two equations.
This handles vanishing leading coefficients and phases equal to \(\pi\).
The universal base factor remains \(1+t^2\) in each chart; in a reciprocal
chart the associated nonreal \(u\)-coordinate can change sign.

If the two bihomogeneous forms have no common component, they have at most eight
complex intersections counted with multiplicity; the two fixed nonreal points
leave at most six physical full-support points. Equivalently, their homogeneous
resultant is a binary octic with the fixed quadratic factor. Multiplicities of
projected common roots account for multiple roots in a fiber. This is only a
degree/coverage bound, not an assumption that the six roots are real or simple.

For each real root pair compute (8) and (11). Discard a zero denominator, a
nonpositive component, or \(g^Tr=0\). For each remaining pair include
\(\nu=Q(r,q)\). Form a rank-one projector by choosing any algebraic square
roots
\[
 w_i^2=r_iq_i,\qquad P_{ij}=\bar w_iw_j. \tag{19}
\]
Changing square-root signs conjugates \(P\) by a diagonal sign matrix and
changes none of the tests or values below. The common weighted spectrum contains
at most \(3+6+6=15\) values, with supports and projectors retained.

## 3. The operator and the two input spectra

On Hermitian three-by-three matrices use
\(\langle X,Y\rangle=\operatorname{tr}(XY)\). Let \(A\) have diagonal
\(a_i\) and off-diagonal entries \(b_{ij}\). Define the real self-adjoint map
\[
 (LX)_{ii}=(A\operatorname{diag}X)_i,\qquad
 (LX)_{ij}=c_{ij}X_{ij}+\bar d_{ij}\bar X_{ij}. \tag{20}
\]
Then \(f(K)=\langle K,LK\rangle/2\). Each off-diagonal real block is
\[
 \begin{pmatrix}c+\operatorname{Re}d&-\operatorname{Im}d\\
 -\operatorname{Im}d&c-\operatorname{Re}d\end{pmatrix}.
\]
For invertible \(L\), set \(R=L^{-1}\), \(G=A^{-1}\), and
\(\Delta_{ij}=c_{ij}^2-|d_{ij}|^2\). Explicitly
\[
 (RX)_{\rm diag}=G\operatorname{diag}X,\qquad
 (RX)_{ij}=\frac{c_{ij}X_{ij}-\bar d_{ij}\bar X_{ij}}{\Delta_{ij}}. \tag{21}
\]
Set \(g=G\mathbf1\), \(\beta=\mathbf1^TG\mathbf1\). In particular
\(RI=\operatorname{diag}(g)\).

**Primal input.** Run Section 2 with
\[
 (\alpha,e,d,g)=(a,b+c,d,\mathbf1). \tag{22}
\]
Every retained projector is a neutral physical matrix and its spectral value
is exactly \(f(P)\). Include all of these values in \(\mathscr C\).

**Dual input.** Run the same procedure with
\[
 \alpha_i'=2G_{ii},\quad
 e_{ij}'=2\left(G_{ij}+\frac{c_{ij}}{\Delta_{ij}}\right),\quad
 d_{ij}'=-\frac{2d_{ij}}{\Delta_{ij}},\quad g'=G\mathbf1. \tag{23}
\]
For each resulting projector \(P\), put
\[
 a_P=\langle P,RI\rangle=g^Tr,\quad
 p_P=\langle P,RP\rangle,\quad
 D_P=\beta p_P-a_P^2. \tag{24}
\]
The dual quotient is exactly \(\nu=p_P/a_P^2\), including its complex phases.
Discard \(D_P=0\) and construct
\[
 K_P=\frac{p_PRI-a_PRP}{D_P},\qquad
 E_P=\frac{p_P}{2D_P}=\frac{\nu}{2(\beta\nu-1)}. \tag{25}
\]
Do not divide by \(p_P\) or \(\nu\), and do not require either to be nonzero.
The projective-stationarity identities prove \(K_PP=0\) and
\(\operatorname{tr}K_P=1\). The remaining physical test is Section 4.

## 4. A scalar charged-admissibility test

Define
\[
 \beta_2=\langle RI,RI\rangle,\quad
 a_{2,P}=\langle RI,RP\rangle,\quad
 p_{2,P}=\langle RP,RP\rangle,
\]
\[
 \chi_P=\frac{p_P^2\beta_2-2p_Pa_Pa_{2,P}+a_P^2p_{2,P}}{D_P^2}.
 \tag{26}
\]
Then \(\chi_P=\operatorname{tr}K_P^2\). Since \(K_P\) is Hermitian, has
trace one and already has a nontrivial kernel, its eigenvalues are
\((0,x,1-x)\). Hence
\[
                     K_P\succeq0\quad\Longleftrightarrow\quad\chi_P\le1.
 \tag{27}
\]
Retain exactly those dual candidates passing (27), adding their values \(E_P\)
to \(\mathscr C\). Equality may produce a rank-one duplicate and is retained.
Purity alone would not enforce the physical rank bound: \(I/3\) is a counterexample
unless the separate kernel identity is proved.

All scalars in (26) can be evaluated without choosing half-angle square roots.
Namely \(\beta_2=\|G\mathbf1\|^2\),
\(a_{2,P}=(G^2\mathbf1)^Tr\), and \(p_{2,P}\) is the neutral numerator
with coefficients
\[
 \alpha_i''=2(G^2)_{ii},\quad
 e_{ij}''=2\left((G^2)_{ij}+\frac{c_{ij}^2+|d_{ij}|^2}{\Delta_{ij}^2}\right),
 \quad d_{ij}''=-\frac{4c_{ij}d_{ij}}{\Delta_{ij}^2}. \tag{28}
\]
This follows by squaring each real two-by-two inverse block. Matrix reconstruction
and principal-minor tests provide redundant implementation checks.

## 5. Charged-to-neutral equivalence and global coverage

### 5.1 Stationarity in two representations

A rank-two point of \(\mathcal D\) lies on a smooth rank-two stratum.
The normal space to fixed trace and rank is spanned by \(I\) and its kernel
projector \(P\). Thus stationarity implies
\[
                         LK=\lambda I+\mu P. \tag{29}
\]
This can independently be derived in the original doublet variables. Write
\(K=\Phi^\dagger\Phi\) with \(\Phi\) a rank-two two-by-three matrix.
The real field derivative of \(f\) is \(2\Phi LK\), while that of
\(\operatorname{tr}K\) is \(2\Phi\). Lagrange stationarity gives
\(\Phi LK=\lambda\Phi\). Hermiticity then forces \(LK-\lambda I\) to be
supported in the one-dimensional kernel of \(\Phi\), which gives (29).
Taking the trace against \(K\) fixes \(\lambda=2f(K)\).
The field-gradient identity has been checked for all twelve independent real
field coordinates with all fifteen couplings symbolic.

Applying \(R\), taking the trace, and taking the expectation in \(P\) yields
\[
 \beta\lambda+a_P\mu=1,\qquad a_P\lambda+p_P\mu=0. \tag{30}
\]
For \(D_P\ne0\) this is exactly (25), with
\(\lambda=p_P/D_P\), \(\mu=-a_P/D_P\).

For \(a_P\ne0\), write \(P=zz^\dagger\), \(z^\dagger z=1\).
Projective stationarity of \(p_P/a_P^2\) is equivalent to
\[
                         (a_PRP-p_PRI)z=0. \tag{31}
\]
For completeness, its directional derivative is
\(4\operatorname{Re}[\delta z^\dagger(a_PRP-p_PRI)z]/a_P^3\).
The expectation of the vector in (31) against \(z\) vanishes identically, so
the normalization multiplier is zero. Equation (31) is exactly \(K_Pz=0\)
from (25). Thus the spectral stationary equations and the charged kernel
condition are equivalent, not only one-way implications.

Missing components of \(z\) cause no omitted derivatives. The required assertion concerns the vector obtained **after applying the structured operator to the projector and then to the supported vector**, not an entire row of the matrix \(RP\). If \(P=zz^\dagger\) and \(z_i=0\), formula (21) allows \((RP)_{ii}=(G r)_i\ne0\): diagonal mixing can create a nonzero entry in the formerly zero row. Nevertheless every off-diagonal term in \(((RP)z)_i=\sum_j(RP)_{ij}z_j\) vanishes, because \((RP)_{ij}\) contains the off-support factor \(z_i\) or \(\bar z_i\), and its diagonal term vanishes upon multiplication by \(z_i=0\). Also \(((RI)z)_i=g_i z_i=0\). Thus the off-support **components of (31)** vanish, exactly as required, without claiming that \(RP\) preserves a zero row. The corresponding vector-component argument holds for the primal structured map \(L\); it relies on the individual sign-flip structure and is not asserted for an arbitrary 3HDM.

### 5.2 Exceptional charged equations

The following exceptions must not be silently discarded.

If \(a_P=0\) but \(p_P\ne0\), (30) forces \(\mu=0\) and
\(K=RI/\beta\), which has rank three when every \(g_i\ne0\). It cannot be
our rank-two point. If \(D_P=0\), consistency of (30) forces
\(a_P=p_P=0\), \(\beta\ne0\), and \(\lambda=1/\beta\).
Moreover \(\mu\ne0\) for the same rank reason, and the kernel equation implies
\[
                    RPz=-\frac{\lambda}{\mu}RIz. \tag{32}
\]
It follows that \(P\) is a stationary zero of \(p_P\) restricted to
\(a_P=0\) on projective space. Section 6 proves that these stationary zeros
are absent for algebraically generic weighted data. They need not be absent for
arbitrary real data; an exact nonreal-phase counterexample is in
`DERIVATIONS.md`. Section 7, not an unproved nonzero-denominator assumption,
covers these cases.

### 5.3 Minimum coverage

A global minimum of (2) has rank one or two. Rank one is covered by the primal
spectrum on its actual support. A rank-two minimum is stationary on its smooth
stratum, hence obeys (29). For generic coefficients Sections 5.1–5.2 place it in
the dual spectrum and it passes the exact physical filter (27). Conversely,
every retained matrix is in \(\mathcal D\) and has the stated energy. Therefore
\[
                             m=\min\mathscr C \tag{33}
\]
for generic data. This proves both directions of the global result; numerical
absence of other minima is not used.

Over a real closed extension, use the semialgebraic extreme-value theorem for
closed bounded domains, equivalently first-order transfer of the ordinary real
compact minimum assertion. Topological compactness of a non-Archimedean field
is not being assumed. The stationary equations are algebraic circle equations,
so no exponential or trigonometric function over that field is needed.

## 6. Why generic data really avoid the missing branches

Only a proper algebraic exceptional set is removed here. Section 7 subsequently
removes this qualification from the theorem.

### 6.1 Elementary exclusions and the full-support intersection

Invertibility of \(A\), all \(\Delta_{ij}\ne0\), all \(g_i\ne0\),
\(\beta\ne0\), nonzero \(d_{ij}\) and the nonreal loop condition each exclude
proper polynomial zero sets after clearing denominators. Pair-face \(W=0\)
also does so: eliminating \(|d|\) gives, for a pair,
\[
 [A_jg_i^2-e_{ij}g_ig_j+A_ig_j^2]^2
       -|d_{ij}|^2g_i^2g_j^2=0. \tag{34}
\]
This polynomial is not identically zero.

For the two full-support bihomogeneous forms, having a common factor of some
positive bidegree is a closed algebraic condition in their projective coefficient
spaces: there are finitely many possible factor bidegrees, and multiplication
maps between the corresponding projective spaces have closed images. Its
pullback to the spectrum parameters is proper. Here is an exact witness:
\[
 \alpha=(3/2,5/3,7/4),\quad e=(1/3,-2/5,3/7),\quad
 d=(2/3+i/5,3/5-i/7,-4/7+i/3),\quad g=\mathbf1.
\]
After clearing scalar denominators the forms are
\[
\begin{split}
 F={}&-3365t^2u^2-14400t^2u+2321t^2+10020tu^2-7612tu\\
    &-3060t+1485u^2-1320u-441,\\
 G={}&-20735t^2u^2-44520t^2u+4613t^2+96460tu^2-49896tu\\
    &+10780t+20335u^2+41160u-4213.
\end{split}
\]
Their exact gcd is one, both have full bidegrees. Define the primitive-normalized polynomial \(S_{\mathrm{prim}}(t)\) by
\[
\begin{split}
 &65532894182001t^6-846134370496944t^5+2404104611159391t^4\\
 &\quad+2245261288159824t^3-463362875655073t^2
 -249992387249952t-20785328196111.
\end{split} \tag{35}
\]
For precisely the integer polynomials \(F,G\) displayed above, the **ordinary Sylvester resultant** is not \((1+t^2)S_{\mathrm{prim}}(t)\) but
\[
\operatorname{Res}_u(F,G)=100(1+t^2)S_{\mathrm{prim}}(t).
\]
Equivalently, the literal quotient \(\operatorname{Res}_u(F,G)/(1+t^2)\) from (18) is \(100S_{\mathrm{prim}}(t)\). The factor is strictly positive and does not change the zero set, primitive square-free data, candidate-root coverage, or properness argument; the paper's original identification of (35) with the unnormalized quotient was a literal normalization error. The factor identity has been independently checked by exact symbolic resultant computation in the manuscript-integration audit.
The loop imaginary part is \(1/1225\). No boundary divisor is a common component.
The same property was separately checked with mixed weights \((2,-1,3)\).
Thus the needed open set is nonempty both for the primal slice \(g=\mathbf1\)
and for independent weighted data. Exact gcd/resultant and degree certificates
are included in `results/hexagon_spectrum_probe.json`.

### 6.2 Independent dual parameters

The inverse map preserves the structured operator space. Parametrize a structured
self-adjoint \(R\) by a real symmetric diagonal block \(G\), three real scalar
off-diagonal coefficients \(c^R\), and three complex coefficients \(d^R\).
Its weighted data are
\[
 \alpha_i'=2G_{ii},\quad e_{ij}'=2(G_{ij}+c^R_{ij}),\quad
 d_{ij}'=2d^R_{ij},\quad g=G\mathbf1. \tag{36}
\]
This is a linear isomorphism between fifteen real coordinates. For example
\[
 G_{12}=\frac{g_1+g_2-g_3-G_{11}-G_{22}+G_{33}}2,
\]
with the other two off-diagonal entries recovered cyclically. The remaining
coefficients follow immediately. An exact Jacobian computation in the recorded
coordinate order gives determinant \(8192\). Operator inversion is birational
where defined. Consequently independent original couplings produce generic
weighted dual data; the dual exceptions cannot be hidden identically by a
parameter constraint.

### 6.3 No stationary zero on the pole locus, generically

Fix a support of size \(s\ge2\), nonzero supported components, generic \(g\),
and impose \(\mathbf1^Tr=1\), \(g^Tr=0\). If this set is nonempty, its radial
dimension is \(s-2\); its phase dimension is \(s-1\). The total is \(2s-3\).
When \(g\) is constant and nonzero on the support the locus is empty, and a
singleton cannot lie on it because \(g_i\ne0\).

At each such point, the value of \(p=r^TB(q)r\) and its \(2s-3\) tangential
first derivatives give \(2s-2\) independent linear conditions on the twelve
numerator coefficients. To see independence explicitly:

* Vary \(\operatorname{Im}(d_{ij}q_j\bar q_i)\) on a spanning tree, while
  adjusting \(e_{ij}\) to leave \(B\) fixed at the point. This changes the
  \(s-1\) phase derivatives independently without changing the value or radial
  derivatives. The incidence-matrix rank is \(s-1\), since all supported
  \(r_i\ne0\); for the tree \(12,23\), a determinant is \(r_1r_2^2r_3\).
* Arbitrary real symmetric changes of \(B\) are available from \(\alpha,e\).
  In particular \(\delta B=(\ell\mathbf1^T+\mathbf1\ell^T)/2\) gives
  \(\delta p=\ell^Tr\) on \(\mathbf1^Tr=1\). Its value and the \(s-2\)
  independent radial derivatives can be prescribed independently.

The incidence set of stationary zeros therefore has dimension at most
\(12+(2s-3)-(2s-2)=11\) for fixed \(g\), or at most fourteen in the full
fifteen-dimensional weighted parameter space. It is semialgebraic; its projection
has no larger dimension and is contained in a proper algebraic set. There are
only finitely many supports and coordinate charts. Thus algebraically generic
weighted data have no such stationary zero. These elementary semialgebraic
projection/dimension facts are the only dimension-theoretic input [BPR06].

A second verification of this particular genericity mechanism avoids the
incidence count. Hold \(g\) fixed and replace \(p\) by
\(p+\eta(\mathbf1^Tr)^2\), an allowed independent direction
\(\delta\alpha_i=2\eta,\delta e_{ij}=2\eta,\delta d_{ij}=0\).
On the normalized pole locus this adds the constant \(\eta\) without changing
its stationary points. A semialgebraic differentiable function has finitely many
critical values: its critical set has finitely many semialgebraic path-connected
components and the function is constant on each by differentiation along paths.
Hence an independent transcendental \(\eta\) cannot make a critical value zero.
This also establishes that the pole-zero exception is not identically imposed
by the model.

### 6.4 Simultaneity

The original coefficient space is irreducible affine fifteen-space. The primal
conditions are proper by the explicit witness and the surjective map
\((a,b,c,d)\mapsto(a,b+c,d)\). The dual conditions pull back properly by (36)
and birational inversion. A finite union of the proper exceptional sets is still
proper. No assumption that all these tests happen to hold in one arbitrary
numerical example is needed. Algebraically independent formal coefficients
avoid all of them simultaneously.

## 7. Universal singular completion by a positive infinitesimal

Order the coefficient coordinates as
\[
 (a_1,a_2,a_3,b_{12},b_{13},b_{23},c_{12},c_{13},c_{23},
 \operatorname{Re}d_{12},\operatorname{Im}d_{12},
 \operatorname{Re}d_{13},\operatorname{Im}d_{13},
 \operatorname{Re}d_{23},\operatorname{Im}d_{23}).
\]
Let \(M_j(K)\) be the coefficient monomial, so \(f=\sum_{j=1}^{15}\kappa_jM_j\).
For an imaginary part of \(d\), this monomial is \(-\operatorname{Im}K_{ij}^2\).
Work in the iterated real closed algebraic Puiseux field
\[
 F=\mathbb R\langle\epsilon_0\rangle\langle\epsilon_1\rangle\cdots
 \langle\epsilon_{15}\rangle,
 \qquad 0<\epsilon_{15}\ll\cdots\ll\epsilon_1\ll\epsilon_0\ll1.
 \tag{37}
\]
A later infinitesimal is smaller than every positive element of the preceding
field. These are sixteen independent formal variables, not sixteen numerical
values chosen by a tolerance rule. Define
\[
 f_\epsilon=f+\epsilon_0(\operatorname{tr}K)^2+
                  \sum_{j=1}^{15}\epsilon_jM_j(K). \tag{38}
\]
Thus \(a_i\) and \(b_{ij}\) each acquire \(2\epsilon_0\), followed by the
coordinate's own \(\epsilon_j\). Other coordinates acquire their own
\(\epsilon_j\) only. The resulting fifteen coordinates are algebraically
independent over \(\mathbb R(\epsilon_0)\): they are independent variables plus
fixed translations. Section 6 consequently applies without a genericity oracle.

On \(\mathcal D\), \(r_i^2/2\le1/2\), and every other coefficient monomial
has absolute value at most \(1/4\), because
\(|K_{ij}|^2\le r_ir_j\le1/4\). Therefore
\[
 \left|\sum_{j=1}^{15}\epsilon_jM_j(K)\right|
 \le\frac92\epsilon_1\ll\epsilon_0. \tag{39}
\]
The bound is deliberately conservative. Taking minima and using Section 5 gives
\[
             |m_\epsilon-m-\epsilon_0|\le\frac92\epsilon_1. \tag{40}
\]
For \(m<0\) the negative real constant dominates the deformation. For \(m>0\)
it exceeds \(2\epsilon_0\). For \(m=0\), (40) places \(m_\epsilon\) strictly
between zero and \(2\epsilon_0\). This proves all tests in (3), with no exchange
of an uncontrolled limit and optimization.

Every minimizing retained matrix is positive semidefinite with trace one, so
all its entries are bounded by real constants. Successive residue maps exist,
are order-preserving ring homomorphisms, and must be applied in the order
\(\epsilon_{15},\epsilon_{14},\ldots,\epsilon_0\) [LRT25]. Principal minors,
trace and determinant survive these residues. Thus \(K_0\in\mathcal D\), and
polynomial evaluation together with (40) gives \(f(K_0)=m\).

Do not set the original singular operator inverse to its limit separately.
The inverse may have poles. Construct the bounded physical matrix first, then
take its residue. This also covers merging roots and stationary continua.

## 8. Finite exact operations and witness recovery

The stationary-candidate stage uses one homogeneous four-by-four resultant per spectrum
(evaluated in the needed projective charts), univariate roots of degree at
most six, common roots of specialized quadratics, the face square roots,
finite arithmetic, signs and small matrix operations. Multiple real roots and
all projective charts are retained. Ordered Thom encodings and univariate sign
determination work over general real closed fields [BPR06, Algorithm 10.14 and
its surrounding root/sign constructions]. Rational-interval bisection is not an
adequate substitute in a non-Archimedean field.

The residue operation in (3) is also finite and explicit. Suppose a selected
bounded algebraic number \(x\) lies over \(E\langle\epsilon\rangle\), where
\(E\) is the preceding real closed field.

1. Compute a nonzero annihilating polynomial \(P(\epsilon,X)\in E[\epsilon,X]\)
   from the finite algebraic root tower, using field norms and clearing
   denominators. Equivalently eliminate in that already zero-dimensional finite
   algebraic tower, with the selected nonzero denominators localized. This is
   not elimination of the original field-orientation problem.
2. Divide the largest common power of \(\epsilon\), obtaining
   \(Q(X)=P(0,X)\ne0\).
3. Isolate and order the distinct real roots \(q_1<\cdots<q_s\) of \(Q\) in
   \(E\). Since \(x\) is bounded, its residue is a root of \(Q\).
4. Compare the selected \(x\) with the midpoints
   \((q_i+q_{i+1})/2\) in the ordered extension. These comparisons uniquely
   identify its residue. A midpoint is not a root of \(Q\), so no ambiguity
   arises even when several branches coalesce at a repeated root.

There are finitely many finite-degree operations at each of the sixteen levels.
Residue annihilators can have higher degree than six; the sextic bound applies
to the phase-elimination stage, not to a minimal polynomial of the final energy
or to every polynomial in a singular-input implementation.
This selected-root procedure requires neither simple roots nor a claim that an
arbitrary multivariate limit algorithm handles singular solutions. Carry the
physical root selection through the computation; do not take limits of an
unfiltered complex elimination set.

Finally construct doublets from the resulting \(K_0\). Choose \(i\) with
\(K_{ii}>0\) and set \(a_j=K_{ij}/\sqrt{K_{ii}}\). The Schur complement
\(H_{jl}=K_{jl}-\bar a_ja_l\) is positive semidefinite of rank at most one.
If \(H=0\), take the second row to be zero. Otherwise choose \(k\) with
\(H_{kk}>0\) and set \(b_j=H_{kj}/\sqrt{H_{kk}}\). Then
\[
                  \Phi_j=(a_j,b_j)^T,\qquad\Phi^\dagger\Phi=K_0. \tag{41}
\]
This recovers an exact minimizing field direction, and hence a negative or
zero direction in the respective cases. It is not a classification of every
zero orbit when the zero set is continuous.

### 8.1 F002 uniform finite input-to-program construction

The 9 real diagonal/pair coefficients and 3 unrestricted complex pair coefficients define 15 real input coordinates \(\kappa\). The analytic deformation (37)--(40) uses rational constants, these original coordinates, and 16 ordered positive infinitesimal generators. In F002 these data are represented by explicit finite input syntax, not by choosing arbitrary semantic expressions *after* a solution is known. The finite code-producing construction generates a two-spectrum candidate list and a selected-minimum record; the same code layer supports exact sign tests, 16 successive residues, a physical Gram-matrix witness, and a pivoted reconstruction into normalized complex doublets. After the residues, the final stage-zero (`Code 0`) scalar and matrix codes no longer contain infinitesimal-generator leaves.

The central Lean theorem is `W3.FiniteInput.uniform_finite_input_exact_criterion (O : ResidueOracles) (κ : Parameters ℝ)` in `lean/W3/FiniteInputMain.lean`. Its conjuncts connect the *evaluations* of finite candidate codes to `actualCandidateValues κ`, prove a bound of at most 30 distinct candidates, identify the selected code value with the deformed candidate minimum, characterize weak/strict/negative/flat cases, establish successful 16-level residue execution with stage-zero value `realMinimum κ`, and produce normalized physical fields of that energy. Its final conjunct supplies a finite-program representative with literal residue execution for **every** retained minimizing Gram matrix satisfying the specified minimum-energy hypothesis; it is not merely existence of one preferred minimizer. The companion `W3.FiniteInput.arbitrary_complex_finite_input_criterion` translates sign programs into unrestricted complex-coupling field-space statements. Supporting constructions include `W3.FiniteInput.actualCodeProgram` (`lean/W3/FiniteInputActualProgram.lean`) and `W3.FiniteInput.every_old_retained_minimizer_coded_execution` (`lean/W3/FiniteInputRetainedExecution.lean`).

These are exact **semantic-interface refinement theorems**. The Lean endpoint is parameterized by `ResidueOracles`; exact arithmetic, coefficient equality/order and finite real-root interfaces act on finite requests over the infinitesimal tower. The sources contain `noncomputable` definitions and permit certain classical choices affecting ordering/equality operations. They do **not** constitute verified implementations of rational/algebraic number representations, real-root isolation, backend-independent portable root-code serialization, or an executable solver for arbitrary real inputs. The sextic bound pertains to phase elimination, not to all residue annihilators or minimal polynomials.

The paper's four-chart/gcd auxiliary procedure applies on a broad undeformed generic domain \(G\). The formal affine-spectrum API instead assumes a **stronger** open generic domain \(G'\), excluding additional projective-boundary roots and nonunique recovery fibers in its chosen affine chart. The formal proof establishes projective-root correspondence on \(G'\), and, importantly, proves the prescribed primal and inverse-dual deformations lie in \(G'\) for **every** original input \(\kappa\). Thus the unrestricted original-input stability theorem is not narrowed. Conversely, F002 must not be cited as a complete formalization of the general-purpose four-chart/gcd API on *every undeformed* input in \(G\), nor of the optional coefficient-only evaluation formula (28) as a separate literal endpoint: the formal physical filter uses its proved exact purity identity. The full general intersection-multiplicity count on the wider undeformed interface is not separately packaged as a formal endpoint. See `docs/SCOPE.md`.

### 8.2 What the formal revision establishes and does not establish

The initial 156-source formal development omitted the uniform input-to-finite-program construction with input provenance. F002 specifically repairs that formal claim rather than merely restating semantic algebraicity. `verification/RELEASE_STATUS.json` (recorded 2026-10-09 18:51 UTC) identifies 190 freshly compiled local Lean modules, 4,545 kernel declarations, 3,088 theorems, strict same-kernel replay and three renewed rounds of four AI reviewer reports each, with no recorded unresolved load-bearing findings. These are **reported local validation and AI audit results**, not human peer review or an independently implemented proof kernel. Pinned external dependencies were fingerprinted and reused rather than all rebuilt from source in that run; any GitHub-hosted CI result must be checked separately. The frozen F002 source identity is `7fc34595fdb0a21778cf000dfac1484a4d6dd9c0e9dc3aff7ad0fce5f1af73c5` (SHA-256), with validation artifacts under `verification/`. This manuscript revision does not itself change or rerun that frozen formalization.

## 9. Scope, provenance and verification limits

The theorem concerns only the tree-level quartic form (1). If \(m=0\), the
quadratic terms can still be negative along a flat quartic direction. No claim
is made here that arbitrary \(V_2+V_4\) is bounded below, that a phenomenologically
acceptable neutral vacuum is global, or that radiative corrections preserve the
classification. Conversely \(m>0\) is strict quartic positivity.

The algebraic genericity, real-root/sign and bounded-residue arguments belong to the mathematical proof and its formal counterpart, not to the floating-point prototype. Numerical tolerances and local root polishing supply diagnostics only; finite symbolic checks alone do not establish universal stationary-point coverage. The F002 Lean kernel verification and AI audits have the precisely stated scope of Section 8.2 and `docs/SCOPE.md`. They do not imply human expert review, external endorsement, absolute priority, or a verified concrete root backend. The original diagnostic wrapper `research/code/replay_checks.py` was found to admit stale outputs; the separately repaired `scripts/hardened_replay.py` is the appropriate finite diagnostic wrapper, but it is not itself a theorem verifier.

### References used at their stated scope

[BPR06] S. Basu, R. Pollack and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
second edition, 2006. Real closed fields, semialgebraic dimension and univariate
root/sign representations, especially Algorithm 10.14. The singular residue
procedure in Section 8 is proved here rather than inferred from a
simple-zero-only multivariate limit algorithm.

[LRT25] A. Lerario, L. Rizzi and D. Tiberio, *Quantitative approximate definable
choices*, Mathematische Annalen 392 (2025), 1289ff. Algebraic Puiseux towers,
bounded residues and the order of successive limits; Definitions 4, 23, 25 and
Remarks 26–27.

[MN15] M. Maniatis and O. Nachtmann, *Stability and symmetry breaking in the
general three-Higgs-doublet model*, arXiv:1408.6833; JHEP 02 (2015) 058, with
erratum JHEP 10 (2015) 149. The inspected arXiv text includes the rank-one
stationary treatment. Gram geometry and the general stationary-equation method
are prior work, not claimed as new here.

For literature-context and equivalent-prior assessments consult `research/SOURCES.md` and `docs/PROVENANCE.md`; they are not a certification of priority. The original research archive refers to an earlier `REPORT.md` which is not included in this public repository. Current validation status and the explicit statement boundaries reside in `verification/RELEASE_STATUS.json` and `docs/SCOPE.md`.
