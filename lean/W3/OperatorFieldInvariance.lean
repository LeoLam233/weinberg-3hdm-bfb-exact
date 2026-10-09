import W3.OperatorFieldCharged
import W3.PrimalFieldBridge
import W3.WeightedCorrespondence

/-! Exact independence of all reconstructed charged scalar tests from the
square-root/sign representative of a weighted candidate, over every ordered field. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.StrataTransfer W3.RealModel W3.Weighted W3.PrimalFieldBridge
open ComplexPair
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def diagonal9 (y : HermitianCoordinates K) : Fin 3 → K := ![y 0,y 1,y 2]
def offReal9 (y : HermitianCoordinates K) : Fin 3 → K := ![y 3,y 5,y 7]
def offImag9 (y : HermitianCoordinates K) : Fin 3 → K := ![y 4,y 6,y 8]
def offNorm9 (y : HermitianCoordinates K) (i : Fin 3) : K := offReal9 y i^2+offImag9 y i^2
def offSquareReal9 (y : HermitianCoordinates K) (i : Fin 3) : K := offReal9 y i^2-offImag9 y i^2
def offSquareImag9 (y : HermitianCoordinates K) (i : Fin 3) : K := 2*offReal9 y i*offImag9 y i

def QuadraticCoordinatesEq (y w : HermitianCoordinates K) : Prop :=
  diagonal9 y = diagonal9 w ∧ ∀ i, offNorm9 y i = offNorm9 w i ∧
    offSquareReal9 y i = offSquareReal9 w i ∧ offSquareImag9 y i = offSquareImag9 w i

lemma operatorPair_form (k : Parameters K) (y : HermitianCoordinates K) :
    hermitianPair y (hermitianOperator k y) =
      y 0*(k 0*y 0+k 3*y 1+k 4*y 2)+y 1*(k 3*y 0+k 1*y 1+k 5*y 2)+
      y 2*(k 4*y 0+k 5*y 1+k 2*y 2)+
      2*(k 6*offNorm9 y 0+k 9*offSquareReal9 y 0-k 10*offSquareImag9 y 0+
        k 7*offNorm9 y 1+k 11*offSquareReal9 y 1-k 12*offSquareImag9 y 1+
        k 8*offNorm9 y 2+k 13*offSquareReal9 y 2-k 14*offSquareImag9 y 2) := by
  simp [hermitianPair,hermitianOperator,offNorm9,offSquareReal9,offSquareImag9,offReal9,offImag9]
  ring

lemma operatorNorm_form (k : Parameters K) (y : HermitianCoordinates K) :
    hermitianPair (hermitianOperator k y) (hermitianOperator k y) =
      (k 0*y 0+k 3*y 1+k 4*y 2)^2+(k 3*y 0+k 1*y 1+k 5*y 2)^2+
      (k 4*y 0+k 5*y 1+k 2*y 2)^2+
      2*((k 6^2+k 9^2+k 10^2)*offNorm9 y 0+
        2*k 6*(k 9*offSquareReal9 y 0-k 10*offSquareImag9 y 0)+
        (k 7^2+k 11^2+k 12^2)*offNorm9 y 1+
        2*k 7*(k 11*offSquareReal9 y 1-k 12*offSquareImag9 y 1)+
        (k 8^2+k 13^2+k 14^2)*offNorm9 y 2+
        2*k 8*(k 13*offSquareReal9 y 2-k 14*offSquareImag9 y 2)) := by
  simp [hermitianPair,hermitianOperator,offNorm9,offSquareReal9,offSquareImag9,offReal9,offImag9]
  ring

lemma diagonal9_equal {y w : HermitianCoordinates K} (h : diagonal9 y = diagonal9 w) :
    y 0=w 0 ∧ y 1=w 1 ∧ y 2=w 2 := by
  exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩

lemma operatorPair_invariant (k : Parameters K) (y w : HermitianCoordinates K)
    (h : QuadraticCoordinatesEq y w) :
    hermitianPair y (hermitianOperator k y) = hermitianPair w (hermitianOperator k w) := by
  obtain ⟨h0,h1,h2⟩ := diagonal9_equal h.1
  rw [operatorPair_form,operatorPair_form,h0,h1,h2,
    (h.2 0).1,(h.2 0).2.1,(h.2 0).2.2,(h.2 1).1,(h.2 1).2.1,(h.2 1).2.2,
    (h.2 2).1,(h.2 2).2.1,(h.2 2).2.2]

lemma operatorNorm_invariant (k : Parameters K) (y w : HermitianCoordinates K)
    (h : QuadraticCoordinatesEq y w) :
    hermitianPair (hermitianOperator k y) (hermitianOperator k y) =
      hermitianPair (hermitianOperator k w) (hermitianOperator k w) := by
  obtain ⟨h0,h1,h2⟩ := diagonal9_equal h.1
  rw [operatorNorm_form,operatorNorm_form,h0,h1,h2,
    (h.2 0).1,(h.2 0).2.1,(h.2 0).2.2,(h.2 1).1,(h.2 1).2.1,(h.2 1).2.2,
    (h.2 2).1,(h.2 2).2.1,(h.2 2).2.2]

lemma diagonalPair_invariant (U y w : HermitianCoordinates K)
    (hU : ∀ i, offReal9 U i=0 ∧ offImag9 U i=0) (h : diagonal9 y=diagonal9 w) :
    hermitianPair U y=hermitianPair U w := by
  obtain ⟨h0,h1,h2⟩ := diagonal9_equal h
  have u3 : U 3=0 := (hU 0).1
  have u4 : U 4=0 := (hU 0).2
  have u5 : U 5=0 := (hU 1).1
  have u6 : U 6=0 := (hU 1).2
  have u7 : U 7=0 := (hU 2).1
  have u8 : U 8=0 := (hU 2).2
  simp [hermitianPair,u3,u4,u5,u6,u7,u8,h0,h1,h2]

lemma operator_diagonal_invariant (k : Parameters K) (y w : HermitianCoordinates K)
    (h : diagonal9 y=diagonal9 w) : diagonal9 (hermitianOperator k y)=diagonal9 (hermitianOperator k w) := by
  obtain ⟨h0,h1,h2⟩ := diagonal9_equal h
  simp [diagonal9,hermitianOperator,h0,h1,h2]

/-- Four basic scalar invariants determine every charged value and purity filter. -/
theorem inverseScalarInvariants (k : Parameters K) (y w : HermitianCoordinates K)
    (h : QuadraticCoordinatesEq y w) :
    let U := hermitianInverse k hermitianIdentity
    hermitianPair U y = hermitianPair U w ∧
    hermitianPair y (hermitianInverse k y) = hermitianPair w (hermitianInverse k w) ∧
    hermitianPair U (hermitianInverse k y) = hermitianPair U (hermitianInverse k w) ∧
    hermitianPair (hermitianInverse k y) (hermitianInverse k y) =
      hermitianPair (hermitianInverse k w) (hermitianInverse k w) := by
  dsimp only
  have hU : ∀ i, offReal9 (hermitianInverse k hermitianIdentity) i=0 ∧
      offImag9 (hermitianInverse k hermitianIdentity) i=0 := by
    intro i
    fin_cases i <;> simp [offReal9,offImag9,hermitianInverse,hermitianOperator,hermitianIdentity]
  refine ⟨diagonalPair_invariant _ _ _ hU h.1, operatorPair_invariant _ _ _ h, ?_, operatorNorm_invariant _ _ _ h⟩
  exact diagonalPair_invariant _ _ _ hU (operator_diagonal_invariant _ _ _ h.1)

lemma projector_norm9 (z : RealVector K) :
    offNorm9 (hermitianProjector z) 0 = normSq (pairVector z 0)*normSq (pairVector z 1) ∧
    offNorm9 (hermitianProjector z) 1 = normSq (pairVector z 0)*normSq (pairVector z 2) ∧
    offNorm9 (hermitianProjector z) 2 = normSq (pairVector z 1)*normSq (pairVector z 2) := by
  simp [offNorm9,offReal9,offImag9,hermitianProjector,projectorRe,projectorIm,pairVector,normSq]
  constructor
  · ring
  constructor <;> ring

lemma projector_square9 (z : RealVector K) :
    (⟨offSquareReal9 (hermitianProjector z) 0,offSquareImag9 (hermitianProjector z) 0⟩ : ComplexPair K) =
      squaredEntry (pairVector z 0) (pairVector z 1) ∧
    (⟨offSquareReal9 (hermitianProjector z) 1,offSquareImag9 (hermitianProjector z) 1⟩ : ComplexPair K) =
      squaredEntry (pairVector z 0) (pairVector z 2) ∧
    (⟨offSquareReal9 (hermitianProjector z) 2,offSquareImag9 (hermitianProjector z) 2⟩ : ComplexPair K) =
      squaredEntry (pairVector z 1) (pairVector z 2) := by
  constructor
  · apply complexPair_ext <;> simp [offSquareReal9,offSquareImag9,offReal9,offImag9,hermitianProjector,
      projectorRe,projectorIm,pairVector,squaredEntry,mul,conj] <;> ring
  constructor <;> apply complexPair_ext <;> simp [offSquareReal9,offSquareImag9,offReal9,offImag9,hermitianProjector,
    projectorRe,projectorIm,pairVector,squaredEntry,mul,conj] <;> ring

/-- PointMatches retains precisely the sign-independent data needed above. -/
theorem pointMatches_quadratic_eq (x : SpectrumPoint K) (z w : RealVector K)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2))
    (hw : PointMatches x (pairVector w 0) (pairVector w 1) (pairVector w 2)) :
    QuadraticCoordinatesEq (hermitianProjector z) (hermitianProjector w) := by
  have h0 := hz.1.symm.trans hw.1
  have h1 := hz.2.1.symm.trans hw.2.1
  have h2 := hz.2.2.1.symm.trans hw.2.2.1
  have hs0 := (projector_square9 z).1.trans (hz.2.2.2.1.trans hw.2.2.2.1.symm) |>.trans (projector_square9 w).1.symm
  have hs1 := (projector_square9 z).2.1.trans (hz.2.2.2.2.1.trans hw.2.2.2.2.1.symm) |>.trans (projector_square9 w).2.1.symm
  have hs2 := (projector_square9 z).2.2.trans (hz.2.2.2.2.2.trans hw.2.2.2.2.2.symm) |>.trans (projector_square9 w).2.2.symm
  refine ⟨?_,?_⟩
  · funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i
    fin_cases i
    · exact ⟨by change offNorm9 (hermitianProjector z) 0 = offNorm9 (hermitianProjector w) 0; rw [(projector_norm9 z).1,(projector_norm9 w).1,h0,h1], congrArg ComplexPair.re hs0, congrArg ComplexPair.im hs0⟩
    · exact ⟨by change offNorm9 (hermitianProjector z) 1 = offNorm9 (hermitianProjector w) 1; rw [(projector_norm9 z).2.1,(projector_norm9 w).2.1,h0,h2], congrArg ComplexPair.re hs1, congrArg ComplexPair.im hs1⟩
    · exact ⟨by change offNorm9 (hermitianProjector z) 2 = offNorm9 (hermitianProjector w) 2; rw [(projector_norm9 z).2.2,(projector_norm9 w).2.2,h1,h2], congrArg ComplexPair.re hs2, congrArg ComplexPair.im hs2⟩

/-- A quadratic pairing expansion for the actual reconstructed matrix. -/
theorem reconstructed_pair_formula (U V : HermitianCoordinates K) (p a D : K) :
    hermitianPair (fun i => (p*U i-a*V i)/D) (fun i => (p*U i-a*V i)/D) =
      (p^2*hermitianPair U U-2*p*a*hermitianPair U V+a^2*hermitianPair V V)/D^2 := by
  simp only [hermitianPair,div_eq_mul_inv]
  ring

lemma hermitianPurity_eq_pair (y : HermitianCoordinates K) : hermitianPurity y = hermitianPair y y := by
  simp [hermitianPurity,hermitianPair,pow_two]

lemma dualPurity_formula (k : Parameters K) (z : RealVector K) :
    dualPurity k z =
      ((dualP k z)^2*hermitianPair (hermitianInverse k hermitianIdentity) (hermitianInverse k hermitianIdentity)-
        2*(dualP k z)*(dualA k z)*hermitianPair (hermitianInverse k hermitianIdentity) (hermitianInverse k (hermitianProjector z))+
        (dualA k z)^2*hermitianPair (hermitianInverse k (hermitianProjector z)) (hermitianInverse k (hermitianProjector z)))/(dualDen k z)^2 := by
  rw [dualPurity,hermitianPurity_eq_pair]
  have hc : dualCoordinates k z = fun i =>
      (dualP k z*hermitianInverse k hermitianIdentity i-dualA k z*hermitianInverse k (hermitianProjector z) i)/dualDen k z := by
    funext i
    simp [dualCoordinates,reconstruction,dualDen,div_eq_mul_inv]
    ring
  rw [hc,reconstructed_pair_formula]

/-- All charged scalar tests, including the physical purity filter, are independent
of the sign/root representative. No division by p is introduced. -/
theorem dual_scalars_invariant (k : Parameters K) (z w : RealVector K)
    (h : QuadraticCoordinatesEq (hermitianProjector z) (hermitianProjector w)) :
    dualA k z = dualA k w ∧ dualP k z = dualP k w ∧ dualDen k z = dualDen k w ∧
      dualPurity k z = dualPurity k w ∧ dualEnergy k z = dualEnergy k w := by
  obtain ⟨ha,hp,hU,hV⟩ := inverseScalarInvariants k _ _ h
  have ha' : dualA k z = dualA k w := by
    unfold dualA
    rw [hermitianPair_comm (hermitianProjector z),hermitianPair_comm (hermitianProjector w)]
    exact ha
  have hp' : dualP k z = dualP k w := hp
  have hD : dualDen k z = dualDen k w := by simp only [dualDen,ha',hp']
  refine ⟨ha',hp',hD,?_,?_⟩
  · rw [dualPurity_formula,dualPurity_formula,ha',hp',hD,hU,hV]
  · simp only [dualEnergy,hp',hD]

/-- Direct endpoint for a common selected weighted candidate. -/
theorem matched_dual_scalars_invariant (k : Parameters K) (x : SpectrumPoint K) (z w : RealVector K)
    (hz : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2))
    (hw : PointMatches x (pairVector w 0) (pairVector w 1) (pairVector w 2)) :
    dualA k z = dualA k w ∧ dualP k z = dualP k w ∧ dualDen k z = dualDen k w ∧
      dualPurity k z = dualPurity k w ∧ dualEnergy k z = dualEnergy k w :=
  dual_scalars_invariant k z w (pointMatches_quadratic_eq x z w hz hw)

#print axioms inverseScalarInvariants
#print axioms pointMatches_quadratic_eq
#print axioms matched_dual_scalars_invariant
end W3.OperatorField
