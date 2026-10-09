import W3.WeightedAlgebraicityExpressionsActual
import W3.OperatorFieldCharged

set_option maxHeartbeats 1000000
noncomputable section
namespace W3.Weighted.Expression
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge ComplexPair

section Generic
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

theorem matched_hermitianProjector_presented (x : SpectrumPoint L) (hx : PresentedPoint F x)
    (z : RealVector L) (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∀ i, Presented F (hermitianProjector z i) := by
  obtain ⟨h0,h1,h2,h3,h5,h7⟩ := matched_projector_presented x hx _ _ _ hm
  have he (i j : Fin 3) : mul (pairVector z i) (conj (pairVector z j)) =
      ⟨projectorRe z i j,projectorIm z i j⟩ := by
    apply complexPair_ext <;> simp [mul,conj,pairVector,projectorRe,projectorIm] <;> ring
  rw [he] at h3 h5 h7
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3.1
  · exact h3.2
  · exact h5.1
  · exact h5.2
  · exact h7.1
  · exact h7.2

theorem inverseParameters_presented (k : Parameters L) (hk : ∀ i, Presented F (k i)) :
    ∀ i, Presented F (inverseParameters k i) := by
  intro i
  fin_cases i <;>
    simp only [inverseParameters,originalAdj,originalMatrixDet,originalDelta12,
      originalDelta13,originalDelta23,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons]
  all_goals
    repeat' first
    | exact hk _
    | exact expr_natCast _
    | apply Presented.add
    | apply Presented.sub
    | apply Presented.mul
    | apply presented_div
    | apply Presented.neg
    | apply Presented.pow

theorem hermitianOperator_presented (k : Parameters L) (y : HermitianCoordinates L)
    (hk : ∀ i, Presented F (k i)) (hy : ∀ i, Presented F (y i)) :
    ∀ i, Presented F (hermitianOperator k y i) := by
  intro i
  fin_cases i <;> simp only [hermitianOperator,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  all_goals
    repeat' first
    | exact hk _
    | exact hy _
    | apply Presented.add
    | apply Presented.sub
    | apply Presented.mul

theorem hermitianInverse_presented (k : Parameters L) (y : HermitianCoordinates L)
    (hk : ∀ i, Presented F (k i)) (hy : ∀ i, Presented F (y i)) :
    ∀ i, Presented F (hermitianInverse k y i) :=
  hermitianOperator_presented _ _ (inverseParameters_presented k hk) hy

theorem hermitianIdentity_presented : ∀ i, Presented F ((hermitianIdentity : HermitianCoordinates L) i) := by
  intro i
  fin_cases i <;> simp only [hermitianIdentity,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons] <;> first | exact expr_zero | exact expr_one

theorem hermitianPair_presented (y w : HermitianCoordinates L)
    (hy : ∀ i, Presented F (y i)) (hw : ∀ i, Presented F (w i)) :
    Presented F (hermitianPair y w) := by
  unfold hermitianPair
  repeat' first
  | exact hy _
  | exact hw _
  | exact expr_natCast _
  | apply Presented.add
  | apply Presented.mul

theorem dual_scalars_presented (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, Presented F (k i)) (hz : ∀ i, Presented F (hermitianProjector z i)) :
    Presented F (dualBeta k) ∧ Presented F (dualA k z) ∧
    Presented F (dualP k z) ∧ Presented F (dualDen k z) := by
  have hI := hermitianInverse_presented k hermitianIdentity hk (hermitianIdentity_presented (F:=F) (L:=L))
  have hP := hermitianInverse_presented k (hermitianProjector z) hk hz
  have hβ : Presented F (dualBeta k) := hermitianPair_presented _ _ hermitianIdentity_presented hI
  have ha : Presented F (dualA k z) := hermitianPair_presented _ _ hz hI
  have hp : Presented F (dualP k z) := hermitianPair_presented _ _ hz hP
  exact ⟨hβ,ha,hp,(hβ.mul hp).sub (ha.pow 2)⟩

theorem dualCoordinates_presented (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, Presented F (k i)) (hz : ∀ i, Presented F (hermitianProjector z i)) :
    ∀ i, Presented F (dualCoordinates k z i) := by
  obtain ⟨hβ,ha,hp,hD⟩ := dual_scalars_presented k z hk hz
  have hI := hermitianInverse_presented k hermitianIdentity hk (hermitianIdentity_presented (F:=F) (L:=L))
  have hP := hermitianInverse_presented k (hermitianProjector z) hk hz
  intro i
  change Presented F ((dualP k z / dualDen k z) * hermitianInverse k hermitianIdentity i -
    (dualA k z / dualDen k z) * hermitianInverse k (hermitianProjector z) i)
  exact ((presented_div hp hD).mul (hI i)).sub ((presented_div ha hD).mul (hP i))

theorem dualEnergy_presented (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, Presented F (k i)) (hz : ∀ i, Presented F (hermitianProjector z i)) :
    Presented F (dualEnergy k z) := by
  obtain ⟨_,_,hp,hD⟩ := dual_scalars_presented k z hk hz
  exact presented_div hp ((expr_natCast 2).mul hD)

end Generic

end W3.Weighted.Expression
