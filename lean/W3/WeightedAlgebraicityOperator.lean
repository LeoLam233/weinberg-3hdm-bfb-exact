import W3.WeightedAlgebraicityActual
import W3.OperatorFieldCharged

/-! Algebraicity of the physical real-nine-coordinate projectors, inverse
operator reconstruction, purity and energy. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace W3.Weighted
open W3.Elimination W3.Infinitesimal W3.OperatorField W3.TransferOperator
open W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge ComplexPair
section Generic
variable {F L : Type*} [Field F] [Field L] [Algebra F L] [LinearOrder L] [IsStrictOrderedRing L]

theorem matched_hermitianProjector_algebraic (x : SpectrumPoint L) (hx : AlgebraicPoint F x)
    (z : RealVector L) (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∀ i, IsAlgebraic F (hermitianProjector z i) := by
  obtain ⟨h0,h1,h2,h3,h5,h7⟩ := matched_projector_algebraic x hx _ _ _ hm
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

theorem inverseParameters_algebraic (k : Parameters L) (hk : ∀ i, IsAlgebraic F (k i)) :
    ∀ i, IsAlgebraic F (inverseParameters k i) := by
  intro i
  fin_cases i <;>
    simp only [inverseParameters,originalAdj,originalMatrixDet,originalDelta12,
      originalDelta13,originalDelta23,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons]
  all_goals
    repeat' first
    | exact hk _
    | exact isAlgebraic_natCast _
    | apply IsAlgebraic.add
    | apply IsAlgebraic.sub
    | apply IsAlgebraic.mul
    | apply algebraic_div
    | apply IsAlgebraic.neg
    | apply IsAlgebraic.pow

theorem hermitianOperator_algebraic (k : Parameters L) (y : HermitianCoordinates L)
    (hk : ∀ i, IsAlgebraic F (k i)) (hy : ∀ i, IsAlgebraic F (y i)) :
    ∀ i, IsAlgebraic F (hermitianOperator k y i) := by
  intro i
  fin_cases i <;> simp only [hermitianOperator,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons]
  all_goals repeat' first | exact hk _ | exact hy _ |
    apply IsAlgebraic.add | apply IsAlgebraic.sub | apply IsAlgebraic.mul

theorem hermitianInverse_algebraic (k : Parameters L) (y : HermitianCoordinates L)
    (hk : ∀ i, IsAlgebraic F (k i)) (hy : ∀ i, IsAlgebraic F (y i)) :
    ∀ i, IsAlgebraic F (hermitianInverse k y i) :=
  hermitianOperator_algebraic _ _ (inverseParameters_algebraic k hk) hy

theorem hermitianIdentity_algebraic : ∀ i, IsAlgebraic F ((hermitianIdentity : HermitianCoordinates L) i) := by
  intro i
  fin_cases i <;> simp only [hermitianIdentity,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons] <;> first | exact isAlgebraic_zero | exact isAlgebraic_one

theorem hermitianPair_algebraic (y w : HermitianCoordinates L)
    (hy : ∀ i, IsAlgebraic F (y i)) (hw : ∀ i, IsAlgebraic F (w i)) :
    IsAlgebraic F (hermitianPair y w) := by
  unfold hermitianPair
  repeat' first | exact hy _ | exact hw _ | exact isAlgebraic_natCast _ |
    apply IsAlgebraic.add | apply IsAlgebraic.mul

theorem dual_scalars_algebraic (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, IsAlgebraic F (k i)) (hz : ∀ i, IsAlgebraic F (hermitianProjector z i)) :
    IsAlgebraic F (dualBeta k) ∧ IsAlgebraic F (dualA k z) ∧
    IsAlgebraic F (dualP k z) ∧ IsAlgebraic F (dualDen k z) := by
  have hI := hermitianInverse_algebraic k hermitianIdentity hk (hermitianIdentity_algebraic (F:=F) (L:=L))
  have hP := hermitianInverse_algebraic k (hermitianProjector z) hk hz
  have hβ : IsAlgebraic F (dualBeta k) := hermitianPair_algebraic _ _ hermitianIdentity_algebraic hI
  have ha : IsAlgebraic F (dualA k z) := hermitianPair_algebraic _ _ hz hI
  have hp : IsAlgebraic F (dualP k z) := hermitianPair_algebraic _ _ hz hP
  exact ⟨hβ,ha,hp,(hβ.mul hp).sub (ha.pow 2)⟩

theorem dualCoordinates_algebraic (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, IsAlgebraic F (k i)) (hz : ∀ i, IsAlgebraic F (hermitianProjector z i)) :
    ∀ i, IsAlgebraic F (dualCoordinates k z i) := by
  obtain ⟨hβ,ha,hp,hD⟩ := dual_scalars_algebraic k z hk hz
  have hI := hermitianInverse_algebraic k hermitianIdentity hk (hermitianIdentity_algebraic (F:=F) (L:=L))
  have hP := hermitianInverse_algebraic k (hermitianProjector z) hk hz
  intro i
  change IsAlgebraic F ((dualP k z / dualDen k z) * hermitianInverse k hermitianIdentity i -
    (dualA k z / dualDen k z) * hermitianInverse k (hermitianProjector z) i)
  exact ((algebraic_div hp hD).mul (hI i)).sub ((algebraic_div ha hD).mul (hP i))

theorem dualEnergy_algebraic (k : Parameters L) (z : RealVector L)
    (hk : ∀ i, IsAlgebraic F (k i)) (hz : ∀ i, IsAlgebraic F (hermitianProjector z i)) :
    IsAlgebraic F (dualEnergy k z) := by
  obtain ⟨_,_,hp,hD⟩ := dual_scalars_algebraic k z hk hz
  exact algebraic_div hp ((isAlgebraic_natCast 2).mul hD)

end Generic
end W3.Weighted
