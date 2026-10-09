import W3.AlgebraicFieldCriterion
import W3.GenericOpen
import W3.WeightedAlgebraicityExecutionMatrices
import W3.PivotedGramFactor
import W3.InfinitesimalAlgebraicInvariance
import W3.InfinitesimalAlgebraicTowerExtension

/-! Full-scope integration: exact finite spectra, algebraic ordered-field signs,
sixteen executed residue stages, and the displayed two-pivot field reconstruction.
`ResidueOracles` is the explicit exact arithmetic/equality/root-enumeration
interface; no computability claim is made for arbitrary uncomputable real inputs. -/
noncomputable section
namespace W3
open RealModel Infinitesimal OperatorField TransferOperator Weighted.Expression StrataTransfer

/-- The concrete real Hermitian matrix returned by the nine residue programs. -/
def executedGram (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) : Matrix (Fin 3) (Fin 3) ℂ :=
  complexMatrix (hermitianRe (executeActualRetainedMatrix O κ y hy))
    (hermitianIm (executeActualRetainedMatrix O κ y hy))

/-- Every minimizing retained matrix, not just a specially chosen one, gives a
physical original matrix after the actual finite residue computation. -/
theorem executedGram_physical (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ) :
    PhysicalGram (executedGram O κ y hy) := by
  obtain ⟨phi,hphi,hgram,_⟩ := (executeActualRetainedMatrix_minimizing O κ y hy hv).2.2
  exact (physicalGram_iff_fields _).mpr ⟨phi,hphi,hgram.symm⟩

/-- Applying exactly the two-pivot formula to the executed residue. -/
def executedPivotFields (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ) : Fields :=
  PivotedGram.pivotedFields (executedGram O κ y hy) (executedGram_physical O κ y hy hv)

theorem executedPivotFields_spec (O : ResidueOracles) (κ : Parameters ℝ) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ)
    (hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ) :
    ‖executedPivotFields O κ y hy hv‖=1 ∧
      gram (executedPivotFields O κ y hy hv)=executedGram O κ y hy ∧
      quartic (couplings κ) (executedPivotFields O κ y hy hv)=executeActualMinimum O κ := by
  obtain ⟨phi,hphi,hgram,henergy⟩ := (executeActualRetainedMatrix_minimizing O κ y hy hv).2.2
  have hmin : gramQuartic (couplings κ) (executedGram O κ y hy)=realMinimum κ := by
    rw [executedGram,hgram,gramQuartic_gram]
    exact henergy
  exact ⟨PivotedGram.pivotedFields_normalized _ _,PivotedGram.pivotedFields_gram _ _,
    (PivotedGram.pivotedFields_value _ _ _).trans (hmin.trans (executeActualMinimum_eq O κ).symm)⟩

/-- Main theorem on all fifteen unrestricted real coordinates, including every
singular/zero/degenerate input. The bounded list is the literal filtered pair
of singleton/pair/sextic spectra, and the witness is the executed residue plus
the literal equation (41) pivot algorithm. -/
theorem full_exact_criterion (O : ResidueOracles) (κ : Parameters ℝ) :
    (actualCandidateValues κ).card≤30 ∧
    (actualCandidateValues κ).Nonempty ∧
    ((∀ K,PhysicalGram K→0≤gramQuartic (couplings κ) K) ↔ 0<algebraicCandidateMinimum κ) ∧
    ((∀ K,PhysicalGram K→0<gramQuartic (couplings κ) K) ↔
      2*algebraicEpsilon 0<algebraicCandidateMinimum κ) ∧
    (realMinimum κ<0 ↔ actualCandidateMinimum κ<0) ∧
    (realMinimum κ=0 ↔ 0<actualCandidateMinimum κ ∧ actualCandidateMinimum κ<2*chronologicalEpsilon 0) ∧
    executeActualMinimum O κ=realMinimum κ ∧
    (∀ y : Matrix16, ∀ hy : y ∈ actualRetainedMatrices κ,
      ∀ hv : hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ,
        ‖executedPivotFields O κ y hy hv‖=1 ∧
        gram (executedPivotFields O κ y hy hv)=executedGram O κ y hy ∧
        quartic (couplings κ) (executedPivotFields O κ y hy hv)=executeActualMinimum O κ) ∧
    (∃ y : Matrix16, ∃ hy : y ∈ actualRetainedMatrices κ,
      hermitianEnergy (actualParameters κ) y/2=actualCandidateMinimum κ) := by
  have h := universal_exact_criterion κ
  obtain ⟨y,hy,hv⟩ := actualMinimum_has_retainedMatrix κ
  exact ⟨h.1,h.2.1,(algebraic_field_sign_tests κ).1,(algebraic_field_sign_tests κ).2,
    h.2.2.2.2.1,h.2.2.2.2.2.1,executeActualMinimum_eq O κ,
    fun y hy hv=>executedPivotFields_spec O κ y hy hv,
    y,hy,hv.trans (actualCandidateMinimum_eq κ).symm⟩

#print axioms full_exact_criterion
#print axioms executedPivotFields_spec
end W3
