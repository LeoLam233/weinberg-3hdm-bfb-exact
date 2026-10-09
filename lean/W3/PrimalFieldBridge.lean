import W3.StrataTransfer
import W3.WeightedValue
import W3.ActualMinimum

/-! The neutral part of the physical/weighted bridge in arbitrary ordered
fields, using only real coordinate polynomials and squared complex amplitudes. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.PrimalFieldBridge
open W3.RealModel W3.StrataTransfer W3.Weighted W3.Elimination
open ComplexPair
open scoped BigOperators
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def pairVector (z : RealVector K) (i : Fin 3) : ComplexPair K := ⟨zRe z i,zIm z i⟩

/-- One nonzero row, conjugated to realize P=z z† with the original Gram convention. -/
def neutralFields (z : RealVector K) : RealFields K :=
  ![z 0,-z 1,z 2,-z 3,z 4,-z 5,0,0,0,0,0,0]

lemma neutralFields_mass (z : RealVector K) : mass (neutralFields z) = zMass z := by
  simp [mass, neutralFields, zMass, zRe, zIm, Fin.sum_univ_succ]
  ring

lemma neutralFields_gramRe (z : RealVector K) (i j : Fin 3) :
    gramRe (neutralFields z) i j = projectorRe z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gramRe,neutralFields,radii,offRe,projectorRe,zRe,zIm] <;> ring
lemma neutralFields_gramIm (z : RealVector K) (i j : Fin 3) :
    gramIm (neutralFields z) i j = projectorIm z i j := by
  fin_cases i <;> fin_cases j <;>
    simp [gramIm,neutralFields,offIm,projectorIm,zRe,zIm] <;> ring

lemma pairVector_norm_sum (z : RealVector K) :
    normSq (pairVector z 0)+normSq (pairVector z 1)+normSq (pairVector z 2) = zMass z := by
  simp [zMass,pairVector,normSq,Fin.sum_univ_three]

/-- Exact energy identity, with the source's half-normalization and arbitrary complex d. -/
theorem neutralFields_energy (κ : Parameters K) (z : RealVector K) :
    quarticReal κ (neutralFields z) = amplitudeEnergy (toSpectrum (originalPrimal κ))
      (pairVector z 0) (pairVector z 1) (pairVector z 2) := by
  simp [quarticReal,twiceQuartic,neutralFields,radii,offRe,offIm,amplitudeEnergy,
    amplitudeRow₁,amplitudeRow₂,amplitudeRow₃,amplitudeEdge,toSpectrum,originalPrimal,
    pairVector,zRe,zIm,normSq,mul,conj]
  ring

lemma gram_equal_coordinates (x y : RealFields K)
    (h : ∀ i j, gramRe x i j = gramRe y i j ∧ gramIm x i j = gramIm y i j) :
    radii x = radii y ∧ offRe x = offRe y ∧ offIm x = offIm y := by
  refine ⟨?_,?_,?_⟩
  · funext i
    fin_cases i
    · exact (h 0 0).1
    · exact (h 1 1).1
    · exact (h 2 2).1
  · funext i
    fin_cases i
    · exact (h 0 1).1
    · exact (h 0 2).1
    · exact (h 1 2).1
  · funext i
    fin_cases i
    · exact (h 0 1).2
    · exact (h 0 2).2
    · exact (h 1 2).2

lemma gram_projector_coordinates (x : RealFields K) (z : RealVector K)
    (h : ∀ i j, gramRe x i j = projectorRe z i j ∧ gramIm x i j = projectorIm z i j) :
    radii x = radii (neutralFields z) ∧ offRe x = offRe (neutralFields z) ∧
      offIm x = offIm (neutralFields z) := by
  apply gram_equal_coordinates
  intro i j
  rw [neutralFields_gramRe,neutralFields_gramIm]
  exact h i j

lemma gram_equal_operators (κ : Parameters K) (x y : RealFields K)
    (hr : radii x = radii y) (hR : offRe x = offRe y) (hI : offIm x = offIm y) :
    operatorRe κ x = operatorRe κ y ∧ operatorIm κ x = operatorIm κ y := by
  simp only [operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,hr,hR,hI,and_self]

lemma neutral_contraction (κ : Parameters K) (z : RealVector K) :
    amplitudeRow₁ (toSpectrum (originalPrimal κ)) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 0*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 0 +
        zIm z 0*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 0,
       zRe z 0*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 0 -
        zIm z 0*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 0⟩ ∧
    amplitudeRow₂ (toSpectrum (originalPrimal κ)) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 1*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 1 +
        zIm z 1*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 1,
       zRe z 1*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 1 -
        zIm z 1*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 1⟩ ∧
    amplitudeRow₃ (toSpectrum (originalPrimal κ)) (pairVector z 0) (pairVector z 1) (pairVector z 2) =
      ⟨zRe z 2*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 2 +
        zIm z 2*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 2,
       zRe z 2*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 2 -
        zIm z 2*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z 2⟩ := by
  constructor
  · apply complexPair_ext <;>
      simp [amplitudeRow₁,amplitudeEdge,toSpectrum,originalPrimal,pairVector,zRe,zIm,normSq,mul,conj,
        actionRe,actionIm,operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,
        neutralFields,radii,offRe,offIm,Fin.sum_univ_three] <;> ring
  constructor
  · apply complexPair_ext <;>
      simp [amplitudeRow₂,amplitudeEdge,toSpectrum,originalPrimal,pairVector,zRe,zIm,normSq,mul,conj,
        actionRe,actionIm,operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,
        neutralFields,radii,offRe,offIm,Fin.sum_univ_three] <;> ring
  · apply complexPair_ext <;>
      simp [amplitudeRow₃,amplitudeEdge,toSpectrum,originalPrimal,pairVector,zRe,zIm,normSq,mul,conj,
        actionRe,actionIm,operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,
        neutralFields,radii,offRe,offIm,Fin.sum_univ_three] <;> ring

/-- The actual neutral stationary stratum implies the complete common weighted
amplitude equations, even when some doublets vanish. -/
theorem neutral_stratum_amplitudes (κ : Parameters K) (x : RealFields K) (z : RealVector K)
    (hG : ∀ i j, gramRe x i j = projectorRe z i j ∧ gramIm x i j = projectorIm z i j)
    (hE : ∀ i, actionRe (operatorRe κ x) (operatorIm κ x) z i = twiceQuartic κ x*zRe z i ∧
      actionIm (operatorRe κ x) (operatorIm κ x) z i = twiceQuartic κ x*zIm z i) :
    AmplitudeEquations (toSpectrum (originalPrimal κ)) (pairVector z 0) (pairVector z 1) (pairVector z 2)
      1 1 1 (twiceQuartic κ x) := by
  obtain ⟨hr,hR,hI⟩ := gram_projector_coordinates x z hG
  obtain ⟨hOpR,hOpI⟩ := gram_equal_operators κ x (neutralFields z) hr hR hI
  have hc := neutral_contraction κ z
  rw [← hOpR, ← hOpI] at hc
  unfold AmplitudeEquations
  rw [hc.1,hc.2.1,hc.2.2,(hE 0).1,(hE 0).2,(hE 1).1,(hE 1).2,(hE 2).1,(hE 2).2]
  constructor
  · apply complexPair_ext <;> simp [pairVector,normSq] <;> ring
  constructor <;> apply complexPair_ext <;> simp [pairVector,normSq] <;> ring

/-- The actual field value equals the represented neutral amplitude value. -/
theorem neutral_stratum_energy (κ : Parameters K) (x : RealFields K) (z : RealVector K)
    (hG : ∀ i j, gramRe x i j = projectorRe z i j ∧ gramIm x i j = projectorIm z i j) :
    quarticReal κ x = amplitudeEnergy (toSpectrum (originalPrimal κ))
      (pairVector z 0) (pairVector z 1) (pairVector z 2) := by
  obtain ⟨hr,hR,hI⟩ := gram_projector_coordinates x z hG
  rw [← neutralFields_energy]
  simp only [quarticReal,twiceQuartic,hr,hR,hI]

#print axioms neutralFields_energy
#print axioms neutral_stratum_amplitudes
end Ordered
end W3.PrimalFieldBridge
