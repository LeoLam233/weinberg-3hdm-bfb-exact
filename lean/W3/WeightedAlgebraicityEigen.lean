import W3.PrimalFieldBridge

/-! Cancellation of amplitude contractions, including every vanishing component.
This supplies the converse operator bridge over arbitrary ordered fields. -/
noncomputable section
namespace W3.PrimalFieldBridge
open W3.RealModel W3.StrataTransfer W3.Weighted W3.Elimination
open ComplexPair
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

lemma contraction_cancel (a b u v c : K) (hn : a^2+b^2 ≠ 0)
    (hr : a*u+b*v = c*(a^2+b^2)) (hi : a*v-b*u=0) :
    u=c*a ∧ v=c*b := by
  have hu : (a^2+b^2)*(u-c*a)=0 := by linear_combination a*hr-b*hi
  have hv : (a^2+b^2)*(v-c*b)=0 := by linear_combination b*hr+a*hi
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left hn),
    sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_left hn)⟩

/-- An absent amplitude gives an identically absent row of L(P)z. -/
lemma neutral_action_zero (κ : Parameters K) (z : RealVector K) (i : Fin 3)
    (hr : zRe z i=0) (hi : zIm z i=0) :
    actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i=0 ∧
    actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i=0 := by
  fin_cases i <;> simp [zRe,zIm] at hr hi <;>
    simp [actionRe,actionIm,operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,
      neutralFields,radii,offRe,offIm,zRe,zIm,Fin.sum_univ_three,hr,hi]

/-- The complete weighted amplitude system is sufficient for the actual
structured-operator eigen-equation on all three support strata. -/
theorem amplitudes_imply_neutral_eigen (κ : Parameters K) (z : RealVector K)
    (g₁ g₂ g₃ lam : K)
    (h : AmplitudeEquations (toSpectrum (originalPrimal κ))
      (pairVector z 0) (pairVector z 1) (pairVector z 2) g₁ g₂ g₃ lam) :
    ∀ i : Fin 3,
      actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i =
        lam*![g₁,g₂,g₃] i*zRe z i ∧
      actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i =
        lam*![g₁,g₂,g₃] i*zIm z i := by
  have hc := neutral_contraction κ z
  have hh : ∀ i : Fin 3,
      zRe z i*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i +
        zIm z i*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i =
        (lam*![g₁,g₂,g₃] i)*((zRe z i)^2+(zIm z i)^2) ∧
      zRe z i*actionIm (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i -
        zIm z i*actionRe (operatorRe κ (neutralFields z)) (operatorIm κ (neutralFields z)) z i = 0 := by
    unfold AmplitudeEquations at h
    rw [hc.1,hc.2.1,hc.2.2] at h
    intro i
    fin_cases i
    · exact ⟨congrArg ComplexPair.re h.1,congrArg ComplexPair.im h.1⟩
    · exact ⟨congrArg ComplexPair.re h.2.1,congrArg ComplexPair.im h.2.1⟩
    · exact ⟨congrArg ComplexPair.re h.2.2,congrArg ComplexPair.im h.2.2⟩
  intro i
  by_cases hn : (zRe z i)^2+(zIm z i)^2=0
  · have hr : zRe z i=0 := by nlinarith [sq_nonneg (zIm z i)]
    have hi : zIm z i=0 := by nlinarith [sq_nonneg (zRe z i)]
    simpa [hr,hi] using neutral_action_zero κ z i hr hi
  · exact contraction_cancel _ _ _ _ _ hn (hh i).1 (hh i).2

#print axioms amplitudes_imply_neutral_eigen
end W3.PrimalFieldBridge
