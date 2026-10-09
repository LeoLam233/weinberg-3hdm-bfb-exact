import W3.OperatorFieldCandidates

/-! Literal equality of the reconstructed charged energies and denominator
test with the source's common-spectrum quotient formula. -/
noncomputable section
namespace W3.OperatorField
open W3.TransferOperator W3.Elimination W3.RealModel W3.StrataTransfer W3.PrimalFieldBridge W3.Weighted
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

lemma quotient_energy_identity (beta a p : K) (ha : a ≠ 0) :
    p/(2*denominator beta a p) = (p/a^2)/(2*(beta*(p/a^2)-1)) := by
  have hden : beta*(p/a^2)-1 = denominator beta a p/a^2 := by
    unfold denominator
    field_simp [ha]
  rw [hden,← mul_div_assoc,div_div]
  field_simp [ha]

lemma candidateVector_dualA_ne_zero (k : Parameters K)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) (q : CandidateIndex (originalDual k)) :
    dualA k (candidateVector _ hd q) ≠ 0 := by
  rw [dualA_eq_weight]
  exact (candidateVector_spec _ hd q).2.2.1

/-- Exactly E=ν/[2(βν−1)], with ν the literal common-spectrum value. -/
theorem candidate_dualEnergy_formula (k : Parameters K)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) (q : CandidateIndex (originalDual k)) :
    dualEnergy k (candidateVector _ hd q) =
      spectrumValue (originalDual k) q.val/(2*(dualBeta k*spectrumValue (originalDual k) q.val-1)) := by
  rw [pointMatches_dual_value k q.val _ (candidateVector_spec _ hd q).1]
  exact quotient_energy_identity _ _ _ (candidateVector_dualA_ne_zero k hd q)

/-- Exactly the source's spectral denominator test, with no restriction ν≠0. -/
theorem candidate_dualDen_formula (k : Parameters K)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) (q : CandidateIndex (originalDual k)) :
    dualBeta k*spectrumValue (originalDual k) q.val-1 =
      dualDen k (candidateVector _ hd q)/(dualA k (candidateVector _ hd q))^2 := by
  rw [pointMatches_dual_value k q.val _ (candidateVector_spec _ hd q).1]
  dsimp [dualDen,denominator]
  field_simp [candidateVector_dualA_ne_zero k hd q]

theorem candidate_dualDen_ne_zero_iff (k : Parameters K)
    (hd : completeWeightedExceptional (originalDual k) ≠ 0) (q : CandidateIndex (originalDual k)) :
    dualDen k (candidateVector _ hd q) ≠ 0 ↔ dualBeta k*spectrumValue (originalDual k) q.val-1 ≠ 0 := by
  rw [candidate_dualDen_formula k hd q]
  simp [candidateVector_dualA_ne_zero k hd q]

#print axioms candidate_dualEnergy_formula
#print axioms candidate_dualDen_ne_zero_iff
end W3.OperatorField
