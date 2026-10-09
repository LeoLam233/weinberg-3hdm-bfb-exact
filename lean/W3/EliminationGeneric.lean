import W3.EliminationWitness

noncomputable section
namespace W3.Elimination
open Polynomial

section GenericRing
variable {R : Type*} [CommRing R]

def linearExceptional (p q : PhaseRow R) : R :=
  Polynomial.resultant (phaseSextic p q) (phaseLinearOne p q) 6 4

def poleExceptional (p q h : PhaseRow R) : R :=
  Polynomial.resultant (phaseSextic p q) (substitutedPhase p q h) 6 10

/-- Single division-free algebraic exclusion, expressed entirely in row coefficients. -/
def phaseExceptional (p q h : PhaseRow R) : R :=
  (phaseSextic p q).coeff 6 * boundaryT p q * boundaryU p q *
    linearExceptional p q * poleExceptional p q h

theorem phaseLinearOne_degree_le (p q : PhaseRow R) :
    (phaseLinearOne p q).natDegree ≤ 4 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le <;> apply natDegree_mul_le_of_le (m := 2) (n := 2)
  · exact phaseA_degree q
  · exact phaseB_degree p
  · exact phaseA_degree p
  · exact phaseB_degree q

theorem phaseLinearZero_degree_le (p q : PhaseRow R) :
    (phaseLinearZero p q).natDegree ≤ 4 := by
  apply (natDegree_sub_le _ _).trans
  apply max_le <;> apply natDegree_mul_le_of_le (m := 2) (n := 2)
  · exact phaseA_degree q
  · exact phaseC_degree p
  · exact phaseA_degree p
  · exact phaseC_degree q

theorem substitutedPhase_degree_le (p q h : PhaseRow R) :
    (substitutedPhase p q h).natDegree ≤ 10 := by
  apply natDegree_add_le_of_degree_le
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le_of_le (phaseA_degree h)
        (natDegree_pow_le_of_le 2 (phaseLinearZero_degree_le p q))
    · exact natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (phaseB_degree h) (phaseLinearZero_degree_le p q))
        (phaseLinearOne_degree_le p q)
  · exact natDegree_mul_le_of_le (phaseC_degree h)
      (natDegree_pow_le_of_le 2 (phaseLinearOne_degree_le p q))

end GenericRing

section GenericField
variable {K : Type*} [Field K]

/-- A fixed-size Sylvester determinant supplies an exact polynomial Bezout certificate. -/
theorem certificate_of_resultant_ne_zero (S L : K[X]) (m n : ℕ)
    (hS : S.natDegree ≤ m) (hL : L.natDegree ≤ n) (hsize : m ≠ 0 ∨ n ≠ 0)
    (hr : Polynomial.resultant S L m n ≠ 0) :
    ∃ A B, BezoutCertificate S L A B := by
  obtain ⟨A, B, _, _, he⟩ := exists_mul_add_mul_eq_C_resultant S L hS hL hsize
  have he' : A * S + B * L = C (Polynomial.resultant S L m n) := by
    simpa only [mul_comm] using he
  exact ⟨_, _, certificate_of_nonzero_constant he' hr⟩

theorem linear_certificate_of_exceptional_ne_zero (p q : PhaseRow K)
    (h : linearExceptional p q ≠ 0) :
    ∃ A B, BezoutCertificate (phaseSextic p q) (phaseLinearOne p q) A B :=
  certificate_of_resultant_ne_zero _ _ 6 4 (phase_sextic_degree_le p q)
    (phaseLinearOne_degree_le p q) (by decide) h

theorem pole_certificate_of_exceptional_ne_zero (p q h : PhaseRow K)
    (he : poleExceptional p q h ≠ 0) :
    ∃ A B, BezoutCertificate (phaseSextic p q) (substitutedPhase p q h) A B :=
  certificate_of_resultant_ne_zero _ _ 6 10 (phase_sextic_degree_le p q)
    (substitutedPhase_degree_le p q h) (by decide) he

theorem phaseExceptional_properties (p q h : PhaseRow K)
    (he : phaseExceptional p q h ≠ 0) :
    phaseSextic p q ≠ 0 ∧ boundaryT p q ≠ 0 ∧ boundaryU p q ≠ 0 ∧
      linearExceptional p q ≠ 0 ∧ poleExceptional p q h ≠ 0 := by
  unfold phaseExceptional at he
  rcases mul_ne_zero_iff.mp he with ⟨he, hh⟩
  rcases mul_ne_zero_iff.mp he with ⟨he, hl⟩
  rcases mul_ne_zero_iff.mp he with ⟨he, hu⟩
  rcases mul_ne_zero_iff.mp he with ⟨hs, ht⟩
  refine ⟨?_, ht, hu, hl, hh⟩
  intro hz
  simpa [hz] using hs

end GenericField

section GenericOrdered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Complete selected-root equivalence and pole exclusion from one concrete algebraic nonvanishing. -/
theorem generic_phase_candidates_exact (p q h : PhaseRow K)
    (he : phaseExceptional p q h ≠ 0) (t u : K) :
    ((t, u) ∈ phaseCandidates p q ↔ phaseValue p t u = 0 ∧ phaseValue q t u = 0) ∧
    ((t, u) ∈ phaseCandidates p q → phaseValue h t u ≠ 0) := by
  obtain ⟨hs, _, _, hl, hh⟩ := phaseExceptional_properties p q h he
  obtain ⟨A, B, hc⟩ := linear_certificate_of_exceptional_ne_zero p q hl
  obtain ⟨AH, BH, hcH⟩ := pole_certificate_of_exceptional_ne_zero p q h hh
  have hm := mem_phaseCandidates_iff p q A B hc hs t u
  refine ⟨hm, ?_⟩
  intro hz
  obtain ⟨hF, hG⟩ := hm.mp hz
  exact phase_exclusion p q h AH BH hcH t u hF hG

theorem generic_projective_candidates_exact (p q h : PhaseRow K)
    (he : phaseExceptional p q h ≠ 0)
    (t₀ t₁ u₀ u₁ : K) (ht : t₀ ≠ 0 ∨ t₁ ≠ 0) (hu : u₀ ≠ 0 ∨ u₁ ≠ 0) :
    (phaseHom p t₀ t₁ u₀ u₁ = 0 ∧ phaseHom q t₀ t₁ u₀ u₁ = 0) ↔
    (t₀ ≠ 0 ∧ u₀ ≠ 0 ∧ (t₁ / t₀, u₁ / u₀) ∈ phaseCandidates p q) := by
  obtain ⟨hs, hbt, hbu, hl, _⟩ := phaseExceptional_properties p q h he
  obtain ⟨A, B, hc⟩ := linear_certificate_of_exceptional_ne_zero p q hl
  rw [mem_phaseCandidates_iff p q A B hc hs]
  constructor
  · rintro ⟨hF, hG⟩
    obtain ⟨ht0, hu0⟩ := phaseHom_denominators_ne_zero p q t₀ t₁ u₀ u₁ ht hu hbt hbu hF hG
    exact ⟨ht0, hu0, (phaseHom_zero_iff_affine p _ _ _ _ ht0 hu0).mp hF,
      (phaseHom_zero_iff_affine q _ _ _ _ ht0 hu0).mp hG⟩
  · rintro ⟨ht0, hu0, hF, hG⟩
    exact ⟨(phaseHom_zero_iff_affine p _ _ _ _ ht0 hu0).mpr hF,
      (phaseHom_zero_iff_affine q _ _ _ _ ht0 hu0).mpr hG⟩

theorem witness_sextic_degree : (phaseSextic (witnessP : PhaseRow K) witnessQ).natDegree = 6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (phase_sextic_degree_le _ _)
  rw [witness_sextic]
  norm_num [witnessS, coeff_X]

theorem witness_linear_degree : (phaseLinearOne (witnessP : PhaseRow K) witnessQ).natDegree = 4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (phaseLinearOne_degree_le _ _)
  rw [witness_linear]
  norm_num [witnessL, coeff_X]

theorem witness_pole_degree :
    (substitutedPhase (witnessP : PhaseRow K) witnessQ witnessH).natDegree = 10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (substitutedPhase_degree_le _ _ _)
  rw [witness_pole]
  norm_num [witnessPole, coeff_X]

theorem witness_linearExceptional_ne_zero : linearExceptional (witnessP : PhaseRow K) witnessQ ≠ 0 := by
  unfold linearExceptional
  rw [← witness_sextic_degree (K := K), ← witness_linear_degree (K := K)]
  obtain ⟨A, B, hc⟩ := witness_L_certificate (K := K)
  exact resultant_ne_zero _ _ ⟨A, B, hc⟩

theorem witness_poleExceptional_ne_zero :
    poleExceptional (witnessP : PhaseRow K) witnessQ witnessH ≠ 0 := by
  unfold poleExceptional
  rw [← witness_sextic_degree (K := K), ← witness_pole_degree (K := K)]
  obtain ⟨A, B, hc⟩ := witness_H_certificate (K := K)
  exact resultant_ne_zero _ _ ⟨A, B, hc⟩

/-- Nonemptiness for the explicit algebraic generic set, in every ordered field. -/
theorem witness_phaseExceptional_ne_zero :
    phaseExceptional (witnessP : PhaseRow K) witnessQ witnessH ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · rw [witness_sextic]
          norm_num [witnessS, coeff_X]
        · exact witness_boundaryT_ne_zero
      · exact witness_boundaryU_ne_zero
    · exact witness_linearExceptional_ne_zero
  · exact witness_poleExceptional_ne_zero

end GenericOrdered
end W3.Elimination
