import W3.EliminationPhase

noncomputable section

namespace W3.Elimination
open Polynomial

section Certificates
variable {K : Type*} [Field K]

/-- Explicit polynomial Bezout identity; no assumption about stationarity or coverage. -/
def BezoutCertificate (S L A B : K[X]) : Prop := A * S + B * L = 1

theorem certificate_nonvanishing {S L A B : K[X]} (h : BezoutCertificate S L A B)
    {t : K} (hS : S.eval t = 0) : L.eval t ≠ 0 := by
  intro hL
  have he := congrArg (fun p : K[X] => p.eval t) h
  simp only [eval_add, eval_mul, eval_one, hS, hL, mul_zero, add_zero] at he
  exact zero_ne_one he

/-- Integer-scaled Bezout identities can be normalized in any field. -/
theorem certificate_of_nonzero_constant {S L A B : K[X]} {k : K}
    (h : A * S + B * L = C k) (hk : k ≠ 0) :
    BezoutCertificate S L (C k⁻¹ * A) (C k⁻¹ * B) := by
  unfold BezoutCertificate
  calc
    C k⁻¹ * A * S + C k⁻¹ * B * L = C k⁻¹ * (A * S + B * L) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hk, C_1]

end Certificates

section PhasePolynomial
variable {K : Type*} [CommRing K]

def phaseLinearOne (p q : PhaseRow K) : K[X] :=
  linearOne (phaseA p) (phaseB p) (phaseA q) (phaseB q)

def phaseLinearZero (p q : PhaseRow K) : K[X] :=
  linearZero (phaseA p) (phaseC p) (phaseA q) (phaseC q)

@[simp] theorem eval_phaseLinearOne (p q : PhaseRow K) (t : K) :
    (phaseLinearOne p q).eval t =
      linearOne ((phaseA p).eval t) ((phaseB p).eval t)
        ((phaseA q).eval t) ((phaseB q).eval t) := by
  simp [phaseLinearOne, linearOne]

@[simp] theorem eval_phaseLinearZero (p q : PhaseRow K) (t : K) :
    (phaseLinearZero p q).eval t =
      linearZero ((phaseA p).eval t) ((phaseC p).eval t)
        ((phaseA q).eval t) ((phaseC q).eval t) := by
  simp [phaseLinearZero, linearZero]

@[simp] theorem eval_phaseResultant (p q : PhaseRow K) (t : K) :
    (phaseResultant p q).eval t =
      resultant₂ ((phaseA p).eval t) ((phaseB p).eval t) ((phaseC p).eval t)
        ((phaseA q).eval t) ((phaseB q).eval t) ((phaseC q).eval t) := by
  simp [phaseResultant, resultant₂]

/-- Denominator-cleared substitution into an additional phase equation. -/
def substitutedPhase (p q h : PhaseRow K) : K[X] :=
  phaseA h * phaseLinearZero p q ^ 2 -
  phaseB h * phaseLinearZero p q * phaseLinearOne p q +
  phaseC h * phaseLinearOne p q ^ 2

theorem substitutedPhase_identity (p q h : PhaseRow K) (t u : K)
    (hF : phaseValue p t u = 0) (hG : phaseValue q t u = 0) :
    (substitutedPhase p q h).eval t =
      (phaseLinearOne p q).eval t ^ 2 * phaseValue h t u := by
  rw [phaseValue_eq_quad] at hF hG
  have hlin := eliminate_linear _ _ _ _ _ _ _ hF hG
  have hz : (phaseLinearZero p q).eval t = -(phaseLinearOne p q).eval t * u := by
    simp only [eval_phaseLinearZero, eval_phaseLinearOne]
    linear_combination hlin
  simp only [substitutedPhase, eval_sub, eval_mul, eval_add, eval_pow, hz,
    phaseValue_eq_quad, quad]
  ring

end PhasePolynomial

section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem circle_eval_ne_zero (t : K) : (circlePoly : K[X]).eval t ≠ 0 := by
  simp only [circlePoly, eval_add, eval_one, eval_pow, eval_X]
  have hs := sq_nonneg t
  linarith

theorem common_phase_root_sextic (p q : PhaseRow K) (t u : K)
    (hF : phaseValue p t u = 0) (hG : phaseValue q t u = 0) :
    (phaseSextic p q).eval t = 0 := by
  have hr : (phaseResultant p q).eval t = 0 := by
    rw [eval_phaseResultant]
    rw [phaseValue_eq_quad] at hF hG
    exact common_root_resultant _ _ _ _ _ _ _ hF hG
  rw [phase_resultant_factor, eval_mul] at hr
  exact (mul_eq_zero.mp hr).resolve_left (circle_eval_ne_zero t)

/-- The sextic plus its linear recovery is exactly the two original phase equations. -/
theorem phase_root_iff (p q : PhaseRow K) (A B : K[X])
    (hcert : BezoutCertificate (phaseSextic p q) (phaseLinearOne p q) A B) (t u : K) :
    (phaseValue p t u = 0 ∧ phaseValue q t u = 0) ↔
    ((phaseSextic p q).eval t = 0 ∧
      u = -(phaseLinearZero p q).eval t / (phaseLinearOne p q).eval t) := by
  constructor
  · rintro ⟨hF, hG⟩
    have hS := common_phase_root_sextic p q t u hF hG
    refine ⟨hS, ?_⟩
    have hL := certificate_nonvanishing hcert hS
    rw [eval_phaseLinearOne] at hL
    rw [eval_phaseLinearZero, eval_phaseLinearOne]
    rw [phaseValue_eq_quad] at hF hG
    exact recover_common_root _ _ _ _ _ _ _ hL hF hG
  · rintro ⟨hS, rfl⟩
    have hL := certificate_nonvanishing hcert hS
    have hR : (phaseResultant p q).eval t = 0 := by
      rw [phase_resultant_factor, eval_mul, hS, mul_zero]
    rw [eval_phaseResultant] at hR
    rw [eval_phaseLinearOne] at hL
    simp only [phaseValue_eq_quad, eval_phaseLinearZero, eval_phaseLinearOne]
    exact ⟨resultant_root_recovers_left _ _ _ _ _ _ hL hR,
      resultant_root_recovers_right _ _ _ _ _ _ hL hR⟩

/-- A second explicit Bezout identity excludes an additional phase equation on every common root. -/
theorem phase_exclusion (p q h : PhaseRow K) (A B : K[X])
    (hcert : BezoutCertificate (phaseSextic p q) (substitutedPhase p q h) A B)
    (t u : K) (hF : phaseValue p t u = 0) (hG : phaseValue q t u = 0) :
    phaseValue h t u ≠ 0 := by
  intro hH
  have hS := common_phase_root_sextic p q t u hF hG
  have hne := certificate_nonvanishing hcert hS
  apply hne
  rw [substitutedPhase_identity p q h t u hF hG, hH, mul_zero]

/-- Any finite set of distinct affine phase solutions has at most six members. -/
theorem phase_solution_card_le_six (p q : PhaseRow K) (A B : K[X])
    (hcert : BezoutCertificate (phaseSextic p q) (phaseLinearOne p q) A B)
    (hS : phaseSextic p q ≠ 0) (Z : Finset (K × K))
    (hZ : ∀ z ∈ Z, phaseValue p z.1 z.2 = 0 ∧ phaseValue q z.1 z.2 = 0) :
    Z.card ≤ 6 := by
  classical
  have hinj : Set.InjOn Prod.fst (↑Z : Set (K × K)) := by
    intro x hx y hy hxy
    apply Prod.ext hxy
    have hxr := (phase_root_iff p q A B hcert x.1 x.2).mp (hZ x hx)
    have hyr := (phase_root_iff p q A B hcert y.1 y.2).mp (hZ y hy)
    rw [hxr.2, hyr.2, hxy]
  have hsub : (Z.image Prod.fst).val ⊆ (phaseSextic p q).roots := by
    intro t ht
    have ht' : t ∈ Z.image Prod.fst := ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht'
    apply (mem_roots hS).2
    exact common_phase_root_sextic p q z.1 z.2 (hZ z hz).1 (hZ z hz).2
  calc
    Z.card = (Z.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (phaseSextic p q).natDegree := card_le_degree_of_subset_roots hsub
    _ ≤ 6 := phase_sextic_degree_le p q

/-- The actual finite selected-root list, with the unique recovered second coordinate. -/
def phaseCandidates (p q : PhaseRow K) : Finset (K × K) := by
  classical
  exact (phaseSextic p q).roots.toFinset.image
    (fun t => (t, -(phaseLinearZero p q).eval t / (phaseLinearOne p q).eval t))

theorem mem_phaseCandidates_iff (p q : PhaseRow K) (A B : K[X])
    (hcert : BezoutCertificate (phaseSextic p q) (phaseLinearOne p q) A B)
    (hS : phaseSextic p q ≠ 0) (t u : K) :
    (t, u) ∈ phaseCandidates p q ↔ phaseValue p t u = 0 ∧ phaseValue q t u = 0 := by
  classical
  rw [phase_root_iff p q A B hcert t u]
  constructor
  · intro hm
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
    have hvt : v = t := congrArg Prod.fst heq
    subst v
    refine ⟨(mem_roots hS).mp (Multiset.mem_toFinset.mp hv), ?_⟩
    exact (congrArg Prod.snd heq).symm
  · rintro ⟨hr, rfl⟩
    exact Finset.mem_image.mpr ⟨t, Multiset.mem_toFinset.mpr ((mem_roots hS).mpr hr), rfl⟩

theorem phaseCandidates_card_le_six (p q : PhaseRow K) :
    (phaseCandidates p q).card ≤ 6 := by
  classical
  exact Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans
    ((card_roots' _).trans (phase_sextic_degree_le p q)))

end Ordered
end W3.Elimination
