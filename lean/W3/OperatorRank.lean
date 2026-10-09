import W3.OperatorConcrete
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases

/-! Exact one-dimensional-kernel normal forms. -/
noncomputable section
namespace W3.Operator
open ComplexConjugate Matrix
open scoped BigOperators

/-- Rank two means exactly one complex kernel dimension, with no minor chart assumption. -/
theorem rank_two_kernel_generator (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : K.rank = 2) :
    ∃ z : Fin 3 → ℂ, z ≠ 0 ∧ K *ᵥ z = 0 ∧
      ∀ v : Fin 3 → ℂ, K *ᵥ v = 0 → ∃ c : ℂ, c • z = v := by
  have hdim : Module.finrank ℂ (LinearMap.ker K.mulVecLin) = 1 := by
    have h := K.mulVecLin.finrank_range_add_finrank_ker
    change K.rank + Module.finrank ℂ (LinearMap.ker K.mulVecLin) =
      Module.finrank ℂ (Fin 3 → ℂ) at h
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hK] at h
    omega
  obtain ⟨z,hz,hspan⟩ := finrank_eq_one_iff'.mp hdim
  refine ⟨z.val, ?_, z.property, ?_⟩
  · intro h; exact hz (Subtype.ext h)
  · intro v hv
    obtain ⟨c,hc⟩ := hspan ⟨v,hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩

/-- Every Hermitian operator whose range lies in one complex line is a real
multiple of that line's rank-one Gram matrix. -/
theorem hermitian_range_line (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X.IsHermitian)
    (z : Fin 3 → ℂ) (hz : z ≠ 0)
    (hspan : ∀ v : Fin 3 → ℂ, ∃ c : ℂ, c • z = X *ᵥ v) :
    ∃ μ : ℝ, X = μ • projector z := by
  have hzk : ∃ k, z k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  obtain ⟨k,hk⟩ := hzk
  have hcol (i j : Fin 3) : X i j * z k = X k j * z i := by
    obtain ⟨c,hc⟩ := hspan (Pi.single j 1)
    have hi := congrFun hc i
    have hh := congrFun hc k
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply] at hi hh
    rw [← hi, ← hh]
    ring
  have hrow (j : Fin 3) : X k j * conj (z k) = X k k * conj (z j) := by
    have h := congrArg (fun a : ℂ => conj a) (hcol j k)
    have hj : conj (X j k) = X k j := hX.apply k j
    have hkk : conj (X k k) = X k k := hX.apply k k
    simpa only [map_mul, hj, hkk] using h
  have hn : Complex.normSq (z k) ≠ 0 := mt Complex.normSq_eq_zero.mp hk
  have hnC : (Complex.normSq (z k) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hd : ((X k k).re : ℂ) = X k k := Complex.conj_eq_iff_re.mp (hX.apply k k)
  refine ⟨(X k k).re / Complex.normSq (z k), ?_⟩
  ext i j
  change X i j = ((X k k).re / Complex.normSq (z k)) • (z i * conj (z j))
  rw [Complex.real_smul, Complex.ofReal_div, hd]
  apply (mul_right_cancel₀ hnC)
  calc
    X i j * (Complex.normSq (z k) : ℂ) = X k k * z i * conj (z j) := by
      rw [Complex.normSq_eq_conj_mul_self]
      calc
        X i j * (conj (z k) * z k) = (X i j * z k) * conj (z k) := by ring
        _ = (X k j * z i) * conj (z k) := by rw [hcol]
        _ = z i * (X k j * conj (z k)) := by ring
        _ = X k k * z i * conj (z j) := by rw [hrow]; ring
    _ = (X k k / (Complex.normSq (z k) : ℂ) * (z i * conj (z j))) *
        (Complex.normSq (z k) : ℂ) := by field_simp [hnC]

/-- The matrix form underlying Section 5.1, proved from rank and multiplication. -/
theorem rank_two_hermitian_normal (K X : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.rank = 2) (hX : X.IsHermitian) (hKX : K * X = 0) :
    ∃ (z : Fin 3 → ℂ) (μ : ℝ), z ≠ 0 ∧ K *ᵥ z = 0 ∧ X = μ • projector z := by
  obtain ⟨z,hz,hker,hspan⟩ := rank_two_kernel_generator K hK
  obtain ⟨μ,hμ⟩ := hermitian_range_line X hX z hz (by
    intro v
    apply hspan
    rw [Matrix.mulVec_mulVec, hKX, Matrix.zero_mulVec])
  exact ⟨z,μ,hz,hker,hμ⟩

lemma projector_real_smul (t : ℝ) (z : Fin 3 → ℂ) :
    projector (t • z) = t ^ 2 • projector z := by
  ext i j
  simp [projector, Complex.real_smul]
  ring

lemma sum_normSq_real_smul (t : ℝ) (z : Fin 3 → ℂ) :
    (∑ i, Complex.normSq ((t • z) i)) = t ^ 2 * ∑ i, Complex.normSq (z i) := by
  simp [Fin.sum_univ_three, Complex.normSq_apply, Complex.smul_re, Complex.smul_im]
  ring

lemma normalize_kernel_vector (z : Fin 3 → ℂ) (hz : z ≠ 0) :
    ∃ (u : Fin 3 → ℂ) (s : ℝ), 0 < s ∧ z = s • u ∧
      (∑ i, Complex.normSq (u i)) = 1 := by
  have hpos : 0 < ∑ i, Complex.normSq (z i) := by
    have hzk : ∃ k, z k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    obtain ⟨k,hk⟩ := hzk
    exact (Complex.normSq_pos.mpr hk).trans_le
      (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (z i)) (Finset.mem_univ k))
  let s := Real.sqrt (∑ i, Complex.normSq (z i))
  have hs : 0 < s := Real.sqrt_pos.mpr hpos
  refine ⟨s⁻¹ • z,s,hs,?_,?_⟩
  · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  · rw [sum_normSq_real_smul]
    have hsquare : s ^ 2 = ∑ i, Complex.normSq (z i) := Real.sq_sqrt hpos.le
    rw [← hsquare, ← mul_pow, inv_mul_cancel₀ hs.ne']
    norm_num

/-- Unit-vector version of the rank-two normal form, matching the source projector. -/
theorem rank_two_hermitian_normal_unit (K X : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.rank = 2) (hX : X.IsHermitian) (hKX : K * X = 0) :
    ∃ (z : Fin 3 → ℂ) (μ : ℝ),
      (∑ i, Complex.normSq (z i)) = 1 ∧ K *ᵥ z = 0 ∧ X = μ • projector z := by
  obtain ⟨z,μ,hz,hker,hμ⟩ := rank_two_hermitian_normal K X hK hX hKX
  obtain ⟨u,s,hs,hzscale,hu⟩ := normalize_kernel_vector z hz
  refine ⟨u,μ * s ^ 2,hu,?_,?_⟩
  · rw [hzscale, Matrix.mulVec_smul] at hker
    exact (smul_eq_zero.mp hker).resolve_left hs.ne'
  · rw [hμ, hzscale, projector_real_smul, smul_smul]

lemma projector_trace (z : Fin 3 → ℂ) :
    (projector z).trace = ((∑ i, Complex.normSq (z i) : ℝ) : ℂ) := by
  simp [projector, Matrix.trace, Complex.mul_conj, ← Complex.ofReal_sum]

lemma projector_mulVec_self (z : Fin 3 → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    projector z *ᵥ z = z := by
  have hsum : (∑ i, conj (z i) * z i) = (1 : ℂ) := by
    simp only [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, hz, Complex.ofReal_one]
  ext i
  change (∑ j, (z i * conj (z j)) * z j) = z i
  calc
    (∑ j, z i * conj (z j) * z j) = z i * ∑ j, conj (z j) * z j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = z i := by rw [hsum, mul_one]

/-- Every Hermitian rank-one trace-one matrix is exactly a normalized projector.
No PSD assumption or phase restriction is required. -/
theorem rank_one_hermitian_trace_one (K : Matrix (Fin 3) (Fin 3) ℂ)
    (hK : K.IsHermitian) (hrank : K.rank = 1) (htr : K.trace = 1) :
    ∃ z : Fin 3 → ℂ, (∑ i, Complex.normSq (z i)) = 1 ∧ K = projector z := by
  change Module.finrank ℂ (LinearMap.range K.mulVecLin) = 1 at hrank
  obtain ⟨z,hz,hspan⟩ := finrank_eq_one_iff'.mp hrank
  have hz0 : z.val ≠ 0 := by intro h; exact hz (Subtype.ext h)
  obtain ⟨μ,hμ⟩ := hermitian_range_line K hK z.val hz0 (by
    intro v
    obtain ⟨c,hc⟩ := hspan ⟨K *ᵥ v, v, rfl⟩
    exact ⟨c, congrArg Subtype.val hc⟩)
  obtain ⟨u,s,hs,hzu,hu⟩ := normalize_kernel_vector z.val hz0
  have hrep : K = (μ * s ^ 2) • projector u := by
    rw [hμ, hzu, projector_real_smul, smul_smul]
  have hscale : μ * s ^ 2 = 1 := by
    rw [hrep, Matrix.trace_smul, projector_trace, hu] at htr
    have h := congrArg Complex.re htr
    simpa [Complex.smul_re, ← Complex.ofReal_pow] using h
  refine ⟨u,hu,?_⟩
  simpa [hscale] using hrep

/-- Hermitian annihilation by a normalized projector is a true vector kernel equation. -/
lemma projector_annihilation (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X.IsHermitian)
    (z : Fin 3 → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1)
    (hPX : projector z * X = 0) : X *ᵥ z = 0 := by
  have hP : (projector z).IsHermitian := by
    rw [← coordinateMatrix_projector]
    exact coordinateMatrix_hermitian _
  have hXP : X * projector z = 0 := by
    have h := congrArg Matrix.conjTranspose hPX
    simpa only [Matrix.conjTranspose_mul, hX.eq, hP.eq, Matrix.conjTranspose_zero] using h
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M *ᵥ z) hXP
  simpa only [← Matrix.mulVec_mulVec, projector_mulVec_self z hz, Matrix.zero_mulVec] using h

#print axioms rank_two_hermitian_normal
#print axioms rank_two_hermitian_normal_unit
#print axioms rank_one_hermitian_trace_one
end W3.Operator
