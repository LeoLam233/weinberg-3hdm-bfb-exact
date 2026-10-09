import W3.PhysicalFields
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Sqrt

noncomputable section
open scoped BigOperators ComplexOrder Matrix
open ComplexConjugate
namespace W3

def twoFields (a b : ℝ) (u v : Fin 3 → ℂ) : Fields :=
  WithLp.toLp 2 (fun p => if p.1 = 0 then (Real.sqrt a : ℂ) * conj (u p.2)
    else (Real.sqrt b : ℂ) * conj (v p.2))

lemma gram_twoFields (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (u v : Fin 3 → ℂ) :
    gram (twoFields a b u v) = fun i j =>
      (a : ℂ) * u i * conj (u j) + (b : ℂ) * v i * conj (v j) := by
  have hsa : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt ha
  have hsb : (Real.sqrt b : ℂ)^2 = (b : ℂ) := by exact_mod_cast Real.sq_sqrt hb
  ext i j
  simp [gram, twoFields, Fin.sum_univ_two]
  calc
    _ = (Real.sqrt a : ℂ)^2 * u i * conj (u j) +
      (Real.sqrt b : ℂ)^2 * v i * conj (v j) := by ring
    _ = _ := by rw [hsa,hsb]

lemma spectral_entry (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.IsHermitian) (i j : Fin 3) :
    A i j = ∑ k, (hA.eigenvalues k : ℂ) * hA.eigenvectorUnitary i k *
      conj (hA.eigenvectorUnitary j k) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal, mul_comm, mul_left_comm]

/-- Every physical 3×3 Gram matrix of rank at most two is realized by the original doublets. -/
theorem exists_gram_factor (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : A.PosSemidef) (hdet : A.det = 0) : ∃ φ : Fields, gram φ = A := by
  let hH := hA.isHermitian
  have hp : ∏ i, hH.eigenvalues i = 0 := by
    have hc := hH.det_eq_prod_eigenvalues.symm.trans hdet
    simpa [Fin.prod_univ_three] using congrArg Complex.re hc
  obtain ⟨k,_,hk⟩ := Finset.prod_eq_zero_iff.mp hp
  have hnn := hA.eigenvalues_nonneg
  fin_cases k <;> dsimp only at hk
  · change hH.eigenvalues 0 = 0 at hk
    refine ⟨twoFields (hH.eigenvalues 1) (hH.eigenvalues 2)
      (fun j => hH.eigenvectorUnitary j 1) (fun j => hH.eigenvectorUnitary j 2), ?_⟩
    rw [gram_twoFields _ _ (hnn _) (hnn _)]
    ext i j
    rw [spectral_entry A hH i j]
    simp [Fin.sum_univ_three, hk]
  · change hH.eigenvalues 1 = 0 at hk
    refine ⟨twoFields (hH.eigenvalues 0) (hH.eigenvalues 2)
      (fun j => hH.eigenvectorUnitary j 0) (fun j => hH.eigenvectorUnitary j 2), ?_⟩
    rw [gram_twoFields _ _ (hnn _) (hnn _)]
    ext i j
    rw [spectral_entry A hH i j]
    simp [Fin.sum_univ_three, hk]
  · change hH.eigenvalues 2 = 0 at hk
    refine ⟨twoFields (hH.eigenvalues 0) (hH.eigenvalues 1)
      (fun j => hH.eigenvectorUnitary j 0) (fun j => hH.eigenvectorUnitary j 1), ?_⟩
    rw [gram_twoFields _ _ (hnn _) (hnn _)]
    ext i j
    rw [spectral_entry A hH i j]
    simp [Fin.sum_univ_three, hk]

theorem exists_normalized_gram_factor (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : A.PosSemidef) (hdet : A.det = 0) (htr : A.trace = 1) :
    ∃ φ : Fields, gram φ = A ∧ ‖φ‖ = 1 := by
  obtain ⟨φ,hφ⟩ := exists_gram_factor A hA hdet
  refine ⟨φ,hφ,?_⟩
  have ht := gram_trace φ
  rw [hφ,htr] at ht
  have hn : ‖φ‖^2 = 1 := by exact_mod_cast ht.symm
  nlinarith [norm_nonneg φ]

#print axioms exists_normalized_gram_factor
end W3
