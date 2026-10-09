import W3.EliminationElementary
import W3.WeightedInverseBridge

noncomputable section
namespace W3.Elimination
open Matrix W3.Operator W3.Weighted

section MatrixField
variable {K : Type*} [Field K]

def originalMatrix (x : Fin 15 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![x 0, x 3, x 4; x 3, x 1, x 5; x 4, x 5, x 2]

def originalInverseMatrix (x : Fin 15 → K) : Matrix (Fin 3) (Fin 3) K :=
  let a := originalAdj x
  let d := originalMatrixDet x
  !![a 0/d, a 3/d, a 4/d; a 3/d, a 1/d, a 5/d; a 4/d, a 5/d, a 2/d]

theorem originalMatrix_det (x : Fin 15 → K) : (originalMatrix x).det = originalMatrixDet x := by
  simp [Matrix.det_fin_three, originalMatrix, originalMatrixDet]
  ring

theorem originalMatrix_inverse (x : Fin 15 → K) (h : originalMatrixDet x ≠ 0) :
    (originalMatrix x)⁻¹ = originalInverseMatrix x := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [originalMatrix, originalInverseMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      originalAdj] <;> field_simp [h] <;> simp only [originalMatrixDet] <;> ring

end MatrixField

/-- Exact embedding of canonical original15 into the unrestricted physical model. -/
def couplingsOfOriginal (x : Fin 15 → ℝ) : W3.Couplings :=
  ⟨![x 0,x 1,x 2], ![x 3,x 4,x 5], ![x 6,x 7,x 8],
    ![⟨x 9,x 10⟩, ⟨x 11,x 12⟩, ⟨x 13,x 14⟩]⟩

theorem couplingMatrix_original (x : Fin 15 → ℝ) :
    couplingMatrix (couplingsOfOriginal x) = originalMatrix x := rfl

theorem primalSpectrum_original (x : Fin 15 → ℝ) :
    toSpectrum (originalPrimal x) =
      structuredSpectrum (couplingMatrix (couplingsOfOriginal x))
        (couplingsOfOriginal x).c (couplingsOfOriginal x).d := by
  rfl

/-- The rational dual coordinates used in the generic proof equal the actual
inverse-operator spectrum, including all complex phases and the factor of two. -/
theorem dualSpectrum_original (x : Fin 15 → ℝ) (h : originalInverseDen x ≠ 0) :
    toSpectrum (originalDual x) =
      dualSpectrum (couplingMatrix (couplingsOfOriginal x))
        (couplingsOfOriginal x).c (couplingsOfOriginal x).d := by
  have hd := (originalInverseDen_nonzero_factors x h).1
  rw [couplingMatrix_original]
  unfold dualSpectrum
  rw [originalMatrix_inverse x hd]
  simp only [toSpectrum, originalDual, scaleSpectrum, structuredSpectrum, originalInverseMatrix,
    couplingsOfOriginal, inverseC, inverseD, ofComplex, ComplexPair.scale,
    Complex.smul_re, Complex.smul_im]
  simp [blockDet, Complex.normSq_apply, originalDelta12, originalDelta13, originalDelta23,
    div_eq_mul_inv, sub_sub]
  all_goals ring_nf <;> simp

theorem dualWeights_original (x : Fin 15 → ℝ) (h : originalInverseDen x ≠ 0) :
    dualWeights (couplingMatrix (couplingsOfOriginal x)) =
      ![(originalDual x).g1, (originalDual x).g2, (originalDual x).g3] := by
  have hd := (originalInverseDen_nonzero_factors x h).1
  rw [couplingMatrix_original]
  unfold dualWeights
  rw [originalMatrix_inverse x hd]
  ext i
  fin_cases i <;> simp [originalInverseMatrix, originalDual, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, div_eq_mul_inv] <;> ring

def originalOfCouplings (k : W3.Couplings) : Fin 15 → ℝ :=
  ![k.a 0,k.a 1,k.a 2,k.b 0,k.b 1,k.b 2,k.c 0,k.c 1,k.c 2,
    (k.d 0).re,(k.d 0).im,(k.d 1).re,(k.d 1).im,(k.d 2).re,(k.d 2).im]

theorem couplings_original_roundtrip (k : W3.Couplings) :
    couplingsOfOriginal (originalOfCouplings k) = k := by
  cases k with
  | mk a b c d =>
    dsimp [couplingsOfOriginal, originalOfCouplings]
    congr 1 <;> funext i <;> fin_cases i <;> simp

theorem original_operator_invertibility (x : Fin 15 → ℝ) (h : originalInverseDen x ≠ 0) :
    (couplingMatrix (couplingsOfOriginal x)).det ≠ 0 ∧
    ∀ i, blockDet ((couplingsOfOriginal x).c i) ((couplingsOfOriginal x).d i) ≠ 0 := by
  obtain ⟨hd,h12,h13,h23⟩ := originalInverseDen_nonzero_factors x h
  refine ⟨?_, ?_⟩
  · rwa [couplingMatrix_original, originalMatrix_det]
  · intro i
    fin_cases i
    · simpa [couplingsOfOriginal, blockDet, Complex.normSq_apply, originalDelta12, sub_sub, pow_two] using h12
    · simpa [couplingsOfOriginal, blockDet, Complex.normSq_apply, originalDelta13, sub_sub, pow_two] using h13
    · simpa [couplingsOfOriginal, blockDet, Complex.normSq_apply, originalDelta23, sub_sub, pow_two] using h23

end W3.Elimination
