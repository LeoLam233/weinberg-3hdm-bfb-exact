import W3.StrataTransferModel

noncomputable section
namespace W3.StrataTransfer
open W3.RealModel W3.Operator Matrix
open scoped BigOperators

/-- Complex notation is used only for the proved real-field source theorem. -/
def complexMatrix (ar ai : RealMatrix ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ⟨ar i j,ai i j⟩
def complexVector (z : RealVector ℝ) : Fin 3 → ℂ := fun i=>⟨zRe z i,zIm z i⟩
def vectorCoordinates (z : Fin 3 → ℂ) : RealVector ℝ :=
  ![(z 0).re,(z 0).im,(z 1).re,(z 1).im,(z 2).re,(z 2).im]

@[simp] theorem complex_vector_coordinates (z : Fin 3 → ℂ) :
    complexVector (vectorCoordinates z)=z := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem zRe_coordinates (z : Fin 3 → ℂ) (i : Fin 3) :
    zRe (vectorCoordinates z) i=(z i).re := by fin_cases i <;> rfl
@[simp] theorem zIm_coordinates (z : Fin 3 → ℂ) (i : Fin 3) :
    zIm (vectorCoordinates z) i=(z i).im := by fin_cases i <;> rfl

theorem complex_norm (z : RealVector ℝ) :
    (∑ i,Complex.normSq (complexVector z i))=zMass z := by
  simp [complexVector,zMass,Complex.normSq_apply,pow_two]

theorem complex_gram (x : RealFields ℝ) :
    complexMatrix (gramRe x) (gramIm x)=W3.gram (fields x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexMatrix,gramRe,gramIm,radii,offRe,offIm,fields,W3.gram,Fin.sum_univ_two] <;> ring

theorem complex_operator (k : Parameters ℝ) (x : RealFields ℝ) :
    complexMatrix (operatorRe k x) (operatorIm k x)=
      coordinateMatrix (couplingOperator (couplings k) (fieldCoordinates (fields x))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [complexMatrix,operatorRe,operatorIm,operatorDiag,operatorOffRe,operatorOffIm,
      radii,offRe,offIm,coordinateMatrix,couplingOperator,structuredLinear,couplingMatrix,
      block,fieldCoordinates,fields,couplings,W3.radius,W3.gram,Fin.sum_univ_three,
      Fin.sum_univ_two,Matrix.mulVec,dotProduct,Complex.normSq_apply] <;> ring

theorem complex_projector (z : RealVector ℝ) :
    complexMatrix (projectorRe z) (projectorIm z)=projector (complexVector z) := by
  ext i j <;> apply Complex.ext <;> simp [complexMatrix,projectorRe,projectorIm,projector,complexVector]
  <;> ring

theorem complex_action (ar ai : RealMatrix ℝ) (z : RealVector ℝ) (i : Fin 3) :
    (complexMatrix ar ai *ᵥ complexVector z) i =
      (⟨actionRe ar ai z i,actionIm ar ai z i⟩ : ℂ) := by
  apply Complex.ext <;>
    simp [complexMatrix,complexVector,actionRe,actionIm,Matrix.mulVec,dotProduct,
      Complex.mul_re,Complex.mul_im]

/-- The real analytic/spectral theorem yields precisely the explicitly encoded polynomial strata. -/
theorem real_minimum_strata (k : Parameters ℝ) (x : RealFields ℝ)
    (hm : mass x=1)
    (hmin : ∀ y : RealFields ℝ,mass y=1→twiceQuartic k x≤twiceQuartic k y) :
    StrataConclusion k x := by
  have hnorm : ‖fields x‖=1 := by
    rw [mass_fields] at hm
    nlinarith [norm_nonneg (fields x)]
  have hminimum : ∀ y : W3.Fields,‖y‖=1→W3.quartic (couplings k) (fields x)≤W3.quartic (couplings k) y := by
    intro y hy
    have h := hmin (coordinates y) (by simp [mass_coordinates,hy])
    rw [twiceQuartic_fields,twiceQuartic_coordinates] at h
    linarith
  rcases normalized_minimum_stationary_strata (couplings k) (fields x) hnorm hminimum with hN|hC
  · obtain ⟨z,hz,hgram,heigen⟩ := hN
    refine ⟨vectorCoordinates z,0,?_,Or.inl ⟨?_,?_⟩⟩
    · rw [← complex_norm,complex_vector_coordinates]
      exact hz
    · have h : complexMatrix (gramRe x) (gramIm x)=
          complexMatrix (projectorRe (vectorCoordinates z)) (projectorIm (vectorCoordinates z)) := by
        rw [complex_gram,complex_projector,complex_vector_coordinates]
        exact hgram
      intro i j
      exact ⟨congrArg (fun M=>(M i j).re) h,congrArg (fun M=>(M i j).im) h⟩
    · have h : complexMatrix (operatorRe k x) (operatorIm k x) *ᵥ complexVector (vectorCoordinates z)=
          (twiceQuartic k x) • complexVector (vectorCoordinates z) := by
        rw [complex_operator,complex_vector_coordinates,twiceQuartic_fields]
        exact heigen
      intro i
      have hi := congrFun h i
      rw [complex_action] at hi
      exact ⟨by simpa [complexVector,Complex.smul_re] using congrArg Complex.re hi,
        by simpa [complexVector,Complex.smul_im] using congrArg Complex.im hi⟩
  · obtain ⟨z,mu,hz,hkernel,hnormal⟩ := hC
    refine ⟨vectorCoordinates z,mu,?_,Or.inr ⟨?_,?_⟩⟩
    · rw [← complex_norm,complex_vector_coordinates]
      exact hz
    · have h : complexMatrix (gramRe x) (gramIm x) *ᵥ complexVector (vectorCoordinates z)=0 := by
        rw [complex_gram,complex_vector_coordinates]
        exact hkernel
      intro i
      have hi := congrFun h i
      rw [complex_action] at hi
      exact ⟨by simpa using congrArg Complex.re hi,by simpa using congrArg Complex.im hi⟩
    · have h : complexMatrix (operatorRe k x) (operatorIm k x)=
          (twiceQuartic k x) • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
            mu • complexMatrix (projectorRe (vectorCoordinates z)) (projectorIm (vectorCoordinates z)) := by
        rw [complex_operator,complex_projector,complex_vector_coordinates,twiceQuartic_fields]
        exact hnormal
      intro i j
      have hr := congrArg (fun M=>(M i j).re) h
      have hi := congrArg (fun M=>(M i j).im) h
      exact ⟨by simpa [complexMatrix,Matrix.one_apply,Complex.smul_re,apply_ite] using hr,
        by simpa [complexMatrix,Matrix.one_apply,Complex.smul_im,apply_ite] using hi⟩

end W3.StrataTransfer
