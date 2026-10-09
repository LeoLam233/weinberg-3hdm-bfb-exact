import W3.FiniteInputOperator
import W3.FiniteInputRealizationProjectors
import W3.TransferOperatorRetainedResidue

/-! Uniform syntax provenance for every original retained matrix, including
all compatible sign and gauge choices. This is a finite covering family, not
an assertion that its extraneous independent-sign entries are physical. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace W3.FiniteInput
open W3.Elimination W3.Weighted W3.OperatorField W3.TransferOperator
open W3.StrataTransfer W3.RealModel W3.Infinitesimal W3.PrimalFieldBridge
variable {n : Nat}

/-- The inverse reconstruction depends only on the nine projector coordinates.
Its syntax uses no supplied ambient vector, scalar or chosen algebraic witness. -/
def projectorDualACode (k : Fin 15 → CoefficientCode n) (p : Fin 9 → Code n) : Code n :=
  pairCode p (inverseCode k identityCode)
def projectorDualPCode (k : Fin 15 → CoefficientCode n) (p : Fin 9 → Code n) : Code n :=
  pairCode p (inverseCode k p)
def projectorDualDenCode (k : Fin 15 → CoefficientCode n) (p : Fin 9 → Code n) : Code n :=
  dualBetaCode k*projectorDualPCode k p-Code.sq (projectorDualACode k p)
def projectorDualCoordinatesCode (k : Fin 15 → CoefficientCode n) (p : Fin 9 → Code n) : Fin 9 → Code n :=
  fun i => (projectorDualPCode k p/projectorDualDenCode k p)*inverseCode k identityCode i-
    (projectorDualACode k p/projectorDualDenCode k p)*inverseCode k p i

section Evaluate
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

@[simp] theorem runCoordinates9_eq_runCodes (p : Fin 9 → Code n) :
    runCoordinates9 input epsilon O p = runCodes input epsilon O p := rfl

@[simp] theorem primalParameterCode_run (k : Fin 15 → CoefficientCode n) :
    runWeighted (K := K) input epsilon (primalParameterCode k) =
      originalPrimal (runParameters (K := K) input epsilon k) := by
  rw [runWeighted,primalParameterCode_eval,map_originalPrimal]
  rfl

@[simp] theorem dualParameterCode_run (k : Fin 15 → CoefficientCode n) :
    runWeighted (K := K) input epsilon (dualParameterCode k) =
      originalDual (runParameters (K := K) input epsilon k) := by
  rw [runWeighted,dualParameterCode_eval,originalDual_map]
  rfl

/-- Literal reconstruction equality; valid also when p or its denominator is
zero, because both sides use the same total field operations. -/
theorem projectorDualCoordinatesCode_run (k : Fin 15 → CoefficientCode n)
    (p : Fin 9 → Code n) (z : RealVector K)
    (hp : runCodes input epsilon O p = hermitianProjector z) :
    runCodes input epsilon O (projectorDualCoordinatesCode k p) =
      dualCoordinates (runParameters (K := K) input epsilon k) z := by
  have ha : (projectorDualACode k p |>.run input epsilon O).value =
      dualA (runParameters (K := K) input epsilon k) z := by
    simp [projectorDualACode,hp,dualA]
  have hq : (projectorDualPCode k p |>.run input epsilon O).value =
      dualP (runParameters (K := K) input epsilon k) z := by
    simp [projectorDualPCode,hp,dualP]
  have hd : (projectorDualDenCode k p |>.run input epsilon O).value =
      dualDen (runParameters (K := K) input epsilon k) z := by
    simp [projectorDualDenCode,ha,hq,dualDen,denominator]
  funext i
  change ((projectorDualCoordinatesCode k p i).run input epsilon O).value = _
  simp only [projectorDualCoordinatesCode,run_sub,run_mul_code,run_div,hq,hd,ha,
    inverseCode_run_apply,identityCode_run,hp]
  rfl

/-- One finite input-generated list covers both kinds of original matrix.
Each leaf remains rational, an original input coordinate, or an epsilon. -/
def retainedProvenanceProgram (k : Fin 15 → CoefficientCode n) : List (Fin 9 → Code n) :=
  spectrumProjectorProgram input epsilon O (primalParameterCode k) ++
    (spectrumProjectorProgram input epsilon O (dualParameterCode k)).map
      (projectorDualCoordinatesCode k)

variable [IsRealClosed K]

/-- All representatives are quantified, rather than only a runtime gauge. -/
theorem retainedProvenanceProgram_covers_primal (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (x : SpectrumPoint K)
    (hx : x ∈ spectrumCandidates (originalPrimal (runParameters (K := K) input epsilon k))
      (canonicalMagnitudes (originalPrimal (runParameters (K := K) input epsilon k))))
    (z : RealVector K) (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∃ p ∈ retainedProvenanceProgram input epsilon O k,
      runCodes input epsilon O p = hermitianProjector z := by
  have hp' : completeWeightedExceptional
      (runWeighted (K := K) input epsilon (primalParameterCode k)) ≠ 0 := by simpa using hp
  have hx' : x ∈ spectrumCandidates (runWeighted (K := K) input epsilon (primalParameterCode k))
      (canonicalMagnitudes (runWeighted (K := K) input epsilon (primalParameterCode k))) := by simpa using hx
  obtain ⟨p,hp,hv⟩ := spectrumProjectorProgram_covers input epsilon O (primalParameterCode k) hp' x hx' z hm
  exact ⟨p,List.mem_append_left _ hp,hv⟩

theorem retainedProvenanceProgram_covers_dual (k : Fin 15 → CoefficientCode n)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (x : SpectrumPoint K)
    (hx : x ∈ spectrumCandidates (originalDual (runParameters (K := K) input epsilon k))
      (canonicalMagnitudes (originalDual (runParameters (K := K) input epsilon k))))
    (z : RealVector K) (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∃ p ∈ retainedProvenanceProgram input epsilon O k,
      runCodes input epsilon O p = dualCoordinates (runParameters (K := K) input epsilon k) z := by
  have hd' : completeWeightedExceptional
      (runWeighted (K := K) input epsilon (dualParameterCode k)) ≠ 0 := by simpa using hd
  have hx' : x ∈ spectrumCandidates (runWeighted (K := K) input epsilon (dualParameterCode k))
      (canonicalMagnitudes (runWeighted (K := K) input epsilon (dualParameterCode k))) := by simpa using hx
  obtain ⟨p,hp,hv⟩ := spectrumProjectorProgram_covers input epsilon O (dualParameterCode k) hd' x hx' z hm
  exact ⟨projectorDualCoordinatesCode k p,
    List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩),
    projectorDualCoordinatesCode_run input epsilon O k p z hv⟩
end Evaluate

variable [DecidableEq (RationalTower 16)]

/-- Specialization to the exact fifteen original coefficients and sixteen
ordered infinitesimals used by the original retained-set theorem. -/
def actualRetainedProvenanceProgram (κ : Fin 15 → ℝ) (O : RealRootEnumeration SixteenLevelField) :
    List (Fin 9 → Code 16) :=
  letI := rationalTowerAlgebra 16
  retainedProvenanceProgram (originalInput κ) (rationalCoordinates 16) O actualParameterCode

@[simp] theorem actualParameterCode_runParameters (κ : Fin 15 → ℝ) :
    letI := rationalTowerAlgebra 16
    runParameters (K := SixteenLevelField) (originalInput κ) (rationalCoordinates 16) actualParameterCode =
      actualParameters κ := by
  letI := rationalTowerAlgebra 16
  funext i
  change rationalTowerHom 16 ((actualParameterCode i).eval (originalInput κ) (rationalCoordinates 16)) = _
  rw [actualParameterCode_eval,rationalActualParameters_map]

/-- Every member of the original retained matrix set is the evaluation of one
member of a single finite input-code list. No candidate or gauge is replaced. -/
theorem actualRetainedProvenanceProgram_covers (κ : Fin 15 → ℝ)
    (O : RealRootEnumeration SixteenLevelField) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) :
    letI := rationalTowerAlgebra 16
    ∃ p ∈ actualRetainedProvenanceProgram κ O,
      runCodes (originalInput κ) (rationalCoordinates 16) O p = y := by
  letI := rationalTowerAlgebra 16
  classical
  rcases Finset.mem_union.mp hy with hp | hd
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
    have hg : completeWeightedExceptional
        (originalPrimal (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode)) ≠ 0 := by
      simpa using (actualParameters_generic κ).1
    have hq : q.val ∈ spectrumCandidates
        (originalPrimal (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode))
        (canonicalMagnitudes (originalPrimal (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode))) := by simpa using q.property
    exact retainedProvenanceProgram_covers_primal (originalInput κ) (rationalCoordinates 16) O
      actualParameterCode hg q.val hq _ (candidateVector_spec _ _ q).1
  · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hd
    have hg : completeWeightedExceptional
        (originalDual (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode)) ≠ 0 := by
      simpa using (actualParameters_generic κ).2.2
    have hq : q.val ∈ spectrumCandidates
        (originalDual (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode))
        (canonicalMagnitudes (originalDual (runParameters (K := SixteenLevelField) (originalInput κ)
          (rationalCoordinates 16) actualParameterCode))) := by simpa using q.property
    simpa only [actualRetainedProvenanceProgram,actualParameterCode_runParameters] using
      retainedProvenanceProgram_covers_dual (originalInput κ) (rationalCoordinates 16) O
        actualParameterCode hg q.val hq _ (candidateVector_spec _ _ q).1

/-- In particular all nine coordinates have explicit code provenance, with
one common matrix-code witness from the same list. -/
theorem actualRetainedMatrix_coordinate_codes (κ : Fin 15 → ℝ)
    (O : RealRootEnumeration SixteenLevelField) (y : Matrix16)
    (hy : y ∈ actualRetainedMatrices κ) :
    letI := rationalTowerAlgebra 16
    ∃ p ∈ actualRetainedProvenanceProgram κ O,
      ∀ i, (p i |>.run (originalInput κ) (rationalCoordinates 16) O).value = y i := by
  letI := rationalTowerAlgebra 16
  obtain ⟨p,hp,hv⟩ := actualRetainedProvenanceProgram_covers κ O y hy
  exact ⟨p,hp,fun i => congrFun hv i⟩

#print axioms projectorDualCoordinatesCode_run
#print axioms retainedProvenanceProgram_covers_primal
#print axioms retainedProvenanceProgram_covers_dual
#print axioms actualRetainedProvenanceProgram_covers
#print axioms actualRetainedMatrix_coordinate_codes
end W3.FiniteInput
