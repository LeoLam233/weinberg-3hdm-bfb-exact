import W3.FiniteInputCandidatesPolynomials
import W3.WeightedRealization

/-! The finite code-bearing singleton/pair/sextic program. Guards use the exact
ordered-field predicates of the previously verified candidate list. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal

variable {n : Nat}
def magnitudeSquareCode (w : WeightedData (CoefficientCode n)) (i : Fin 3) : Code n :=
  let d := (pairInputCode (liftWeighted w) i).d
  Code.sq d.re + Code.sq d.im

section Program
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

/-- All three coordinate programs, with the original nonzero weight guard. -/
def singletonProgram (w : WeightedData (CoefficientCode n)) : List (SpectrumPoint (Code n)) := by
  classical
  exact ((List.finRange 3).filter fun i =>
    spectrumWeight (runWeighted (K := K) input epsilon w) (singletonPoint i) ≠ 0).map singletonCode

/-- Both phase signs are evaluated for each nonnegative coupling magnitude. -/
def pairProgram (w : WeightedData (CoefficientCode n)) : List (SpectrumPoint (Code n)) := by
  classical
  exact (List.finRange 3).flatMap fun i =>
    (squareRootFamily input epsilon O (magnitudeSquareCode w i)).flatMap fun rho =>
      (([false,true] : List Bool).filter fun s =>
        0 ≤ (rho.run input epsilon O).value ∧
        PairRetained (runWeighted (K := K) input epsilon w)
          (fun _ => (rho.run input epsilon O).value) i s).map
        (fun s => pairPointCode (liftWeighted w) rho i s)

/-- Every sextic root ordinal is retained until the exact physical filter. -/
def fullProgram (w : WeightedData (CoefficientCode n)) : List (SpectrumPoint (Code n)) := by
  classical
  exact ((rootFamily input epsilon O (sexticCodes w)).filter fun t =>
    FullRetained (runWeighted (K := K) input epsilon w) (t.run input epsilon O).value
      ((recoveredCode w t).run input epsilon O).value).map
      (fun t => fullPointCode (liftWeighted w) t (recoveredCode w t))

def spectrumProgram (w : WeightedData (CoefficientCode n)) : List (SpectrumPoint (Code n)) :=
  singletonProgram (K := K) input epsilon w ++ pairProgram input epsilon O w ++ fullProgram input epsilon O w

/-- The scalar program keeps its associated coordinate program as data. -/
def candidateProgram (w : WeightedData (CoefficientCode n)) :
    List (SpectrumPoint (Code n) × Code n) :=
  (spectrumProgram input epsilon O w).map (fun x => (x,valueCode (liftWeighted w) x))

@[simp] theorem run_magnitudeSquare (w : WeightedData (CoefficientCode n)) (i : Fin 3) :
    ((magnitudeSquareCode w i).run input epsilon O).value =
      ComplexPair.normSq (pairInput (runWeighted (K := K) input epsilon w) i).d := by
  fin_cases i <;> simp [magnitudeSquareCode,pairInputCode,pairInput,liftWeighted,
    runWeighted,evalWeighted,mapWeighted,ComplexPair.normSq]

theorem singletonProgram_correct (w : WeightedData (CoefficientCode n)) (x : SpectrumPoint K) :
    x ∈ (singletonProgram (K := K) input epsilon w).map (runPoint input epsilon O) ↔
      x ∈ singletonCandidates (runWeighted (K := K) input epsilon w) := by
  classical
  simp only [singletonProgram,List.map_map,List.mem_map,List.mem_filter,
    List.mem_finRange,decide_eq_true_eq,true_and,Function.comp_def,run_singleton,
    singletonCandidates,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]

theorem root_program_polynomial (w : WeightedData (CoefficientCode n)) :
    (coefficientPolynomial input epsilon (sexticCodes w)).map (algebraMap F K) =
      phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
        (weightedQ (runWeighted (K := K) input epsilon w)) := by
  simp [runWeighted]

theorem phaseRootProgram_correct (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0) (x : K × K) :
    (∃ t ∈ rootFamily input epsilon O (sexticCodes w),
      ((t.run input epsilon O).value, ((recoveredCode w t).run input epsilon O).value) = x) ↔
    x ∈ phaseCandidates (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) := by
  classical
  have hp : coefficientPolynomial input epsilon (sexticCodes w) ≠ 0 := by
    intro hz
    apply hS
    rw [← root_program_polynomial (K := K) input epsilon w,hz,Polynomial.map_zero]
  have hroots := rootFamily_correct input epsilon O (sexticCodes w) hp
  rw [root_program_polynomial] at hroots
  simp only [run_recovered]
  simp only [phaseCandidates,Finset.mem_image,Multiset.mem_toFinset]
  constructor
  · rintro ⟨c,hc,rfl⟩
    refine ⟨(c.run input epsilon O).value,?_,rfl⟩
    apply (Polynomial.mem_roots hS).mpr
    apply (O.correct _ hS _).mp
    rw [← hroots]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  · rintro ⟨t,ht,rfl⟩
    have ht' := (O.correct _ hS t).mpr ((Polynomial.mem_roots hS).mp ht)
    rw [← hroots] at ht'
    obtain ⟨c,hc,hcv⟩ := List.mem_map.mp ht'
    exact ⟨c,hc,by rw [hcv]⟩

theorem fullProgram_correct (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0) (x : SpectrumPoint K) :
    x ∈ (fullProgram input epsilon O w).map (runPoint input epsilon O) ↔
      x ∈ fullCandidates (runWeighted (K := K) input epsilon w) := by
  classical
  simp only [fullProgram,List.map_map,List.mem_map,List.mem_filter,Function.comp_def,run_fullPoint,
    fullCandidates,Finset.mem_image,Finset.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨c,⟨hc,hret⟩,hx⟩
    exact ⟨((c.run input epsilon O).value,((recoveredCode w c).run input epsilon O).value),
      ⟨(phaseRootProgram_correct input epsilon O w hS _).mp ⟨c,hc,rfl⟩,hret⟩,hx⟩
  · rintro ⟨⟨t,u⟩,⟨hmem,hret⟩,hx⟩
    obtain ⟨c,hc,heq⟩ := (phaseRootProgram_correct input epsilon O w hS (t,u)).mpr hmem
    have ht := congrArg Prod.fst heq
    have hu := congrArg Prod.snd heq
    dsimp only at ht hu
    exact ⟨c,⟨hc,by simpa only [ht,hu] using hret⟩,by simpa only [ht,hu] using hx⟩

/-- Every value of every quadratic-root ordinal, with no selected-root input. -/
theorem squareRootProgram_mem (a : Code n) (x : K) :
    (∃ c ∈ squareRootFamily input epsilon O a, (c.run input epsilon O).value = x) ↔
      x^2 = (a.run input epsilon O).value := by
  have hp : (X^2-C (a.run input epsilon O).value : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C _ (by decide : (2 : Nat) ≠ 0)).ne_zero
  rw [← List.mem_map, squareRootFamily_correct, O.correct _ hp]
  simp [Polynomial.IsRoot,sub_eq_zero]

theorem pairPoint_magnitude_congr (w : WeightedData K) (rho rho' : Fin 3 → K)
    (i : Fin 3) (s : Bool) (h : rho i = rho' i) :
    pairPoint w rho i s = pairPoint w rho' i s := by
  simp only [pairPoint,h]

theorem pairRetained_magnitude_congr (w : WeightedData K) (rho rho' : Fin 3 → K)
    (i : Fin 3) (s : Bool) (h : rho i = rho' i) :
    PairRetained w rho i s ↔ PairRetained w rho' i s := by
  simp only [PairRetained,h,pairPoint_magnitude_congr w rho rho' i s h]

variable [IsRealClosed K]
theorem pairProgram_correct (w : WeightedData (CoefficientCode n)) (x : SpectrumPoint K) :
    x ∈ (pairProgram input epsilon O w).map (runPoint input epsilon O) ↔
      x ∈ pairCandidates (runWeighted (K := K) input epsilon w)
        (canonicalMagnitudes (runWeighted (K := K) input epsilon w)) := by
  classical
  let v := runWeighted (K := K) input epsilon w
  simp only [pairProgram,List.mem_map,List.mem_flatMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨c,⟨i,rho,hrho,s,hs,hc⟩,hx⟩
    subst c
    have hs' : 0 ≤ (rho.run input epsilon O).value ∧
        PairRetained v (fun _ => (rho.run input epsilon O).value) i s := by
      exact of_decide_eq_true (List.mem_filter.mp hs).2
    have hsq := (squareRootProgram_mem input epsilon O (magnitudeSquareCode w i)
      (rho.run input epsilon O).value).mp ⟨rho,hrho,rfl⟩
    rw [run_magnitudeSquare] at hsq
    have heq : (rho.run input epsilon O).value = canonicalMagnitudes v i :=
      (sq_eq_sq₀ hs'.1 (canonicalMagnitudes_spec v i).1).mp
        (hsq.trans (canonicalMagnitudes_spec v i).2.symm)
    apply Finset.mem_image.mpr
    refine ⟨(i,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · exact (pairRetained_magnitude_congr v _ _ i s heq).mp hs'.2
    · rw [run_pairPoint] at hx
      exact (pairPoint_magnitude_congr v _ _ i s heq).symm.trans hx
  · intro hx
    obtain ⟨⟨i,s⟩,hs,hx⟩ := Finset.mem_image.mp hx
    have hret := (Finset.mem_filter.mp hs).2
    have hsq : (canonicalMagnitudes v i)^2 =
        ((magnitudeSquareCode w i).run input epsilon O).value := by
      rw [run_magnitudeSquare]
      exact (canonicalMagnitudes_spec v i).2
    obtain ⟨rho,hrho,heq⟩ := (squareRootProgram_mem input epsilon O
      (magnitudeSquareCode w i) (canonicalMagnitudes v i)).mpr hsq
    refine ⟨pairPointCode (liftWeighted w) rho i s,?_,?_⟩
    · refine ⟨i,rho,hrho,s,?_,rfl⟩
      apply List.mem_filter.mpr
      refine ⟨?_,decide_eq_true ?_⟩
      · cases s <;> simp
      · exact ⟨heq.symm ▸ (canonicalMagnitudes_spec v i).1,
          (pairRetained_magnitude_congr v _ _ i s heq).mpr hret⟩
    · rw [run_pairPoint]
      exact (pairPoint_magnitude_congr v _ _ i s heq).trans hx

/-- Point-for-point refinement, hence all scalar values and the 3+6+6 bound. -/
theorem spectrumProgram_correct (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0) (x : SpectrumPoint K) :
    x ∈ (spectrumProgram input epsilon O w).map (runPoint input epsilon O) ↔
      x ∈ spectrumCandidates (runWeighted (K := K) input epsilon w)
        (canonicalMagnitudes (runWeighted (K := K) input epsilon w)) := by
  classical
  simp only [spectrumProgram,List.map_append,List.mem_append,spectrumCandidates,Finset.mem_union,
    singletonProgram_correct,pairProgram_correct,fullProgram_correct input epsilon O w hS]

end Program
end W3.FiniteInput
