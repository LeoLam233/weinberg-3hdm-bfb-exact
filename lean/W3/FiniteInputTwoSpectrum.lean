import W3.FiniteInputOperator
import W3.FiniteInputRealizationVectors
import W3.FiniteInputCandidatesMinimum
import W3.OperatorFieldTwoSpectrum

/-! The finite program keeps source points, explicit root-generated vectors,
reconstructed matrices and scalar codes. Its only charged guards are D ≠ 0
and purity ≤ 1. No selected semantic vector is used to construct this list. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal W3.OperatorField
open W3.TransferOperator W3.StrataTransfer W3.RealModel W3.PrimalFieldBridge
variable {n : Nat}

structure PhysicalCodeRecord (n : Nat) where
  charged : Bool
  point : SpectrumPoint (Code n)
  vector : Fin 6 → Code n
  matrix : Fin 9 → Code n
  scalar : Code n

def primalPhysicalRecord (k : Fin 15 → CoefficientCode n)
    (x : SpectrumPoint (Code n)) (z : Fin 6 → Code n) : PhysicalCodeRecord n :=
  ⟨false,x,z,projectorCode z,valueCode (liftWeighted (primalParameterCode k)) x⟩

def dualPhysicalRecord (k : Fin 15 → CoefficientCode n)
    (x : SpectrumPoint (Code n)) (z : Fin 6 → Code n) : PhysicalCodeRecord n :=
  ⟨true,x,z,dualCoordinatesCode k z,dualEnergyCode k z⟩

section Program
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

@[simp] theorem twoSpectrum_primalParameterCode_run (k : Fin 15 → CoefficientCode n) :
    runWeighted (K := K) input epsilon (primalParameterCode k) =
      originalPrimal (runParameters (K := K) input epsilon k) := by
  rw [runWeighted,primalParameterCode_eval,map_originalPrimal]
  rfl

@[simp] theorem twoSpectrum_dualParameterCode_run (k : Fin 15 → CoefficientCode n) :
    runWeighted (K := K) input epsilon (dualParameterCode k) =
      originalDual (runParameters (K := K) input epsilon k) := by
  rw [runWeighted,dualParameterCode_eval,originalDual_map]
  rfl

/-- Finite Cartesian product of the spectrum-point and square-root programs. -/
def primalPhysicalProgram (k : Fin 15 → CoefficientCode n) : List (PhysicalCodeRecord n) :=
  (spectrumProgram input epsilon O (primalParameterCode k)).flatMap fun x =>
    (amplitudeProgram input epsilon O x).map (primalPhysicalRecord k x)

def physicalChargedGuard (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) : Prop :=
  ((dualDenCode k z).run input epsilon O).value ≠ 0 ∧
    ((dualPurityCode k z).run input epsilon O).value ≤ 1

def dualPhysicalProgram (k : Fin 15 → CoefficientCode n) : List (PhysicalCodeRecord n) := by
  classical
  exact (spectrumProgram input epsilon O (dualParameterCode k)).flatMap fun x =>
    ((amplitudeProgram input epsilon O x).filter (physicalChargedGuard input epsilon O k)).map
      (dualPhysicalRecord k x)

def twoSpectrumProgram (k : Fin 15 → CoefficientCode n) : List (PhysicalCodeRecord n) :=
  primalPhysicalProgram input epsilon O k ++ dualPhysicalProgram input epsilon O k

@[simp] theorem primalPhysicalProgram_mem (k : Fin 15 → CoefficientCode n) (r : PhysicalCodeRecord n) :
    r ∈ primalPhysicalProgram input epsilon O k ↔
      ∃ x ∈ spectrumProgram input epsilon O (primalParameterCode k),
        ∃ z ∈ amplitudeProgram input epsilon O x, primalPhysicalRecord k x z = r := by
  simp only [primalPhysicalProgram,List.mem_flatMap,List.mem_map]

@[simp] theorem dualPhysicalProgram_mem (k : Fin 15 → CoefficientCode n) (r : PhysicalCodeRecord n) :
    r ∈ dualPhysicalProgram input epsilon O k ↔
      ∃ x ∈ spectrumProgram input epsilon O (dualParameterCode k),
        ∃ z ∈ amplitudeProgram input epsilon O x,
          physicalChargedGuard input epsilon O k z ∧ dualPhysicalRecord k x z = r := by
  classical
  simp only [dualPhysicalProgram,List.mem_flatMap,List.mem_map,List.mem_filter,decide_eq_true_eq]
  aesop

@[simp] theorem physicalChargedGuard_run (k : Fin 15 → CoefficientCode n) (z : Fin 6 → Code n) :
    physicalChargedGuard input epsilon O k z ↔
      dualDen (runParameters (K := K) input epsilon k) (runVector input epsilon O z) ≠ 0 ∧
      dualPurity (runParameters (K := K) input epsilon k) (runVector input epsilon O z) ≤ 1 := by
  simp only [physicalChargedGuard,dualDenCode_run,dualPurityCode_run]
  rfl

variable [IsRealClosed K]

theorem program_phase_ne_zero (w : WeightedData (CoefficientCode n))
    (h : completeWeightedExceptional (runWeighted (K := K) input epsilon w) ≠ 0) :
    phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0 :=
  (phaseExceptional_properties _ _ _ (mul_ne_zero_iff.mp h).1).1

theorem primalPhysicalProgram_values (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (v : K) :
    v ∈ (primalPhysicalProgram input epsilon O k).map (fun r => (r.scalar.run input epsilon O).value) ↔
      v ∈ primalValues (runParameters (K := K) input epsilon k) := by
  classical
  have he : completeWeightedExceptional (runWeighted (K := K) input epsilon (primalParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_primalParameterCode_run] using hp
  have hS := program_phase_ne_zero input epsilon (primalParameterCode k) he
  constructor
  · rintro hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv
    obtain ⟨x,hx,z,hz,rfl⟩ := (primalPhysicalProgram_mem input epsilon O k r).mp hr
    have hv := (commonValuesProgram_correct input epsilon O (primalParameterCode k) hS _).mp
      (List.mem_map.mpr ⟨valueCode (liftWeighted (primalParameterCode k)) x,
        List.mem_map.mpr ⟨x,hx,rfl⟩,rfl⟩)
    simpa only [twoSpectrum_primalParameterCode_run,primalPhysicalRecord,primalValues] using hv
  · intro hv
    have hv' : v ∈ spectrumValues (runWeighted (K := K) input epsilon (primalParameterCode k))
        (canonicalMagnitudes (runWeighted (K := K) input epsilon (primalParameterCode k))) := by simpa only [twoSpectrum_primalParameterCode_run,primalValues] using hv
    obtain ⟨c,hc,hcv⟩ := List.mem_map.mp
      ((commonValuesProgram_correct input epsilon O (primalParameterCode k) hS v).mpr hv')
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _
      (amplitudeProgram_candidate_nonempty input epsilon O (primalParameterCode k) he x hx)
    exact List.mem_map.mpr ⟨primalPhysicalRecord k x z,
      (primalPhysicalProgram_mem input epsilon O k _).mpr ⟨x,hx,z,hz,rfl⟩,hcv⟩

theorem dualPhysicalProgram_values (k : Fin 15 → CoefficientCode n)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (v : K) :
    v ∈ (dualPhysicalProgram input epsilon O k).map (fun r => (r.scalar.run input epsilon O).value) ↔
      v ∈ dualValues (runParameters (K := K) input epsilon k) hd := by
  classical
  let p := runParameters (K := K) input epsilon k
  have he : completeWeightedExceptional (runWeighted (K := K) input epsilon (dualParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_dualParameterCode_run] using hd
  have hS := program_phase_ne_zero input epsilon (dualParameterCode k) he
  constructor
  · intro hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv
    obtain ⟨x,hx,z,hz,hguard,rfl⟩ := (dualPhysicalProgram_mem input epsilon O k r).mp hr
    have hxc : runPoint input epsilon O x ∈ spectrumCandidates (originalDual p) (canonicalMagnitudes (originalDual p)) := by
      simpa only [twoSpectrum_dualParameterCode_run] using
        (spectrumProgram_correct input epsilon O (dualParameterCode k) hS _).mp
          (List.mem_map.mpr ⟨x,hx,rfl⟩)
    let j : CandidateIndex (originalDual p) := ⟨runPoint input epsilon O x,hxc⟩
    have hr : VectorRepresentation (originalDual p) (runPoint input epsilon O x) (runVector input epsilon O z) := by
      simpa only [twoSpectrum_dualParameterCode_run] using
        amplitudeProgram_representation input epsilon O (dualParameterCode k) he x hx z hz
    have ho := candidateVector_spec (originalDual p) hd j
    obtain ⟨_,_,hD,hchi,hE⟩ := matched_dual_scalars_invariant p _ _ _ hr.1 ho.1
    have hg := (physicalChargedGuard_run input epsilon O k z).mp hguard
    apply Finset.mem_image.mpr
    refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_attach _ j,?_,?_⟩,?_⟩
    · change dualDen p (candidateVector (originalDual p) hd j) ≠ 0
      rw [← hD]
      exact hg.1
    · change dualPurity p (candidateVector (originalDual p) hd j) ≤ 1
      rw [← hchi]
      exact hg.2
    · change dualEnergy p (candidateVector (originalDual p) hd j) =
        ((dualEnergyCode k z).run input epsilon O).value
      rw [dualEnergyCode_run]
      exact hE.symm
  · intro hv
    obtain ⟨j,hj,hjv⟩ := Finset.mem_image.mp hv
    have hjguard := (Finset.mem_filter.mp hj).2
    have hjc : j.val ∈ spectrumCandidates (runWeighted (K := K) input epsilon (dualParameterCode k))
        (canonicalMagnitudes (runWeighted (K := K) input epsilon (dualParameterCode k))) := by simpa only [twoSpectrum_dualParameterCode_run] using j.property
    obtain ⟨x,hx,hxj⟩ := List.mem_map.mp
      ((spectrumProgram_correct input epsilon O (dualParameterCode k) hS j.val).mpr hjc)
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil _
      (amplitudeProgram_candidate_nonempty input epsilon O (dualParameterCode k) he x hx)
    have hr : VectorRepresentation (originalDual p) j.val (runVector input epsilon O z) := by
      simpa only [twoSpectrum_dualParameterCode_run,hxj] using
        amplitudeProgram_representation input epsilon O (dualParameterCode k) he x hx z hz
    have ho := candidateVector_spec (originalDual p) hd j
    obtain ⟨_,_,hD,hchi,hE⟩ := matched_dual_scalars_invariant p _ _ _ hr.1 ho.1
    have hg : physicalChargedGuard input epsilon O k z := by
      apply (physicalChargedGuard_run input epsilon O k z).mpr
      change dualDen p (runVector input epsilon O z) ≠ 0 ∧ dualPurity p (runVector input epsilon O z) ≤ 1
      rw [hD,hchi]
      exact hjguard
    apply List.mem_map.mpr
    refine ⟨dualPhysicalRecord k x z,
      (dualPhysicalProgram_mem input epsilon O k _).mpr ⟨x,hx,z,hz,hg,rfl⟩,?_⟩
    change ((dualEnergyCode k z).run input epsilon O).value = v
    rw [dualEnergyCode_run]
    exact hE.trans hjv

/-- Equality is of the exact scalar set; extra square-root representatives may
repeat a scalar, but cannot create a thirty-first distinct value. -/
theorem twoSpectrumProgram_values (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (v : K) :
    v ∈ (twoSpectrumProgram input epsilon O k).map (fun r => (r.scalar.run input epsilon O).value) ↔
      v ∈ twoSpectrumValues (runParameters (K := K) input epsilon k) hd := by
  classical
  simp only [twoSpectrumProgram,List.map_append,List.mem_append,twoSpectrumValues,Finset.mem_union,
    primalPhysicalProgram_values input epsilon O k hp,dualPhysicalProgram_values input epsilon O k hd]

theorem twoSpectrumProgram_valueSet (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0) :
    ((twoSpectrumProgram input epsilon O k).map (fun r => (r.scalar.run input epsilon O).value)).toFinset =
      twoSpectrumValues (runParameters (K := K) input epsilon k) hd := by
  classical
  ext v
  exact List.mem_toFinset.trans (twoSpectrumProgram_values input epsilon O k hp hd v)

theorem twoSpectrumProgram_card (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0) :
    ((twoSpectrumProgram input epsilon O k).map (fun r => (r.scalar.run input epsilon O).value)).toFinset.card ≤ 30 := by
  classical
  rw [twoSpectrumProgram_valueSet input epsilon O k hp hd]
  exact twoSpectrumValues_card_le_thirty _ _

def twoSpectrumMinimumProgram (k : Fin 15 → CoefficientCode n) : Option (PhysicalCodeRecord n) :=
  codeArgmin input epsilon O PhysicalCodeRecord.scalar (twoSpectrumProgram input epsilon O k)

theorem twoSpectrumMinimumProgram_exists (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0) :
    ∃ r, twoSpectrumMinimumProgram input epsilon O k = some r := by
  obtain ⟨v,hv⟩ := twoSpectrumValues_nonempty (runParameters (K := K) input epsilon k) hd
  obtain ⟨r,hr,_⟩ := List.mem_map.mp ((twoSpectrumProgram_values input epsilon O k hp hd v).mpr hv)
  exact codeArgmin_exists input epsilon O PhysicalCodeRecord.scalar _ (List.ne_nil_of_mem hr)

theorem twoSpectrumMinimumProgram_minimum (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : twoSpectrumMinimumProgram input epsilon O k = some r) :
    (r.scalar.run input epsilon O).value =
      (twoSpectrumValues (runParameters (K := K) input epsilon k) hd).min'
        (twoSpectrumValues_nonempty _ hd) := by
  apply codeArgmin_minimum input epsilon O PhysicalCodeRecord.scalar _ r hr
  exact twoSpectrumProgram_values input epsilon O k hp hd

#print axioms twoSpectrumProgram_valueSet
#print axioms twoSpectrumMinimumProgram_minimum
end Program
end W3.FiniteInput
