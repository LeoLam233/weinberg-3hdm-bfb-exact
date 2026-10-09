import W3.FiniteInputTwoSpectrum

/-! Every literal output matrix is physical and its stored scalar is exactly
one half of its Hermitian energy. The charged proof includes its kernel. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal W3.OperatorField
open W3.TransferOperator W3.StrataTransfer W3.RealModel W3.PrimalFieldBridge
variable {n : Nat}
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

theorem primalPhysicalProgram_energy (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ primalPhysicalProgram input epsilon O k) :
    (r.scalar.run input epsilon O).value =
      hermitianEnergy (runParameters (K := K) input epsilon k) (runCodes input epsilon O r.matrix)/2 := by
  obtain ⟨x,hx,z,hz,rfl⟩ := (primalPhysicalProgram_mem input epsilon O k r).mp hr
  have he : completeWeightedExceptional (runWeighted (K := K) input epsilon (primalParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_primalParameterCode_run] using hp
  have hs : VectorRepresentation (originalPrimal (runParameters (K := K) input epsilon k))
      (runPoint input epsilon O x) (runVector input epsilon O z) := by
    simpa only [twoSpectrum_primalParameterCode_run] using
      amplitudeProgram_representation input epsilon O (primalParameterCode k) he x hx z hz
  change ((valueCode (liftWeighted (primalParameterCode k)) x).run input epsilon O).value =
    hermitianEnergy _ (runCodes input epsilon O (projectorCode z))/2
  rw [run_value,twoSpectrum_primalParameterCode_run,projectorCode_run]
  rw [pointMatches_primal_value _ _ _ hs.1 hs.2.1]
  rw [projector_eq_neutral_gram,hermitianEnergy_gramCoordinates]
  rfl

theorem dualPhysicalProgram_kernel (k : Fin 15 → CoefficientCode n)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ dualPhysicalProgram input epsilon O k) :
    NormalizedKernel (runCodes input epsilon O r.matrix) (runVector input epsilon O r.vector) ∧
      hermitianPurity (runCodes input epsilon O r.matrix) ≤ 1 ∧
      dualDen (runParameters (K := K) input epsilon k) (runVector input epsilon O r.vector) ≠ 0 := by
  obtain ⟨x,hx,z,hz,hguard,rfl⟩ := (dualPhysicalProgram_mem input epsilon O k r).mp hr
  have he : completeWeightedExceptional (runWeighted (K := K) input epsilon (dualParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_dualParameterCode_run] using hd
  have hs : VectorRepresentation (originalDual (runParameters (K := K) input epsilon k))
      (runPoint input epsilon O x) (runVector input epsilon O z) := by
    simpa only [twoSpectrum_dualParameterCode_run] using
      amplitudeProgram_representation input epsilon O (dualParameterCode k) he x hx z hz
  obtain ⟨lam,ham⟩ := hs.2.2.2
  obtain ⟨hD,hchi⟩ := (physicalChargedGuard_run input epsilon O k z).mp hguard
  have hker := (dual_kernel_iff _ _ hD).mpr (dual_amplitudes_kernel _ _ lam ham)
  change NormalizedKernel (runCodes input epsilon O (dualCoordinatesCode k z)) (runVector input epsilon O z) ∧
    hermitianPurity (runCodes input epsilon O (dualCoordinatesCode k z)) ≤ 1 ∧
    dualDen (runParameters (K := K) input epsilon k) (runVector input epsilon O z) ≠ 0
  rw [dualCoordinatesCode_run]
  exact ⟨⟨dual_trace _ _ hD,hs.2.1,(actionLinear_zero_iff _ _).mp hker⟩,hchi,hD⟩

theorem dualPhysicalProgram_energy (k : Fin 15 → CoefficientCode n)
    (hk : originalInverseDen (runParameters (K := K) input epsilon k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ dualPhysicalProgram input epsilon O k) :
    (r.scalar.run input epsilon O).value =
      hermitianEnergy (runParameters (K := K) input epsilon k) (runCodes input epsilon O r.matrix)/2 := by
  have hkernel := dualPhysicalProgram_kernel input epsilon O k hd r hr
  obtain ⟨x,hx,z,hz,hguard,rfl⟩ := (dualPhysicalProgram_mem input epsilon O k r).mp hr
  change ((dualEnergyCode k z).run input epsilon O).value =
      hermitianEnergy _ (runCodes input epsilon O (dualCoordinatesCode k z))/2
  rw [dualEnergyCode_run,dualCoordinatesCode_run]
  have hD := (physicalChargedGuard_run input epsilon O k z).mp hguard |>.1
  have hker : actionLinear (runVector input epsilon O z)
      (dualCoordinates (runParameters (K := K) input epsilon k) (runVector input epsilon O z)) = 0 := by
    apply (actionLinear_zero_iff _ _).mpr
    have hv : runCodes input epsilon O z = runVector input epsilon O z := rfl
    simpa only [dualPhysicalRecord,dualCoordinatesCode_run,hv] using hkernel.1.2.2
  exact (dual_energy _ hk _ hD hker).symm

theorem twoSpectrumProgram_energy (k : Fin 15 → CoefficientCode n)
    (hk : originalInverseDen (runParameters (K := K) input epsilon k) ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := K) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := K) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ twoSpectrumProgram input epsilon O k) :
    (r.scalar.run input epsilon O).value =
      hermitianEnergy (runParameters (K := K) input epsilon k) (runCodes input epsilon O r.matrix)/2 := by
  rcases List.mem_append.mp hr with hr | hr
  · exact primalPhysicalProgram_energy input epsilon O k hp r hr
  · exact dualPhysicalProgram_energy input epsilon O k hk hd r hr

theorem twoSpectrumProgram_provenance (k : Fin 15 → CoefficientCode n)
    (r : PhysicalCodeRecord n) (hr : r ∈ twoSpectrumProgram input epsilon O k) :
    (r.charged = false ∧ r.point ∈ spectrumProgram input epsilon O (primalParameterCode k) ∧
      r.vector ∈ amplitudeProgram input epsilon O r.point ∧ r.matrix = projectorCode r.vector ∧
      r.scalar = valueCode (liftWeighted (primalParameterCode k)) r.point) ∨
    (r.charged = true ∧ r.point ∈ spectrumProgram input epsilon O (dualParameterCode k) ∧
      r.vector ∈ amplitudeProgram input epsilon O r.point ∧ physicalChargedGuard input epsilon O k r.vector ∧
      r.matrix = dualCoordinatesCode k r.vector ∧ r.scalar = dualEnergyCode k r.vector) := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨x,hx,z,hz,rfl⟩ := (primalPhysicalProgram_mem input epsilon O k r).mp hr
    exact Or.inl ⟨rfl,hx,hz,rfl,rfl⟩
  · obtain ⟨x,hx,z,hz,hg,rfl⟩ := (dualPhysicalProgram_mem input epsilon O k r).mp hr
    exact Or.inr ⟨rfl,hx,hz,hg,rfl,rfl⟩

section Physical
variable [Algebra F SixteenLevelField]
variable (R : RealRootEnumeration SixteenLevelField)

theorem primalPhysicalProgram_physical (k : Fin 15 → CoefficientCode n)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := SixteenLevelField) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ primalPhysicalProgram input epsilon R k) :
    ∃ f : RealFields SixteenLevelField, mass f = 1 ∧
      gramCoordinates f = runCodes input epsilon R r.matrix ∧
      quarticReal (runParameters (K := SixteenLevelField) input epsilon k) f =
        (r.scalar.run input epsilon R).value := by
  obtain ⟨x,hx,z,hz,rfl⟩ := (primalPhysicalProgram_mem input epsilon R k r).mp hr
  have he : completeWeightedExceptional (runWeighted (K := SixteenLevelField) input epsilon (primalParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_primalParameterCode_run] using hp
  have hs : VectorRepresentation (originalPrimal (runParameters (K := SixteenLevelField) input epsilon k))
      (runPoint input epsilon R x) (runVector input epsilon R z) := by
    simpa only [twoSpectrum_primalParameterCode_run] using
      amplitudeProgram_representation input epsilon R (primalParameterCode k) he x hx z hz
  refine ⟨neutralFields (runVector input epsilon R z),(neutralFields_mass _).trans hs.2.1,?_,?_⟩
  · change gramCoordinates (neutralFields _) = runCodes input epsilon R (projectorCode z)
    rw [projectorCode_run,projector_eq_neutral_gram]
    rfl
  · change quarticReal _ _ = ((valueCode (liftWeighted (primalParameterCode k)) x).run input epsilon R).value
    rw [run_value,twoSpectrum_primalParameterCode_run]
    exact (pointMatches_primal_value _ _ _ hs.1 hs.2.1).symm

theorem dualPhysicalProgram_physical (k : Fin 15 → CoefficientCode n)
    (hk : originalInverseDen (runParameters (K := SixteenLevelField) input epsilon k) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := SixteenLevelField) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ dualPhysicalProgram input epsilon R k) :
    ∃ f : RealFields SixteenLevelField, mass f = 1 ∧
      gramCoordinates f = runCodes input epsilon R r.matrix ∧
      quarticReal (runParameters (K := SixteenLevelField) input epsilon k) f =
        (r.scalar.run input epsilon R).value := by
  obtain ⟨x,hx,z,hz,hguard,rfl⟩ := (dualPhysicalProgram_mem input epsilon R k r).mp hr
  have he : completeWeightedExceptional (runWeighted (K := SixteenLevelField) input epsilon (dualParameterCode k)) ≠ 0 := by
    simpa only [twoSpectrum_dualParameterCode_run] using hd
  have hs : VectorRepresentation (originalDual (runParameters (K := SixteenLevelField) input epsilon k))
      (runPoint input epsilon R x) (runVector input epsilon R z) := by
    simpa only [twoSpectrum_dualParameterCode_run] using
      amplitudeProgram_representation input epsilon R (dualParameterCode k) he x hx z hz
  obtain ⟨lam,ham⟩ := hs.2.2.2
  obtain ⟨hD,hchi⟩ := (physicalChargedGuard_run input epsilon R k z).mp hguard
  obtain ⟨f,hf,hG,hE⟩ := dual_candidate_physical _ hk _ lam hs.2.1 ham hD hchi
  refine ⟨f,hf,?_,?_⟩
  · change gramCoordinates f = runCodes input epsilon R (dualCoordinatesCode k z)
    rw [dualCoordinatesCode_run]
    exact hG
  · change quarticReal _ f = ((dualEnergyCode k z).run input epsilon R).value
    rw [dualEnergyCode_run]
    exact hE

theorem twoSpectrumProgram_physical (k : Fin 15 → CoefficientCode n)
    (hk : originalInverseDen (runParameters (K := SixteenLevelField) input epsilon k) ≠ 0)
    (hp : completeWeightedExceptional (originalPrimal (runParameters (K := SixteenLevelField) input epsilon k)) ≠ 0)
    (hd : completeWeightedExceptional (originalDual (runParameters (K := SixteenLevelField) input epsilon k)) ≠ 0)
    (r : PhysicalCodeRecord n) (hr : r ∈ twoSpectrumProgram input epsilon R k) :
    ∃ f : RealFields SixteenLevelField, mass f = 1 ∧
      gramCoordinates f = runCodes input epsilon R r.matrix ∧
      quarticReal (runParameters (K := SixteenLevelField) input epsilon k) f =
        (r.scalar.run input epsilon R).value := by
  rcases List.mem_append.mp hr with hr | hr
  · exact primalPhysicalProgram_physical input epsilon R k hp r hr
  · exact dualPhysicalProgram_physical input epsilon R k hk hd r hr

end Physical
#print axioms twoSpectrumProgram_energy
#print axioms twoSpectrumProgram_provenance
#print axioms twoSpectrumProgram_physical
end W3.FiniteInput
