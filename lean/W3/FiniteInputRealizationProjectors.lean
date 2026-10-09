import W3.FiniteInputRealizationVectors

/-! A finite coordinate family covering every projector compatible with a
retained point, including all discrete square-root choices. It is a provenance
family; the amplitude program supplies the physical runtime representatives. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal W3.OperatorField W3.RealModel
open W3.PrimalFieldBridge W3.TransferOperator W3.StrataTransfer ComplexPair
variable {n : Nat}

def projectorCoordinateCode (x : SpectrumPoint (Code n))
    (a b c : ComplexPair (Code n)) : Fin 9 → Code n :=
  ![x.r₁,x.r₂,x.r₃,a.re,a.im,b.re,b.im,c.re,c.im]

section Program
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

def runCoordinates9 (y : Fin 9 → Code n) : HermitianCoordinates K :=
  fun i => ((y i).run input epsilon O).value

/-- Each off-diagonal coordinate ranges over its exact finite complex-square
branches. All fields are code data; no ambient scalar is a syntax leaf. -/
def projectorProgram (x : SpectrumPoint (Code n)) : List (Fin 9 → Code n) :=
  (phaseRadiusProgram input epsilon O (x.r₁*x.r₂) (complexConj x.q)).flatMap fun a =>
    (phaseRadiusProgram input epsilon O (x.r₁*x.r₃) (complexConj x.v)).flatMap fun b =>
      (phaseRadiusProgram input epsilon O (x.r₂*x.r₃)
        (complexConj (complexMul x.v (complexConj x.q)))).map fun c =>
        projectorCoordinateCode x a b c

theorem phaseRadiusProgram_covers_entry (r s : Code n) (q : ComplexPair (Code n))
    (hr : 0 ≤ (r.run input epsilon O).value) (hs : 0 ≤ (s.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O q)=1) (a b : ComplexPair K)
    (ha : normSq a=(r.run input epsilon O).value)
    (hb : normSq b=(s.run input epsilon O).value)
    (he : squaredEntry a b = scale ((r.run input epsilon O).value*(s.run input epsilon O).value)
      (runComplex input epsilon O q)) :
    ∃ c ∈ phaseRadiusProgram input epsilon O (r*s) (complexConj q),
      runComplex input epsilon O c = mul a (conj b) := by
  have hprod : 0 ≤ ((r*s).run input epsilon O).value := by simpa using mul_nonneg hr hs
  have hconj : normSq (runComplex input epsilon O (complexConj q))=1 := by
    simpa only [run_complexConj,complexPair_norm_conj] using hq
  apply List.mem_map.mp
  apply (phaseRadiusProgram_correct input epsilon O (r*s) (complexConj q) hprod hconj _).mpr
  constructor
  · rw [complex_norm_mul,complexPair_norm_conj,ha,hb,run_mul]
  · change conj (squaredEntry a b)=_
    rw [he,run_mul,run_complexConj]
    apply complexPair_ext <;> simp [conj,scale]

/-- Every compatible physical projector is in the uniform coordinate family.
The quantified vector may have any common global phase and every sign choice. -/
theorem projectorProgram_covers (x : SpectrumPoint (Code n))
    (hr1 : 0 ≤ (x.r₁.run input epsilon O).value)
    (hr2 : 0 ≤ (x.r₂.run input epsilon O).value)
    (hr3 : 0 ≤ (x.r₃.run input epsilon O).value)
    (hq : normSq (runComplex input epsilon O x.q)=1)
    (hv : normSq (runComplex input epsilon O x.v)=1)
    (z : RealVector K)
    (hm : PointMatches (runPoint input epsilon O x) (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∃ y ∈ projectorProgram input epsilon O x,
      runCoordinates9 input epsilon O y = hermitianProjector z := by
  obtain ⟨h1,h2,h3,h12,h13,h23⟩ := hm
  obtain ⟨a,ha,hav⟩ := phaseRadiusProgram_covers_entry input epsilon O x.r₁ x.r₂ x.q
    hr1 hr2 hq (pairVector z 0) (pairVector z 1) h1.symm h2.symm h12
  obtain ⟨b,hb,hbv⟩ := phaseRadiusProgram_covers_entry input epsilon O x.r₁ x.r₃ x.v
    hr1 hr3 hv (pairVector z 0) (pairVector z 2) h1.symm h3.symm h13
  have hrel : normSq (runComplex input epsilon O (complexMul x.v (complexConj x.q)))=1 := by
    rw [run_complexMul,run_complexConj,complex_norm_mul,complexPair_norm_conj,hv,hq,mul_one]
  have h23' : squaredEntry (pairVector z 1) (pairVector z 2) =
      scale ((x.r₂.run input epsilon O).value*(x.r₃.run input epsilon O).value)
        (runComplex input epsilon O (complexMul x.v (complexConj x.q))) := by
    simpa only [run_complexMul,run_complexConj,runPoint] using h23
  obtain ⟨c,hc,hcv⟩ := phaseRadiusProgram_covers_entry input epsilon O x.r₂ x.r₃
    (complexMul x.v (complexConj x.q)) hr2 hr3 hrel (pairVector z 1) (pairVector z 2) h2.symm h3.symm h23'
  refine ⟨projectorCoordinateCode x a b c,?_,?_⟩
  · simp only [projectorProgram,List.mem_flatMap,List.mem_map]
    exact ⟨a,ha,b,hb,c,hc,rfl⟩
  · have haR := congrArg ComplexPair.re hav
    have haI := congrArg ComplexPair.im hav
    have hbR := congrArg ComplexPair.re hbv
    have hbI := congrArg ComplexPair.im hbv
    have hcR := congrArg ComplexPair.re hcv
    have hcI := congrArg ComplexPair.im hcv
    funext i
    fin_cases i <;>
      simp [runCoordinates9,projectorCoordinateCode,hermitianProjector,
        projectorRe,projectorIm,runComplex,pairVector,normSq,mul,conj,runPoint] at *
    all_goals first | assumption | linarith

variable [IsRealClosed K]
theorem projectorProgram_covers_candidate (w : WeightedData (CoefficientCode n))
    (hex : completeWeightedExceptional (runWeighted (K := K) input epsilon w) ≠ 0)
    (x : SpectrumPoint (Code n)) (hx : x ∈ spectrumProgram input epsilon O w)
    (z : RealVector K)
    (hm : PointMatches (runPoint input epsilon O x) (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∃ y ∈ projectorProgram input epsilon O x,
      runCoordinates9 input epsilon O y = hermitianProjector z := by
  let v := runWeighted (K := K) input epsilon w
  have he := (mul_ne_zero_iff.mp hex).1
  have hS := (phaseExceptional_properties (weightedP v) (weightedQ v) (weightedPole v) he).1
  have hxc := (spectrumProgram_correct input epsilon O w hS _).mp (List.mem_map.mpr ⟨x,hx,rfl⟩)
  obtain ⟨h1,h2,h3,hq,hv,_⟩ := spectrumCandidate_shape v hex _ hxc
  exact projectorProgram_covers input epsilon O x h1 h2 h3 hq hv z hm

/-- One input-generated provenance list for every matched projector over all
three support types. The runtime physical vector list remains amplitudeProgram. -/
def spectrumProjectorProgram (w : WeightedData (CoefficientCode n)) : List (Fin 9 → Code n) :=
  (spectrumProgram input epsilon O w).flatMap (projectorProgram input epsilon O)

theorem spectrumProjectorProgram_covers (w : WeightedData (CoefficientCode n))
    (hex : completeWeightedExceptional (runWeighted (K := K) input epsilon w) ≠ 0)
    (x : SpectrumPoint K)
    (hx : x ∈ spectrumCandidates (runWeighted (K := K) input epsilon w)
      (canonicalMagnitudes (runWeighted (K := K) input epsilon w)))
    (z : RealVector K) (hm : PointMatches x (pairVector z 0) (pairVector z 1) (pairVector z 2)) :
    ∃ y ∈ spectrumProjectorProgram input epsilon O w,
      runCoordinates9 input epsilon O y = hermitianProjector z := by
  let v := runWeighted (K := K) input epsilon w
  have he := (mul_ne_zero_iff.mp hex).1
  have hS := (phaseExceptional_properties (weightedP v) (weightedQ v) (weightedPole v) he).1
  obtain ⟨c,hc,hcx⟩ := List.mem_map.mp ((spectrumProgram_correct input epsilon O w hS x).mpr hx)
  obtain ⟨y,hy,hyz⟩ := projectorProgram_covers_candidate input epsilon O w hex c hc z (hcx.symm ▸ hm)
  exact ⟨y,List.mem_flatMap.mpr ⟨c,hc,hy⟩,hyz⟩

#print axioms projectorProgram_covers_candidate
end Program
end W3.FiniteInput
