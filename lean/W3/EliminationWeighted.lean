import W3.EliminationGeneric
import W3.WeightedPhase

noncomputable section
namespace W3.Elimination
open Polynomial

/-- All fifteen real coordinates of the common weighted spectrum. -/
structure WeightedData (R : Type*) where
  alpha1 : R
  alpha2 : R
  alpha3 : R
  e12 : R
  e13 : R
  e23 : R
  d12r : R
  d12i : R
  d13r : R
  d13i : R
  d23r : R
  d23i : R
  g1 : R
  g2 : R
  g3 : R

section WeightedRing
variable {R : Type*} [CommRing R]

def scaleRow (k : R) (p : PhaseRow R) : PhaseRow R :=
  ⟨k*p.ar, k*p.ai, k*p.br, k*p.bi, k*p.cr, k*p.ci⟩

def subRow (p q : PhaseRow R) : PhaseRow R :=
  ⟨p.ar-q.ar, p.ai-q.ai, p.br-q.br, p.bi-q.bi, p.cr-q.cr, p.ci-q.ci⟩

/-- The three real/imaginary rows of equation (12), written without complex notation. -/
def weightedC1 (w : WeightedData R) : PhaseRow R :=
  ⟨w.e13*w.d12r, w.e13*w.d12i, -w.e12*w.d13r, -w.e12*w.d13i,
    w.alpha1*w.d23r - (w.d13r*w.d12r+w.d13i*w.d12i),
    w.alpha1*w.d23i - (w.d13i*w.d12r-w.d13r*w.d12i)⟩

def weightedC2 (w : WeightedData R) : PhaseRow R :=
  ⟨w.e23*w.d12r, w.e23*w.d12i,
    w.d12r*w.d23r-w.d12i*w.d23i-w.alpha2*w.d13r,
    w.d12r*w.d23i+w.d12i*w.d23r-w.alpha2*w.d13i,
    w.e12*w.d23r, w.e12*w.d23i⟩

def weightedC3 (w : WeightedData R) : PhaseRow R :=
  ⟨w.alpha3*w.d12r-(w.d13r*w.d23r+w.d13i*w.d23i),
    w.alpha3*w.d12i-(w.d13i*w.d23r-w.d13r*w.d23i),
    -w.e23*w.d13r, -w.e23*w.d13i, w.e13*w.d23r, w.e13*w.d23i⟩

def weightedF (w : WeightedData R) : PhaseRow R :=
  subRow (scaleRow w.g1 (weightedC2 w)) (scaleRow w.g2 (weightedC1 w))

def weightedG (w : WeightedData R) : PhaseRow R :=
  subRow (scaleRow w.g1 (weightedC3 w)) (scaleRow w.g3 (weightedC1 w))

def weightedH (w : WeightedData R) : PhaseRow R :=
  ⟨w.g3*w.d12r, w.g3*w.d12i, -w.g2*w.d13r, -w.g2*w.d13i,
    w.g1*w.d23r, w.g1*w.d23i⟩

/-- Fixed, nonzero integer scalings make the printed rational witness primitive. -/
def weightedP (w : WeightedData R) : PhaseRow R := scaleRow 3150 (weightedF w)
def weightedQ (w : WeightedData R) : PhaseRow R := scaleRow 14700 (weightedG w)
def weightedPole (w : WeightedData R) : PhaseRow R := scaleRow 105 (weightedH w)

def weightedExceptional (w : WeightedData R) : R :=
  phaseExceptional (weightedP w) (weightedQ w) (weightedPole w)

theorem phaseValue_scale (k : R) (p : PhaseRow R) (t u : R) :
    phaseValue (scaleRow k p) t u = k * phaseValue p t u := by
  unfold phaseValue scaleRow
  ring

theorem phaseHom_scale (k : R) (p : PhaseRow R) (t₀ t₁ u₀ u₁ : R) :
    phaseHom (scaleRow k p) t₀ t₁ u₀ u₁ = k * phaseHom p t₀ t₁ u₀ u₁ := by
  unfold phaseHom scaleRow
  ring

/-- Bridge to the independently proved current/stationarity representation. -/
def toSpectrum (w : WeightedData R) : W3.Weighted.SpectrumData R :=
  ⟨w.alpha1, w.alpha2, w.alpha3, w.e12, w.e13, w.e23,
    ⟨w.d12r, w.d12i⟩, ⟨w.d13r, w.d13i⟩, ⟨w.d23r, w.d23i⟩⟩

theorem weightedC1_eq (w : WeightedData R) : weightedC1 w = W3.Weighted.cRow₁ (toSpectrum w) := by
  simp only [weightedC1, W3.Weighted.cRow₁, W3.Weighted.complexRow, toSpectrum,
    W3.Weighted.ComplexPair.scale, W3.Weighted.ComplexPair.sub,
    W3.Weighted.ComplexPair.mul, W3.Weighted.ComplexPair.conj]
  congr 1 <;> ring

theorem weightedC2_eq (w : WeightedData R) : weightedC2 w = W3.Weighted.cRow₂ (toSpectrum w) := by
  rfl

theorem weightedC3_eq (w : WeightedData R) : weightedC3 w = W3.Weighted.cRow₃ (toSpectrum w) := by
  simp only [weightedC3, W3.Weighted.cRow₃, W3.Weighted.complexRow, toSpectrum,
    W3.Weighted.ComplexPair.scale, W3.Weighted.ComplexPair.sub,
    W3.Weighted.ComplexPair.mul, W3.Weighted.ComplexPair.conj]
  congr 1 <;> ring

theorem weightedF_eq (w : WeightedData R) :
    weightedF w = W3.Weighted.rowDifference w.g1 w.g2
      (W3.Weighted.cRow₁ (toSpectrum w)) (W3.Weighted.cRow₂ (toSpectrum w)) := by
  rw [weightedF, weightedC1_eq, weightedC2_eq]
  rfl

theorem weightedG_eq (w : WeightedData R) :
    weightedG w = W3.Weighted.rowDifference w.g1 w.g3
      (W3.Weighted.cRow₁ (toSpectrum w)) (W3.Weighted.cRow₃ (toSpectrum w)) := by
  rw [weightedG, weightedC1_eq, weightedC3_eq]
  rfl

end WeightedRing

section WeightedField
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def weightedWitness : WeightedData K :=
  ⟨3/2, 5/3, 7/4, 1/3, -2/5, 3/7, 2/3, 1/5, 3/5, -1/7, -4/7, 1/3, 1, 1, 1⟩

theorem weightedWitness_P : weightedP (weightedWitness : WeightedData K) = witnessP := by
  norm_num [weightedP, weightedF, weightedC2, weightedC1, scaleRow, subRow, weightedWitness, witnessP]

theorem weightedWitness_Q : weightedQ (weightedWitness : WeightedData K) = witnessQ := by
  norm_num [weightedQ, weightedG, weightedC3, weightedC1, scaleRow, subRow, weightedWitness, witnessQ]

theorem weightedWitness_H : weightedPole (weightedWitness : WeightedData K) = witnessH := by
  norm_num [weightedPole, weightedH, scaleRow, weightedWitness, witnessH]

theorem weightedWitness_exceptional_ne_zero :
    weightedExceptional (weightedWitness : WeightedData K) ≠ 0 := by
  unfold weightedExceptional
  rw [weightedWitness_P, weightedWitness_Q, weightedWitness_H]
  exact witness_phaseExceptional_ne_zero

theorem weighted_candidates_exact (w : WeightedData K) (he : weightedExceptional w ≠ 0)
    (t u : K) :
    ((t, u) ∈ phaseCandidates (weightedP w) (weightedQ w) ↔
      phaseValue (weightedF w) t u = 0 ∧ phaseValue (weightedG w) t u = 0) ∧
    ((t, u) ∈ phaseCandidates (weightedP w) (weightedQ w) → phaseValue (weightedH w) t u ≠ 0) := by
  have h := generic_phase_candidates_exact (weightedP w) (weightedQ w) (weightedPole w) he t u
  refine ⟨?_, ?_⟩
  · simpa only [weightedP, weightedQ, phaseValue_scale,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or] using h.1
  · intro hc hz
    apply h.2 hc
    rw [weightedPole, phaseValue_scale, hz, mul_zero]

end WeightedField
end W3.Elimination
