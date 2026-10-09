import W3.EliminationDual

noncomputable section
namespace W3.Elimination

section ElementaryRing
variable {R : Type*} [CommRing R]

def weightedLoop (w : WeightedData R) : R :=
  (w.d12r*w.d23r-w.d12i*w.d23i)*(-w.d13i) +
    (w.d12r*w.d23i+w.d12i*w.d23r)*w.d13r

def pairExceptional (ai aj e dr di gi gj : R) : R :=
  (aj*gi^2-2*e*gi*gj+ai*gj^2)^2 - 4*(dr^2+di^2)*gi^2*gj^2

def pair12Exceptional (w : WeightedData R) : R :=
  pairExceptional w.alpha1 w.alpha2 w.e12 w.d12r w.d12i w.g1 w.g2

def pair13Exceptional (w : WeightedData R) : R :=
  pairExceptional w.alpha1 w.alpha3 w.e13 w.d13r w.d13i w.g1 w.g3

def pair23Exceptional (w : WeightedData R) : R :=
  pairExceptional w.alpha2 w.alpha3 w.e23 w.d23r w.d23i w.g2 w.g3

/-- All remaining elementary weighted exclusions: loop, individual weights,
β, and the three phase-independent pair denominators. -/
def elementaryExceptional (w : WeightedData R) : R :=
  weightedLoop w * w.g1 * w.g2 * w.g3 * (w.g1+w.g2+w.g3) *
    pair12Exceptional w * pair13Exceptional w * pair23Exceptional w

def completeWeightedExceptional (w : WeightedData R) : R :=
  weightedExceptional w * elementaryExceptional w

theorem weightedLoop_eq (w : WeightedData R) : weightedLoop w =
    (W3.Weighted.ComplexPair.mul
      (W3.Weighted.ComplexPair.mul (toSpectrum w).d₁₂ (toSpectrum w).d₂₃)
      (W3.Weighted.ComplexPair.conj (toSpectrum w).d₁₃)).im := rfl

@[simp] theorem map_elementaryExceptional {S : Type*} [CommRing S]
    (f : R →+* S) (w : WeightedData R) :
    f (elementaryExceptional w) = elementaryExceptional (mapWeighted f w) := by
  simp [elementaryExceptional, weightedLoop, pair12Exceptional, pair13Exceptional,
    pair23Exceptional, pairExceptional, mapWeighted, map_ofNat]

@[simp] theorem map_completeWeightedExceptional {S : Type*} [CommRing S]
    (f : R →+* S) (w : WeightedData R) :
    f (completeWeightedExceptional w) = completeWeightedExceptional (mapWeighted f w) := by
  simp [completeWeightedExceptional]

theorem pairExceptional_scale (r ai aj e dr di gi gj : R) :
    pairExceptional (r*ai) (r*aj) (r*e) (r*dr) (r*di) (r*gi) (r*gj) =
      r^6 * pairExceptional ai aj e dr di gi gj := by
  unfold pairExceptional
  ring

theorem weightedLoop_scale (r : R) (w : WeightedData R) :
    weightedLoop (scaleWeighted r w) = r^3 * weightedLoop w := by
  unfold weightedLoop scaleWeighted
  ring

theorem elementaryExceptional_scale (r : R) (w : WeightedData R) :
    elementaryExceptional (scaleWeighted r w) = r^25 * elementaryExceptional w := by
  unfold elementaryExceptional
  rw [weightedLoop_scale]
  simp only [pair12Exceptional,
    pair13Exceptional, pair23Exceptional, scaleWeighted, pairExceptional_scale]
  ring

theorem completeWeightedExceptional_scale (r : R) (w : WeightedData R) :
    completeWeightedExceptional (scaleWeighted r w) = r^349 * completeWeightedExceptional w := by
  unfold completeWeightedExceptional
  rw [weightedExceptional_scale, elementaryExceptional_scale]
  ring

/-- Canonical original-coordinate primal polynomial, including every weighted exclusion. -/
def completePrimalPolynomial : MvPolynomial (Fin 15) R :=
  completeWeightedExceptional (originalPrimal MvPolynomial.X)

/-- Canonical original-coordinate dual polynomial, including invertibility and every weighted exclusion. -/
def completeDualPolynomial : MvPolynomial (Fin 15) R :=
  originalInverseDen MvPolynomial.X * completeWeightedExceptional (originalDualNumerators MvPolynomial.X)

theorem completePrimalPolynomial_eval {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → S) :
    MvPolynomial.eval₂ f x (completePrimalPolynomial (R := R)) =
      completeWeightedExceptional (originalPrimal x) := by
  change (MvPolynomial.eval₂Hom f x) (completeWeightedExceptional (originalPrimal MvPolynomial.X)) = _
  rw [map_completeWeightedExceptional, map_originalPrimal]
  simp only [MvPolynomial.eval₂Hom_X']

theorem completeDualPolynomial_eval {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → S) :
    MvPolynomial.eval₂ f x (completeDualPolynomial (R := R)) =
      originalInverseDen x * completeWeightedExceptional (originalDualNumerators x) := by
  change (MvPolynomial.eval₂Hom f x)
    (originalInverseDen MvPolynomial.X * completeWeightedExceptional (originalDualNumerators MvPolynomial.X)) = _
  rw [map_mul, map_originalInverseDen, map_completeWeightedExceptional, map_originalDualNumerators]
  simp only [MvPolynomial.eval₂Hom_X']

end ElementaryRing

section ElementaryField
variable {K : Type*} [Field K] [CharZero K]

theorem elementaryExceptional_properties (w : WeightedData K) (h : elementaryExceptional w ≠ 0) :
    weightedLoop w ≠ 0 ∧ w.g1 ≠ 0 ∧ w.g2 ≠ 0 ∧ w.g3 ≠ 0 ∧
      w.g1+w.g2+w.g3 ≠ 0 ∧ pair12Exceptional w ≠ 0 ∧
      pair13Exceptional w ≠ 0 ∧ pair23Exceptional w ≠ 0 := by
  simpa only [elementaryExceptional, mul_ne_zero_iff, and_assoc] using h

/-- The eliminated pair polynomial excludes each signed phase branch denominator. -/
theorem pair_denominator_ne_zero (ai aj e dr di gi gj m s : K)
    (hm : m^2=dr^2+di^2) (hs : s^2=1)
    (he : pairExceptional ai aj e dr di gi gj ≠ 0) :
    (aj/2)*gi^2-(e+s*m)*gi*gj+(ai/2)*gj^2 ≠ 0 := by
  intro hz
  apply he
  have ha : aj*gi^2-2*e*gi*gj+ai*gj^2=2*s*m*gi*gj := by
    linear_combination 2*hz
  unfold pairExceptional
  rw [ha]
  calc
    (2*s*m*gi*gj)^2-4*(dr^2+di^2)*gi^2*gj^2 =
      4*gi^2*gj^2*(s^2*m^2-(dr^2+di^2)) := by ring
    _ = 0 := by rw [hs, hm]; ring

/-- On a two-element support, a phase-stationary zero cannot lie on g·r=0.
Here m is the real phase-rotated coupling, so m²=|d|²; it may have either sign. -/
theorem pair_phase_zero_excludes_pole (ai aj e dr di gi gj m ri rj : K)
    (hm : m^2=dr^2+di^2) (he : pairExceptional ai aj e dr di gi gj ≠ 0)
    (hri : ri ≠ 0)
    (hp : (ai/2)*ri^2+(e+m)*ri*rj+(aj/2)*rj^2=0) : gi*ri+gj*rj ≠ 0 := by
  intro hg
  have hW := pair_denominator_ne_zero ai aj e dr di gi gj m 1 hm (by simp) he
  apply hW
  apply mul_left_cancel₀ (pow_ne_zero 2 hri)
  linear_combination gj^2*hp - ((e+m)*ri*gj+(aj/2)*(gj*rj-gi*ri))*hg

end ElementaryField

section ElementaryWitness
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem weightedLoop_edge_norms_ne_zero (w : WeightedData K) (h : weightedLoop w ≠ 0) :
    w.d12r^2+w.d12i^2 ≠ 0 ∧ w.d13r^2+w.d13i^2 ≠ 0 ∧ w.d23r^2+w.d23i^2 ≠ 0 := by
  have zeros (a b : K) (hz : a^2+b^2=0) : a=0 ∧ b=0 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    obtain ⟨hr, hi⟩ := zeros w.d12r w.d12i hz
    apply h
    simp [weightedLoop, hr, hi]
  · intro hz
    obtain ⟨hr, hi⟩ := zeros w.d13r w.d13i hz
    apply h
    simp [weightedLoop, hr, hi]
  · intro hz
    obtain ⟨hr, hi⟩ := zeros w.d23r w.d23i hz
    apply h
    simp [weightedLoop, hr, hi]

theorem weightedWitness_elementary_ne_zero : elementaryExceptional (weightedWitness : WeightedData K) ≠ 0 := by
  norm_num [elementaryExceptional, weightedLoop, pair12Exceptional, pair13Exceptional,
    pair23Exceptional, pairExceptional, weightedWitness]

theorem weightedWitness_complete_ne_zero : completeWeightedExceptional (weightedWitness : WeightedData K) ≠ 0 :=
  mul_ne_zero weightedWitness_exceptional_ne_zero weightedWitness_elementary_ne_zero

theorem completePrimalPolynomial_ne_zero : completePrimalPolynomial (R := K) ≠ 0 := by
  intro h
  have he := completePrimalPolynomial_eval (RingHom.id K) (originalPrimalWitness : Fin 15 → K)
  rw [h, MvPolynomial.eval₂_zero, originalPrimal_witness_eq] at he
  exact weightedWitness_complete_ne_zero he.symm

theorem originalDualWitness_complete_cleared_ne_zero :
    originalInverseDen (originalDualWitness : Fin 15 → K) *
      completeWeightedExceptional (originalDualNumerators (originalDualWitness : Fin 15 → K)) ≠ 0 := by
  apply mul_ne_zero originalDualWitness_den_ne_zero
  rw [originalDualNumerators_eq _ originalDualWitness_den_ne_zero, completeWeightedExceptional_scale,
    originalDual_witness_eq]
  exact mul_ne_zero (pow_ne_zero _ originalDualWitness_den_ne_zero) weightedWitness_complete_ne_zero

theorem completeDualPolynomial_ne_zero : completeDualPolynomial (R := K) ≠ 0 := by
  intro h
  have he := completeDualPolynomial_eval (RingHom.id K) (originalDualWitness : Fin 15 → K)
  rw [h, MvPolynomial.eval₂_zero] at he
  exact originalDualWitness_complete_cleared_ne_zero he.symm

end ElementaryWitness

section CompleteSpecialization
variable {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Field K] [Algebra R K]

theorem completePrimal_ne_zero_of_independent (x : Fin 15 → K) (hx : AlgebraicIndependent R x) :
    completeWeightedExceptional (originalPrimal x) ≠ 0 := by
  intro hz
  apply completePrimalPolynomial_ne_zero (K := R)
  apply hx.eq_zero_of_aeval_eq_zero
  change MvPolynomial.eval₂ (algebraMap R K) x (completePrimalPolynomial (R := R)) = 0
  rw [completePrimalPolynomial_eval, hz]

theorem completeDual_ne_zero_of_independent (x : Fin 15 → K) (hx : AlgebraicIndependent R x) :
    originalInverseDen x ≠ 0 ∧ completeWeightedExceptional (originalDual x) ≠ 0 := by
  have hc : originalInverseDen x * completeWeightedExceptional (originalDualNumerators x) ≠ 0 := by
    intro hz
    apply completeDualPolynomial_ne_zero (K := R)
    apply hx.eq_zero_of_aeval_eq_zero
    change MvPolynomial.eval₂ (algebraMap R K) x (completeDualPolynomial (R := R)) = 0
    rw [completeDualPolynomial_eval, hz]
  obtain ⟨hd, he⟩ := mul_ne_zero_iff.mp hc
  refine ⟨hd, ?_⟩
  rw [originalDualNumerators_eq x hd, completeWeightedExceptional_scale] at he
  exact (mul_ne_zero_iff.mp he).2

end CompleteSpecialization
end W3.Elimination
