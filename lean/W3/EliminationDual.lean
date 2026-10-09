import W3.EliminationPrimal
import W3.EliminationScaling

noncomputable section
namespace W3.Elimination

section DualRing
variable {R : Type*} [CommRing R]

/-- Determinant of the original real symmetric diagonal-sector block. -/
def originalMatrixDet (x : Fin 15 → R) : R :=
  x 0*x 1*x 2 + 2*x 3*x 4*x 5 - x 0*(x 5)^2 - x 1*(x 4)^2 - x 2*(x 3)^2

def originalDelta12 (x : Fin 15 → R) : R := (x 6)^2-(x 9)^2-(x 10)^2
def originalDelta13 (x : Fin 15 → R) : R := (x 7)^2-(x 11)^2-(x 12)^2
def originalDelta23 (x : Fin 15 → R) : R := (x 8)^2-(x 13)^2-(x 14)^2

def originalAdj (x : Fin 15 → R) : Fin 6 → R :=
  ![x 1*x 2-(x 5)^2, x 0*x 2-(x 4)^2, x 0*x 1-(x 3)^2,
    x 4*x 5-x 2*x 3, x 3*x 5-x 1*x 4, x 3*x 4-x 0*x 5]

def originalDeltaProduct (x : Fin 15 → R) : R :=
  originalDelta12 x * originalDelta13 x * originalDelta23 x

def originalInverseDen (x : Fin 15 → R) : R := originalMatrixDet x * originalDeltaProduct x

/-- Polynomial common numerators of all fifteen dual weighted coordinates. -/
def originalDualNumerators (x : Fin 15 → R) : WeightedData R :=
  let a := originalAdj x
  let d := originalMatrixDet x
  let p := originalDeltaProduct x
  let d12 := originalDelta12 x
  let d13 := originalDelta13 x
  let d23 := originalDelta23 x
  ⟨2*a 0*p, 2*a 1*p, 2*a 2*p,
    2*(a 3*p+x 6*d*d13*d23), 2*(a 4*p+x 7*d*d12*d23), 2*(a 5*p+x 8*d*d12*d13),
    -2*x 9*d*d13*d23, -2*x 10*d*d13*d23,
    -2*x 11*d*d12*d23, -2*x 12*d*d12*d23,
    -2*x 13*d*d12*d13, -2*x 14*d*d12*d13,
    (a 0+a 3+a 4)*p, (a 3+a 1+a 5)*p, (a 4+a 5+a 2)*p⟩

def originalDualExceptionalPolynomial : MvPolynomial (Fin 15) R :=
  originalInverseDen MvPolynomial.X * weightedExceptional (originalDualNumerators MvPolynomial.X)

@[simp] theorem map_originalInverseDen {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → R) :
    f (originalInverseDen x) = originalInverseDen (fun i => f (x i)) := by
  simp [originalInverseDen, originalMatrixDet, originalDeltaProduct,
    originalDelta12, originalDelta13, originalDelta23, map_ofNat]

@[simp] theorem map_originalDualNumerators {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → R) :
    mapWeighted f (originalDualNumerators x) = originalDualNumerators (fun i => f (x i)) := by
  simp [originalDualNumerators, originalAdj, originalMatrixDet, originalDeltaProduct,
    originalDelta12, originalDelta13, originalDelta23, mapWeighted, map_ofNat]

theorem originalDualPolynomial_eval {S : Type*} [CommRing S]
    (f : R →+* S) (x : Fin 15 → S) :
    MvPolynomial.eval₂ f x (originalDualExceptionalPolynomial (R := R)) =
      originalInverseDen x * weightedExceptional (originalDualNumerators x) := by
  change (MvPolynomial.eval₂Hom f x)
    (originalInverseDen MvPolynomial.X * weightedExceptional (originalDualNumerators MvPolynomial.X)) = _
  rw [map_mul, map_originalInverseDen, map_weightedExceptional, map_originalDualNumerators]
  simp only [MvPolynomial.eval₂Hom_X']

end DualRing

section DualField
variable {K : Type*} [Field K]

/-- The explicit inverse-operator spectrum, in original real coordinates. -/
def originalDual (x : Fin 15 → K) : WeightedData K :=
  let a := originalAdj x
  let d := originalMatrixDet x
  let d12 := originalDelta12 x
  let d13 := originalDelta13 x
  let d23 := originalDelta23 x
  ⟨2*(a 0/d), 2*(a 1/d), 2*(a 2/d),
    2*(a 3/d+x 6/d12), 2*(a 4/d+x 7/d13), 2*(a 5/d+x 8/d23),
    -2*x 9/d12, -2*x 10/d12, -2*x 11/d13, -2*x 12/d13, -2*x 13/d23, -2*x 14/d23,
    (a 0+a 3+a 4)/d, (a 3+a 1+a 5)/d, (a 4+a 5+a 2)/d⟩

theorem originalInverseDen_nonzero_factors (x : Fin 15 → K) (h : originalInverseDen x ≠ 0) :
    originalMatrixDet x ≠ 0 ∧ originalDelta12 x ≠ 0 ∧ originalDelta13 x ≠ 0 ∧ originalDelta23 x ≠ 0 := by
  simpa only [originalInverseDen, originalDeltaProduct, mul_ne_zero_iff, and_assoc] using h

theorem originalDualNumerators_eq (x : Fin 15 → K) (h : originalInverseDen x ≠ 0) :
    originalDualNumerators x = scaleWeighted (originalInverseDen x) (originalDual x) := by
  obtain ⟨hd, h12, h13, h23⟩ := originalInverseDen_nonzero_factors x h
  simp only [originalDualNumerators, scaleWeighted, originalDual, originalInverseDen, originalDeltaProduct]
  congr 1 <;> field_simp <;> ring

theorem dual_exceptional_of_cleared_nonzero (x : Fin 15 → K)
    (h : originalInverseDen x * weightedExceptional (originalDualNumerators x) ≠ 0) :
    originalInverseDen x ≠ 0 ∧ weightedExceptional (originalDual x) ≠ 0 := by
  obtain ⟨hd, he⟩ := mul_ne_zero_iff.mp h
  refine ⟨hd, ?_⟩
  rw [originalDualNumerators_eq x hd, weightedExceptional_scale] at he
  exact (mul_ne_zero_iff.mp he).2

end DualField

section DualWitness
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact original coefficients whose inverse weighted spectrum is the printed witness. -/
def originalDualWitness : Fin 15 → K :=
  ![1679/1197, 1487/1197, 1391/1197, -289/1197, -193/1197, -1/1197,
    -400/2317, 171696/1459, -1040/387,
    6400/2317, 1920/2317, 169344/1459, -40320/1459, -512/129, 896/387]

theorem originalDualWitness_den_ne_zero : originalInverseDen (originalDualWitness : Fin 15 → K) ≠ 0 := by
  norm_num [originalInverseDen, originalMatrixDet, originalDeltaProduct,
    originalDelta12, originalDelta13, originalDelta23, originalDualWitness]

theorem originalDual_witness_eq : originalDual (originalDualWitness : Fin 15 → K) = weightedWitness := by
  norm_num [originalDual, originalAdj, originalMatrixDet, originalDelta12, originalDelta13,
    originalDelta23, originalDualWitness, weightedWitness]

theorem originalDualWitness_cleared_ne_zero :
    originalInverseDen (originalDualWitness : Fin 15 → K) *
      weightedExceptional (originalDualNumerators (originalDualWitness : Fin 15 → K)) ≠ 0 := by
  apply mul_ne_zero originalDualWitness_den_ne_zero
  rw [originalDualNumerators_eq _ originalDualWitness_den_ne_zero, weightedExceptional_scale,
    originalDual_witness_eq]
  exact mul_ne_zero (pow_ne_zero _ originalDualWitness_den_ne_zero) weightedWitness_exceptional_ne_zero

theorem originalDualExceptionalPolynomial_ne_zero :
    originalDualExceptionalPolynomial (R := K) ≠ 0 := by
  intro h
  have he := originalDualPolynomial_eval (RingHom.id K) (originalDualWitness : Fin 15 → K)
  rw [h, MvPolynomial.eval₂_zero] at he
  exact originalDualWitness_cleared_ne_zero he.symm

end DualWitness

section DualSpecialization
variable {R K : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Field K] [Algebra R K]

/-- Full dual genericity, discharged by one explicitly nonzero original-coordinate polynomial. -/
theorem originalDualExceptional_ne_zero_of_independent (x : Fin 15 → K)
    (hx : AlgebraicIndependent R x) :
    originalInverseDen x ≠ 0 ∧ weightedExceptional (originalDual x) ≠ 0 := by
  apply dual_exceptional_of_cleared_nonzero
  intro hz
  apply originalDualExceptionalPolynomial_ne_zero (K := R)
  apply hx.eq_zero_of_aeval_eq_zero
  change MvPolynomial.eval₂ (algebraMap R K) x (originalDualExceptionalPolynomial (R := R)) = 0
  rw [originalDualPolynomial_eval, hz]

end DualSpecialization
end W3.Elimination
