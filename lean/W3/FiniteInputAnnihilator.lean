import W3.FiniteInputAnnihilatorPresentation
import W3.FiniteInputAnnihilatorNormalization

/-! # A uniform finite-input annihilator compiler
The compiler builds explicit singleton/tensor/monic-quotient power bases over a
free commutative ring. Every determinant coefficient is lowered by its finite
monomial expansion to arithmetic in the original fifteen inputs and epsilons.
Root and inverse normalizations use finite coefficient tests. There is no
algebraicity-to-expression choice, arbitrary basis, or annihilator oracle. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal

variable {n : Nat} {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K]
variable (input : Fin 15 → F) (epsilon : Fin n → F)

@[instance_reducible] def specializedAlgebra : Algebra (FreeCoefficientRing n) K :=
  ((algebraMap F K).comp (FreeCoefficientRing.specialize input epsilon)).toAlgebra

abbrev CodedPresentation (x : K) :=
  @RingExpressionPresentation (FreeCoefficientRing n) K _ _
    (specializedAlgebra input epsilon) x

theorem specialized_aeval (p : (FreeCoefficientRing n)[X]) (x : K) :
    letI := specializedAlgebra (K := K) input epsilon
    aeval x p = aeval x (p.map (FreeCoefficientRing.specialize input epsilon)) := by
  letI := specializedAlgebra (K := K) input epsilon
  simp only [aeval_def, eval₂_map]
  rfl

namespace CodedPresentation

def coefficient (c : CoefficientCode n) :
    CodedPresentation input epsilon (algebraMap F K (c.eval input epsilon)) := by
  letI := specializedAlgebra (K := K) input epsilon
  have h : algebraMap (FreeCoefficientRing n) K (MvPolynomial.X c) =
      algebraMap F K (c.eval input epsilon) := by
    change algebraMap F K (FreeCoefficientRing.specialize input epsilon (MvPolynomial.X c)) = _
    rw [FreeCoefficientRing.specialize_X]
  exact h ▸ RingExpressionPresentation.constant (R := FreeCoefficientRing n) (MvPolynomial.X c)

def zero : CodedPresentation input epsilon (0 : K) := by
  simpa only [CoefficientCode.eval, Rat.cast_zero, map_zero] using
    coefficient (K := K) input epsilon (.rational 0)

def selectedRoot (p : (FreeCoefficientRing n)[X])
    (hp : p.map (FreeCoefficientRing.specialize input epsilon) ≠ 0)
    (x : K) (hx : aeval x (p.map (FreeCoefficientRing.specialize input epsilon)) = 0) :
    CodedPresentation input epsilon x := by
  letI := specializedAlgebra (K := K) input epsilon
  apply RingExpressionPresentation.selectedRoot
    (FreeCoefficientRing.monicLift input epsilon p)
    (FreeCoefficientRing.monicLift_monic input epsilon p) x
  rw [specialized_aeval, FreeCoefficientRing.monicLift_map input epsilon p hp]
  simp only [map_mul, hx, zero_mul]

def inverse {x : K} (A : CodedPresentation input epsilon x) (hx : x ≠ 0) :
    CodedPresentation input epsilon x⁻¹ := by
  letI := specializedAlgebra (K := K) input epsilon
  let p := A.annihilator
  let f := FreeCoefficientRing.specialize input epsilon
  have hp : p.map f ≠ 0 := (A.annihilator_monic.map f).ne_zero
  have ha : aeval x (p.map f) = 0 := by
    rw [← specialized_aeval input epsilon p x]
    exact A.annihilator_aeval
  let r := FreeCoefficientRing.inverseRaw input epsilon p
  have hr : r.map f ≠ 0 := by
    rw [FreeCoefficientRing.inverseRaw_map]
    exact mt reverse_eq_zero.mp (normalizedInitial_ne_zero _ hp)
  apply RingExpressionPresentation.selectedRoot
    (FreeCoefficientRing.monicLift input epsilon r)
    (FreeCoefficientRing.monicLift_monic input epsilon r) x⁻¹
  rw [specialized_aeval, FreeCoefficientRing.monicLift_map input epsilon r hr]
  rw [FreeCoefficientRing.inverseRaw_map]
  exact inverseAnnihilator_aeval (p.map f) hp x hx ha

def codes {x : K} (A : CodedPresentation input epsilon x) : List (CoefficientCode n) :=
  letI := specializedAlgebra (K := K) input epsilon
  FreeCoefficientRing.polynomialCodes A.annihilator

theorem codes_spec {x : K} (A : CodedPresentation input epsilon x) :
    (coefficientPolynomial input epsilon (codes input epsilon A)).Monic ∧
      aeval x (coefficientPolynomial input epsilon (codes input epsilon A)) = 0 := by
  letI := specializedAlgebra (K := K) input epsilon
  rw [codes, FreeCoefficientRing.polynomialCodes_correct]
  exact ⟨A.annihilator_monic.map _, by
    rw [← specialized_aeval input epsilon A.annihilator x]
    exact A.annihilator_aeval⟩
end CodedPresentation

variable [LinearOrder K] [IsStrictOrderedRing K]
variable (O : RealRootEnumeration K)

/-- Recursive, syntax-directed construction of a presentation for the exact
operational interpreter output, including its zero fallbacks. -/
def Code.compileFinite (c : Code n) :
    CodedPresentation input epsilon (c.run input epsilon O).value := by
  letI := specializedAlgebra (K := K) input epsilon
  induction c with
  | coefficient a => exact CodedPresentation.coefficient input epsilon a
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb
  | neg a iha => exact iha.neg
  | inv a iha =>
    change CodedPresentation input epsilon ((a.run input epsilon O).inv).value
    unfold Evaluated.inv
    split_ifs with h
    · exact CodedPresentation.zero input epsilon
    · exact CodedPresentation.inverse input epsilon iha h
  | root cs i =>
    change CodedPresentation input epsilon
      (Evaluated.root O (coefficientPolynomial input epsilon cs) i).value
    unfold Evaluated.root
    split_ifs with hp
    · exact CodedPresentation.zero input epsilon
    · dsimp only
      split
      · exact CodedPresentation.zero input epsilon
      · rename_i x hx
        apply CodedPresentation.selectedRoot input epsilon (liftCoefficientPolynomial cs)
          (by simpa only [liftCoefficientPolynomial_map] using hp) x
        rw [liftCoefficientPolynomial_map]
        have hm := List.mem_of_getElem? hx
        have hpm : (coefficientPolynomial input epsilon cs).map (algebraMap F K) ≠ 0 :=
          (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hp
        have hr := (O.correct _ hpm x).mp hm
        simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hr
  | squareRoot a i iha =>
    change CodedPresentation input epsilon
      (Evaluated.squareRoot O (a.run input epsilon O) i).value
    unfold Evaluated.squareRoot
    dsimp only
    split
    · exact CodedPresentation.zero input epsilon
    · rename_i x hx
      apply iha.squareRoot x
      have hm := List.mem_of_getElem? hx
      have hp : (X^2-C (a.run input epsilon O).value : K[X]) ≠ 0 :=
        (monic_X_pow_sub_C _ (by decide : (2 : Nat) ≠ 0)).ne_zero
      have hr := (O.correct _ hp x).mp hm
      simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using hr

/-- The emitted artifact is a literal finite list of original-input arithmetic
programs, not a semantic polynomial whose coefficients require another oracle. -/
def Code.annihilatorCodes (c : Code n) : List (CoefficientCode n) :=
  CodedPresentation.codes input epsilon (c.compileFinite input epsilon O)

theorem Code.annihilatorCodes_spec (c : Code n) :
    (coefficientPolynomial input epsilon (c.annihilatorCodes input epsilon O)).Monic ∧
      aeval (c.run input epsilon O).value
        (coefficientPolynomial input epsilon (c.annihilatorCodes input epsilon O)) = 0 :=
  CodedPresentation.codes_spec input epsilon (c.compileFinite input epsilon O)

theorem Code.annihilatorCodes_ne_zero (c : Code n) :
    coefficientPolynomial input epsilon (c.annihilatorCodes input epsilon O) ≠ 0 :=
  (c.annihilatorCodes_spec input epsilon O).1.ne_zero

#print axioms Code.compileFinite
#print axioms Code.annihilatorCodes_spec
end W3.FiniteInput
