import W3.InfinitesimalExtension
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Direct real-closedness transfer for the constructed ultrapower.
This proof lifts the finitely many polynomial coefficients, rather than assuming
an unformalized transfer principle. -/
noncomputable section
namespace W3.Infinitesimal
open Filter Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The actual quotient ring homomorphism from coordinate functions. -/
def germRingHom : (K → K) →+* Extension K where
  toFun := Germ.ofFun
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Representatives chosen to preserve zero exactly. -/
def coefficientRep (c : Extension K) : K → K :=
  if c = 0 then 0 else Quotient.out c

@[simp] theorem coefficientRep_zero : coefficientRep K 0 = 0 := by
  simp [coefficientRep]

@[simp] theorem germ_coefficientRep (c : Extension K) :
    germRingHom K (coefficientRep K c) = c := by
  unfold coefficientRep
  split_ifs with h
  · simp [h]
  · exact Quotient.out_eq c

/-- Finite polynomial coefficient lift, with no extraneous high-degree coefficients. -/
def polynomialLift (p : (Extension K)[X]) : (K → K)[X] :=
  ∑ n ∈ p.support, monomial n (coefficientRep K (p.coeff n))

@[simp] theorem coeff_polynomialLift (p : (Extension K)[X]) (n : ℕ) :
    (polynomialLift K p).coeff n = coefficientRep K (p.coeff n) := by
  classical
  by_cases h : p.coeff n = 0
  · simp [polynomialLift, Polynomial.coeff_sum, Polynomial.coeff_monomial,
      Polynomial.mem_support_iff, h]
  · simp [polynomialLift, Polynomial.coeff_sum, Polynomial.coeff_monomial,
      Polynomial.mem_support_iff, h]

@[simp] theorem map_polynomialLift (p : (Extension K)[X]) :
    (polynomialLift K p).map (germRingHom K) = p := by
  ext n
  simp only [Polynomial.coeff_map, coeff_polynomialLift, germ_coefficientRep]

@[simp] theorem natDegree_polynomialLift (p : (Extension K)[X]) :
    (polynomialLift K p).natDegree = p.natDegree := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_polynomialLift, Polynomial.coeff_eq_zero_of_natDegree_lt hn, coefficientRep_zero]
  · have h := Polynomial.natDegree_map_le (p := polynomialLift K p) (f := germRingHom K)
    simpa only [map_polynomialLift] using h

@[simp] theorem leadingCoeff_polynomialLift (p : (Extension K)[X]) :
    (polynomialLift K p).leadingCoeff = coefficientRep K p.leadingCoeff := by
  simp only [Polynomial.leadingCoeff, natDegree_polynomialLift, coeff_polynomialLift]

/-- Evaluate all lifted coefficient functions at one coordinate. -/
def coordinatePolynomial (p : (Extension K)[X]) (x : K) : K[X] :=
  (polynomialLift K p).map (Pi.evalRingHom (fun _ : K => K) x)

theorem eventually_coordinate_degree {p : (Extension K)[X]} (hp : p ≠ 0) :
    ∀ᶠ x in (extensionUltrafilter K : Filter K),
      (coordinatePolynomial K p x).natDegree = p.natDegree := by
  have hnonzero : germRingHom K (coefficientRep K p.leadingCoeff) ≠ 0 := by
    rw [germ_coefficientRep]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hev : ∀ᶠ x in (extensionUltrafilter K : Filter K),
      coefficientRep K p.leadingCoeff x ≠ 0 :=
    Ultrafilter.eventually_not.mpr (fun h => hnonzero (Germ.coe_eq.mpr h))
  apply hev.mono
  intro x hx
  unfold coordinatePolynomial
  rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero,
    natDegree_polynomialLift]
  simpa only [leadingCoeff_polynomialLift, Pi.evalRingHom_apply] using hx

variable [IsRealClosed K]

theorem extension_square_of_nonneg {x : Extension K} (hx : 0 ≤ x) : IsSquare x := by
  induction x using Germ.inductionOn with
  | h f =>
    have hf : ∀ᶠ i in (extensionUltrafilter K : Filter K), 0 ≤ f i := Germ.coe_le.mp hx
    let r : K → K := fun i => if h : 0 ≤ f i then Classical.choose (IsSquare.of_nonneg h) else 0
    refine ⟨germRingHom K r, ?_⟩
    apply Germ.coe_eq.mpr
    apply hf.mono
    intro i hi
    change f i = r i * r i
    dsimp only [r]
    rw [dif_pos hi]
    exact Classical.choose_spec (IsSquare.of_nonneg hi)

theorem extension_odd_polynomial_root {p : (Extension K)[X]} (hp : Odd p.natDegree) :
    ∃ x, p.IsRoot x := by
  have hp0 : p ≠ 0 := by
    intro h
    simp only [h, Polynomial.natDegree_zero] at hp
    exact Nat.not_odd_zero hp
  let r : K → K := fun i =>
    if h : Odd (coordinatePolynomial K p i).natDegree then
      Classical.choose (IsRealClosed.exists_isRoot_of_odd_natDegree h) else 0
  have hr : ∀ᶠ i in (extensionUltrafilter K : Filter K),
      (coordinatePolynomial K p i).eval (r i) = 0 := by
    apply (eventually_coordinate_degree K hp0).mono
    intro i hi
    have hi' : Odd (coordinatePolynomial K p i).natDegree := hi.symm ▸ hp
    dsimp only [r]
    rw [dif_pos hi']
    exact Classical.choose_spec (IsRealClosed.exists_isRoot_of_odd_natDegree hi')
  refine ⟨germRingHom K r, ?_⟩
  change p.eval (germRingHom K r) = 0
  rw [← map_polynomialLift K p, Polynomial.eval_map_apply]
  apply Germ.coe_eq.mpr
  apply hr.mono
  intro i hi
  change ((polynomialLift K p).map (Pi.evalRingHom (fun _ : K => K) i)).eval
    ((Pi.evalRingHom (fun _ : K => K) i) r) = 0 at hi
  rw [Polynomial.eval_map_apply] at hi
  exact hi

/-- Real closedness is actually preserved by the explicit extension. -/
instance extensionIsRealClosed : IsRealClosed (Extension K) :=
  IsRealClosed.of_linearOrderedField (extension_square_of_nonneg K)
    (extension_odd_polynomial_root K)

#print axioms extensionIsRealClosed
end W3.Infinitesimal
