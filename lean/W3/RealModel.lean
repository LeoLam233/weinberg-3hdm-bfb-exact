import W3.Model
import W3.PhysicalFields
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
open scoped BigOperators
namespace W3.RealModel

/-- Real coordinates in row-major doublet order: re,im for each of 6 complex entries. -/
abbrev RealFields (K : Type*) := Fin 12 → K
abbrev Parameters (K : Type*) := Fin 15 → K

section PolynomialModel
variable {K : Type*} [CommRing K]
def radii (x : RealFields K) : Fin 3 → K :=
  ![x 0^2+x 1^2+x 6^2+x 7^2,
    x 2^2+x 3^2+x 8^2+x 9^2,
    x 4^2+x 5^2+x 10^2+x 11^2]
def offRe (x : RealFields K) : Fin 3 → K :=
  ![x 0*x 2+x 1*x 3+x 6*x 8+x 7*x 9,
    x 0*x 4+x 1*x 5+x 6*x 10+x 7*x 11,
    x 2*x 4+x 3*x 5+x 8*x 10+x 9*x 11]
def offIm (x : RealFields K) : Fin 3 → K :=
  ![x 0*x 3-x 1*x 2+x 6*x 9-x 7*x 8,
    x 0*x 5-x 1*x 4+x 6*x 11-x 7*x 10,
    x 2*x 5-x 3*x 4+x 8*x 11-x 9*x 10]
def mass (x : RealFields K) : K := ∑ i, x i ^ 2

/-- Integer polynomial, twice the original quartic. Avoids division in polynomial transfer. -/
def twiceQuartic (κ : Parameters K) (x : RealFields K) : K :=
  κ 0*radii x 0^2+κ 1*radii x 1^2+κ 2*radii x 2^2 +
  2*(κ 3*radii x 0*radii x 1+κ 4*radii x 0*radii x 2+κ 5*radii x 1*radii x 2)+
  2*(κ 6*(offRe x 0^2+offIm x 0^2)+κ 7*(offRe x 1^2+offIm x 1^2)+
    κ 8*(offRe x 2^2+offIm x 2^2))+
  2*(κ 9*(offRe x 0^2-offIm x 0^2)-2*κ 10*offRe x 0*offIm x 0+
    κ 11*(offRe x 1^2-offIm x 1^2)-2*κ 12*offRe x 1*offIm x 1+
    κ 13*(offRe x 2^2-offIm x 2^2)-2*κ 14*offRe x 2*offIm x 2)
end PolynomialModel

/-- The actual integer polynomial for twice the quartic, parameters and field variables separated. -/
def potentialPolynomial : MvPolynomial (Fin 15 ⊕ Fin 12) ℤ :=
  twiceQuartic (fun i => MvPolynomial.X (Sum.inl i)) (fun j => MvPolynomial.X (Sum.inr j))

def massConstraintPolynomial : MvPolynomial (Fin 12) ℤ :=
  mass (fun j => MvPolynomial.X j) - 1

lemma potentialPolynomial_eval {K : Type*} [CommRing K] (κ : Parameters K) (x : RealFields K) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) (Sum.elim κ x) potentialPolynomial =
      twiceQuartic κ x := by
  unfold potentialPolynomial twiceQuartic radii offRe offIm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp

lemma massConstraintPolynomial_eval {K : Type*} [CommRing K] (x : RealFields K) :
    MvPolynomial.eval₂Hom (Int.castRingHom K) x massConstraintPolynomial = mass x - 1 := by
  unfold massConstraintPolynomial
  rw [map_sub, map_one]
  simp [mass]

/-- Exact coordinate map, no phase/CP or support restriction. -/
def coordinates (φ : Fields) : RealFields ℝ :=
  ![(φ (0,0)).re,(φ (0,0)).im,(φ (0,1)).re,(φ (0,1)).im,
    (φ (0,2)).re,(φ (0,2)).im,(φ (1,0)).re,(φ (1,0)).im,
    (φ (1,1)).re,(φ (1,1)).im,(φ (1,2)).re,(φ (1,2)).im]
def fields (x : RealFields ℝ) : Fields := WithLp.toLp 2 (fun p =>
  (![![⟨x 0,x 1⟩,⟨x 2,x 3⟩,⟨x 4,x 5⟩],
     ![⟨x 6,x 7⟩,⟨x 8,x 9⟩,⟨x 10,x 11⟩]] : Fin 2 → Fin 3 → ℂ) p.1 p.2)
def couplings (κ : Parameters ℝ) : Couplings :=
  ⟨![κ 0,κ 1,κ 2],![κ 3,κ 4,κ 5],![κ 6,κ 7,κ 8],
    ![⟨κ 9,κ 10⟩,⟨κ 11,κ 12⟩,⟨κ 13,κ 14⟩]⟩

lemma coordinates_fields (x : RealFields ℝ) : coordinates (fields x) = x := by
  funext i; fin_cases i <;> rfl
lemma fields_coordinates (φ : Fields) : fields (coordinates φ) = φ := by
  apply PiLp.ext
  intro i
  rcases i with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> simp [fields,coordinates]

lemma radii_coordinates (φ : Fields) : radii (coordinates φ) = radius φ := by
  funext i; fin_cases i <;> simp [radii,coordinates,radius,Fin.sum_univ_two,Complex.normSq] <;> ring

lemma mass_coordinates (φ : Fields) : mass (coordinates φ) = ‖φ‖^2 := by
  rw [← total_radius]
  simp [mass,coordinates,radius,Fin.sum_univ_succ,Complex.normSq]
  ring

lemma twiceQuartic_coordinates (κ : Parameters ℝ) (φ : Fields) :
    twiceQuartic κ (coordinates φ) = 2 * quartic (couplings κ) φ := by
  simp [twiceQuartic,radii,offRe,offIm,coordinates,quartic,pairTerm,couplings,
    radius,gram,Fin.sum_univ_succ,Complex.normSq,pow_two]
  ring

lemma mass_fields (x : RealFields ℝ) : mass x = ‖fields x‖^2 := by
  simpa [coordinates_fields] using mass_coordinates (fields x)
lemma twiceQuartic_fields (κ : Parameters ℝ) (x : RealFields ℝ) :
    twiceQuartic κ x = 2 * quartic (couplings κ) (fields x) := by
  simpa [coordinates_fields] using twiceQuartic_coordinates κ (fields x)

/-- The base-field universal minimum property that will be transferred through the tower. -/
theorem real_minimum (κ : Parameters ℝ) :
    ∃ x : RealFields ℝ, mass x = 1 ∧
      ∀ y : RealFields ℝ, mass y = 1 → twiceQuartic κ x ≤ twiceQuartic κ y := by
  obtain ⟨φ,hφ,hmin⟩ := exists_normalized_minimum (couplings κ)
  refine ⟨coordinates φ,by simp [mass_coordinates,hφ],?_⟩
  intro y hy
  have hyn : ‖fields y‖ = 1 := by
    rw [mass_fields] at hy
    nlinarith [norm_nonneg (fields y)]
  rw [twiceQuartic_coordinates,twiceQuartic_fields]
  exact mul_le_mul_of_nonneg_left (hmin _ hyn) (by norm_num)

#print axioms real_minimum
end W3.RealModel
