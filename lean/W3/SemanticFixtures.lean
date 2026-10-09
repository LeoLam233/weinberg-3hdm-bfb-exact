import W3.ActualStability

/-! Small independently specified semantic controls for normalization, complex
orientation, charged support, zero input and strict stability. These controls
are not substitutes for the universal two-spectrum theorem. -/
noncomputable section
namespace W3.SemanticFixtures
open W3.RealModel W3.Infinitesimal
open scoped BigOperators

def zeroCouplings : W3.Couplings := ⟨0,0,0,0⟩

lemma zero_quartic (φ : W3.Fields) : W3.quartic zeroCouplings φ = 0 := by
  simp [W3.quartic,W3.pairTerm,zeroCouplings]

/-- A pure imaginary coupling is load-bearing: K01=1+i gives Re(i K01²)=-2. -/
def imaginaryCoupling : W3.Couplings := ⟨0,0,0,![Complex.I,0,0]⟩
def imaginaryDirection : W3.Fields := fields ![1,0,1,1,0,0,0,0,0,0,0,0]

example : W3.gram imaginaryDirection 0 1 = (1+Complex.I : ℂ) := by
  apply Complex.ext <;> norm_num [imaginaryDirection,fields,W3.gram,Fin.sum_univ_two]
example : W3.quartic imaginaryCoupling imaginaryDirection = -2 := by
  norm_num [imaginaryCoupling,imaginaryDirection,fields,W3.quartic,W3.pairTerm,W3.radius,
    W3.gram,Fin.sum_univ_three,Fin.sum_univ_two,Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im]

/-- Orthogonal nonzero doublets retain b while annihilating the c and d terms. -/
def chargedDirection : W3.Fields := fields ![1,0,0,0,0,0,0,0,1,0,0,0]
example (b c : ℝ) (d : ℂ) :
    W3.quartic ⟨0,![b,0,0],![c,0,0],![d,0,0]⟩ chargedDirection = b := by
  simp [chargedDirection,fields,W3.quartic,W3.pairTerm,W3.radius,W3.gram,
    Fin.sum_univ_three,Fin.sum_univ_two,Complex.normSq_apply,pow_two,Complex.mul_re,Complex.mul_im]

lemma zero_parameters (φ : W3.Fields) : W3.quartic (couplings (0 : Parameters ℝ)) φ = 0 := by
  simp [couplings,W3.quartic,W3.pairTerm,Fin.sum_univ_three]

/-- Completely singular zero input must fall strictly between the two epsilon thresholds. -/
example : 0 < deformedMinimum (0 : Parameters ℝ) ∧
    deformedMinimum (0 : Parameters ℝ) < 2*chronologicalEpsilon 0 := by
  have hm : realMinimum (0 : Parameters ℝ) = 0 := by
    rw [← realMinimum_field_value,zero_parameters]
  exact ((actual_minimum_signs_and_residue (0 : Parameters ℝ)).2.2.2.1).mp hm

/-- A simple strictly positive model checks the a_i/2 normalization. -/
def diagonalPositive : W3.Couplings := ⟨![2,2,2],0,0,0⟩
lemma diagonalPositive_quartic (φ : W3.Fields) :
    W3.quartic diagonalPositive φ = ∑ i, (W3.radius φ i)^2 := by
  simp [W3.quartic,W3.pairTerm,diagonalPositive,Fin.sum_univ_three]
  ring

example : ∀ φ : W3.Fields, φ ≠ 0 → 0 < W3.quartic diagonalPositive φ := by
  rw [W3.positive_iff_normalized]
  intro φ hφ
  rw [diagonalPositive_quartic]
  have hsum := W3.total_radius φ
  rw [hφ] at hsum
  simp only [Fin.sum_univ_three,one_pow] at hsum ⊢
  have h0 := W3.radius_nonneg φ 0
  have h1 := W3.radius_nonneg φ 1
  have h2 := W3.radius_nonneg φ 2
  nlinarith [sq_nonneg (W3.radius φ 0-W3.radius φ 1),
    sq_nonneg (W3.radius φ 0-W3.radius φ 2),sq_nonneg (W3.radius φ 1-W3.radius φ 2)]

end W3.SemanticFixtures
