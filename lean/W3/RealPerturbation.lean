import W3.RealModel
import W3.InfinitesimalPerturbation

/-! Exact fifteen-coordinate deformation and physical monomial bounds.
All algebra and inequalities are over arbitrary ordered fields. -/
noncomputable section
open scoped BigOperators
namespace W3.RealModel
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def quarticReal (κ : Parameters K) (x : RealFields K) : K := twiceQuartic κ x / 2

def monomials (x : RealFields K) : Fin 15 → K :=
  ![radii x 0^2/2, radii x 1^2/2, radii x 2^2/2,
    radii x 0*radii x 1, radii x 0*radii x 2, radii x 1*radii x 2,
    offRe x 0^2+offIm x 0^2, offRe x 1^2+offIm x 1^2, offRe x 2^2+offIm x 2^2,
    offRe x 0^2-offIm x 0^2, -2*offRe x 0*offIm x 0,
    offRe x 1^2-offIm x 1^2, -2*offRe x 1*offIm x 1,
    offRe x 2^2-offIm x 2^2, -2*offRe x 2*offIm x 2]

def deformedParameters (κ : Parameters K) (e0 : K) (e : Fin 15 → K) : Parameters K :=
  fun i => κ i + (if i.val < 6 then 2*e0 else 0) + e i

lemma sum_radii (x : RealFields K) : ∑ i, radii x i = mass x := by
  simp [radii, mass, Fin.sum_univ_succ]
  ring

lemma radii_nonneg (x : RealFields K) (i : Fin 3) : 0 ≤ radii x i := by
  fin_cases i <;> simp [radii] <;> positivity

lemma radii_le_one (x : RealFields K) (hx : mass x = 1) (i : Fin 3) : radii x i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => radii_nonneg x j)
    (Finset.mem_univ i)
  simpa [sum_radii, hx] using h

lemma radii_pair_sum_le (x : RealFields K) (hx : mass x = 1) (i j : Fin 3) (hij : i ≠ j) :
    radii x i + radii x j ≤ 1 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({i,j} : Finset (Fin 3))) (t := Finset.univ)
    (by intro k _; exact Finset.mem_univ k)
    (fun k _ _ => radii_nonneg x k)
  simpa [Finset.sum_pair hij, sum_radii, hx] using h

lemma radii_pair_quarter (x : RealFields K) (hx : mass x = 1) (i j : Fin 3) (hij : i ≠ j) :
    radii x i*radii x j ≤ (1:K)/4 := by
  have hi := radii_nonneg x i
  have hj := radii_nonneg x j
  have hs := radii_pair_sum_le x hx i j hij
  have hsq : (radii x i+radii x j)^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (radii x i-radii x j)]

/-- Real-coordinate form of the complex Lagrange identity. -/
lemma off_cauchy (a b c d e f g h : K) :
    (a*c+b*d+e*g+f*h)^2+(a*d-b*c+e*h-f*g)^2 ≤
      (a^2+b^2+e^2+f^2)*(c^2+d^2+g^2+h^2) := by
  nlinarith only [sq_nonneg (a*g-b*h-e*c+f*d), sq_nonneg (a*h+b*g-e*d-f*c)]

lemma off_norm_le_quarter (x : RealFields K) (hx : mass x = 1) (i : Fin 3) :
    offRe x i^2+offIm x i^2 ≤ (1:K)/4 := by
  fin_cases i
  · exact (off_cauchy (x 0) (x 1) (x 2) (x 3) (x 6) (x 7) (x 8) (x 9)).trans
      (radii_pair_quarter x hx 0 1 (by decide))
  · exact (off_cauchy (x 0) (x 1) (x 4) (x 5) (x 6) (x 7) (x 10) (x 11)).trans
      (radii_pair_quarter x hx 0 2 (by decide))
  · exact (off_cauchy (x 2) (x 3) (x 4) (x 5) (x 8) (x 9) (x 10) (x 11)).trans
      (radii_pair_quarter x hx 1 2 (by decide))

lemma diagonal_monomial_bound (x : RealFields K) (hx : mass x = 1) (i : Fin 3) :
    |radii x i^2/2| ≤ (1:K)/2 := by
  have hi := radii_nonneg x i
  have hu := radii_le_one x hx i
  rw [abs_of_nonneg (by positivity)]
  nlinarith

lemma pair_monomial_bound (x : RealFields K) (hx : mass x = 1) (i j : Fin 3) (hij : i ≠ j) :
    |radii x i*radii x j| ≤ (1:K)/4 := by
  rw [abs_of_nonneg (mul_nonneg (radii_nonneg x i) (radii_nonneg x j))]
  exact radii_pair_quarter x hx i j hij

lemma norm_monomial_bound (x : RealFields K) (hx : mass x = 1) (i : Fin 3) :
    |offRe x i^2+offIm x i^2| ≤ (1:K)/4 := by
  rw [abs_of_nonneg (by positivity)]
  exact off_norm_le_quarter x hx i

lemma real_monomial_bound (x : RealFields K) (hx : mass x = 1) (i : Fin 3) :
    |offRe x i^2-offIm x i^2| ≤ (1:K)/4 := by
  rw [abs_le]
  have h := off_norm_le_quarter x hx i
  constructor <;> nlinarith [sq_nonneg (offRe x i), sq_nonneg (offIm x i)]

lemma imag_monomial_bound (x : RealFields K) (hx : mass x = 1) (i : Fin 3) :
    |-2*offRe x i*offIm x i| ≤ (1:K)/4 := by
  rw [abs_le]
  have h := off_norm_le_quarter x hx i
  constructor <;> nlinarith [sq_nonneg (offRe x i-offIm x i), sq_nonneg (offRe x i+offIm x i)]

/-- Exactly the three one-half and twelve one-quarter bounds in the source. -/
theorem monomials_bound (x : RealFields K) (hx : mass x = 1) (i : Fin 15) :
    |monomials x i| ≤ W3.Infinitesimal.monomialBound i := by
  fin_cases i <;> simp only [monomials, W3.Infinitesimal.monomialBound, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.reduceLT, if_true, if_false]
  · exact diagonal_monomial_bound x hx 0
  · exact diagonal_monomial_bound x hx 1
  · exact diagonal_monomial_bound x hx 2
  · exact pair_monomial_bound x hx 0 1 (by decide)
  · exact pair_monomial_bound x hx 0 2 (by decide)
  · exact pair_monomial_bound x hx 1 2 (by decide)
  · exact norm_monomial_bound x hx 0
  · exact norm_monomial_bound x hx 1
  · exact norm_monomial_bound x hx 2
  · exact real_monomial_bound x hx 0
  · exact imag_monomial_bound x hx 0
  · exact real_monomial_bound x hx 1
  · exact imag_monomial_bound x hx 1
  · exact real_monomial_bound x hx 2
  · exact imag_monomial_bound x hx 2

/-- Coefficient-level equality with the original trace-square plus fifteen-monomial deformation. -/
theorem quarticReal_deformed (κ : Parameters K) (e0 : K) (e : Fin 15 → K) (x : RealFields K) :
    quarticReal (deformedParameters κ e0 e) x = quarticReal κ x +
      e0*(mass x)^2 + ∑ i, e i*monomials x i := by
  rw [← sum_radii]
  simp [quarticReal, twiceQuartic, deformedParameters, monomials, Fin.sum_univ_succ]
  ring

#print axioms monomials_bound
#print axioms quarticReal_deformed
end W3.RealModel
