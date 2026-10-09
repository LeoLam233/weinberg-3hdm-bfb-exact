import W3.WeightedAlgebra

noncomputable section
namespace W3.Weighted
open ComplexPair
open W3.Elimination

/-- Data of the common weighted problem, in exact real coordinates. -/
structure SpectrumData (K : Type*) where
  a₁ : K
  a₂ : K
  a₃ : K
  e₁₂ : K
  e₁₃ : K
  e₂₃ : K
  d₁₂ : ComplexPair K
  d₁₃ : ComplexPair K
  d₂₃ : ComplexPair K

section Ring
variable {K : Type*} [CommRing K]

def complexRow (A B C : ComplexPair K) : PhaseRow K :=
  ⟨A.re, A.im, B.re, B.im, C.re, C.im⟩

def rowImag (p : PhaseRow K) (q v : ComplexPair K) : K :=
  p.ar * q.im + p.ai * q.re + p.br * v.im + p.bi * v.re +
  p.cr * (mul v (conj q)).im + p.ci * (mul v (conj q)).re

/-- The three exact rows of C, equation (12). -/
def cRow₁ (k : SpectrumData K) : PhaseRow K :=
  complexRow (scale k.e₁₃ k.d₁₂) (scale (-k.e₁₂) k.d₁₃)
    (sub (scale k.a₁ k.d₂₃) (mul k.d₁₃ (conj k.d₁₂)))
def cRow₂ (k : SpectrumData K) : PhaseRow K :=
  complexRow (scale k.e₂₃ k.d₁₂) (sub (mul k.d₁₂ k.d₂₃) (scale k.a₂ k.d₁₃))
    (scale k.e₁₂ k.d₂₃)
def cRow₃ (k : SpectrumData K) : PhaseRow K :=
  complexRow (sub (scale k.a₃ k.d₁₂) (mul k.d₁₃ (conj k.d₂₃)))
    (scale (-k.e₂₃) k.d₁₃) (scale k.e₁₃ k.d₂₃)

def edge₁₂ (k : SpectrumData K) (q : ComplexPair K) := mul k.d₁₂ q
def edge₁₃ (k : SpectrumData K) (v : ComplexPair K) := mul k.d₁₃ v
def edge₂₃ (k : SpectrumData K) (q v : ComplexPair K) := mul k.d₂₃ (mul v (conj q))

/-- Coordinate actions of 2B(q), avoiding any characteristic assumption. -/
def twiceB₁ (k : SpectrumData K) (q v : ComplexPair K) (x y z : K) : K :=
  k.a₁ * x + (k.e₁₂ + (edge₁₂ k q).re) * y + (k.e₁₃ + (edge₁₃ k v).re) * z
def twiceB₂ (k : SpectrumData K) (q v : ComplexPair K) (x y z : K) : K :=
  (k.e₁₂ + (edge₁₂ k q).re) * x + k.a₂ * y + (k.e₂₃ + (edge₂₃ k q v).re) * z
def twiceB₃ (k : SpectrumData K) (q v : ComplexPair K) (x y z : K) : K :=
  (k.e₁₃ + (edge₁₃ k v).re) * x + (k.e₂₃ + (edge₂₃ k q v).re) * y + k.a₃ * z

/-- First component of the exact identity 2Bj=Im(Cz). -/
theorem current_matrix_identity₁ (k : SpectrumData K) (q v : ComplexPair K) :
    twiceB₁ k q v (edge₂₃ k q v).im (-(edge₁₃ k v).im) (edge₁₂ k q).im =
      rowImag (cRow₁ k) q v := by
  simp only [twiceB₁, edge₁₂, edge₁₃, edge₂₃, rowImag, cRow₁,
    complexRow, scale, sub, mul, conj]
  ring

/-- The only extra term in component two is exactly the first circle relation. -/
theorem current_matrix_identity₂ (k : SpectrumData K) (q v : ComplexPair K)
    (hq : normSq q = 1) :
    twiceB₂ k q v (edge₂₃ k q v).im (-(edge₁₃ k v).im) (edge₁₂ k q).im =
      rowImag (cRow₂ k) q v := by
  simp only [twiceB₂, edge₁₂, edge₁₃, edge₂₃, rowImag, cRow₂,
    complexRow, scale, sub, mul, conj]
  simp only [normSq] at hq
  linear_combination ((k.d₁₂.re * k.d₂₃.im + k.d₁₂.im * k.d₂₃.re) * v.re +
    (k.d₁₂.re * k.d₂₃.re - k.d₁₂.im * k.d₂₃.im) * v.im) * hq

/-- The only extra term in component three is exactly the second circle relation. -/
theorem current_matrix_identity₃ (k : SpectrumData K) (q v : ComplexPair K)
    (hv : normSq v = 1) :
    twiceB₃ k q v (edge₂₃ k q v).im (-(edge₁₃ k v).im) (edge₁₂ k q).im =
      rowImag (cRow₃ k) q v := by
  simp only [twiceB₃, edge₁₂, edge₁₃, edge₂₃, rowImag, cRow₃,
    complexRow, scale, sub, mul, conj]
  simp only [normSq] at hv
  linear_combination -((k.d₁₃.im * k.d₂₃.re - k.d₁₃.re * k.d₂₃.im) * q.re +
    (k.d₁₃.re * k.d₂₃.re + k.d₁₃.im * k.d₂₃.im) * q.im) * hv

/-- Weighted row difference, equation (14). -/
def rowDifference (g₁ gᵢ : K) (p q : PhaseRow K) : PhaseRow K :=
  ⟨g₁ * q.ar - gᵢ * p.ar, g₁ * q.ai - gᵢ * p.ai,
   g₁ * q.br - gᵢ * p.br, g₁ * q.bi - gᵢ * p.bi,
   g₁ * q.cr - gᵢ * p.cr, g₁ * q.ci - gᵢ * p.ci⟩

theorem rowDifference_imag (g₁ gᵢ : K) (p q : PhaseRow K) (u v : ComplexPair K) :
    rowImag (rowDifference g₁ gᵢ p q) u v =
      g₁ * rowImag q u v - gᵢ * rowImag p u v := by
  unfold rowImag rowDifference
  ring

end Ring
end W3.Weighted
