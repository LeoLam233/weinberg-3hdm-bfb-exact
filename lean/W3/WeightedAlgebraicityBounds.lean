import W3.WeightedAlgebraicitySelected

/-! Uniform coordinate bounds for the algebraic projectors selected above.
Half-angle parameters need not be bounded; the actual physical coordinates are. -/
noncomputable section
namespace W3.Weighted
open ComplexPair
section Ordered
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def UnitBoundedPair (z : ComplexPair K) : Prop := |z.re| ≤ 1 ∧ |z.im| ≤ 1

lemma pair_coordinates_bounded_of_norm (z : ComplexPair K) (hn : normSq z ≤ 1) : UnitBoundedPair z := by
  have hr : z.re ^ 2 ≤ 1 := by unfold normSq at hn; nlinarith [sq_nonneg z.im]
  have hi : z.im ^ 2 ≤ 1 := by unfold normSq at hn; nlinarith [sq_nonneg z.re]
  constructor <;> apply abs_le.mpr
  · constructor <;> nlinarith [sq_nonneg (z.re - 1),sq_nonneg (z.re + 1)]
  · constructor <;> nlinarith [sq_nonneg (z.im - 1),sq_nonneg (z.im + 1)]

/-- Normalized rank-one projectors have all nine real coordinates bounded by
one in every ordered field, including every level of the infinitesimal tower. -/
theorem normalized_projector_bounds (z₁ z₂ z₃ : ComplexPair K)
    (hn : normSq z₁+normSq z₂+normSq z₃=1) :
    |normSq z₁| ≤ 1 ∧ |normSq z₂| ≤ 1 ∧ |normSq z₃| ≤ 1 ∧
    UnitBoundedPair (mul z₁ (conj z₂)) ∧ UnitBoundedPair (mul z₁ (conj z₃)) ∧
    UnitBoundedPair (mul z₂ (conj z₃)) := by
  have h₁ : 0 ≤ normSq z₁ := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h₂ : 0 ≤ normSq z₂ := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have h₃ : 0 ≤ normSq z₃ := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb₁ : normSq z₁ ≤ 1 := by linarith
  have hb₂ : normSq z₂ ≤ 1 := by linarith
  have hb₃ : normSq z₃ ≤ 1 := by linarith
  have finish (z w : ComplexPair K) (hz : 0 ≤ normSq z) (hw : 0 ≤ normSq w)
      (hz1 : normSq z ≤ 1) (hw1 : normSq w ≤ 1) : UnitBoundedPair (mul z (conj w)) := by
    apply pair_coordinates_bounded_of_norm
    rw [complex_norm_mul,complexPair_norm_conj]
    exact (mul_le_mul_of_nonneg_right hz1 hw).trans (by simpa using hw1)
  exact ⟨by rwa [abs_of_nonneg h₁],by rwa [abs_of_nonneg h₂],by rwa [abs_of_nonneg h₃],
    finish _ _ h₁ h₂ hb₁ hb₂,finish _ _ h₁ h₃ hb₁ hb₃,finish _ _ h₂ h₃ hb₂ hb₃⟩

end Ordered
end W3.Weighted
