import W3.InfinitesimalTranslation
import Mathlib.Data.Fin.Rev

/-! # Chronological epsilons and their strict hierarchy in the final field. -/
noncomputable section
namespace W3.Infinitesimal

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

theorem orderedFieldHom_strictMono (ι : K →+*o L) : StrictMono ι := by
  intro x y h
  exact lt_of_le_of_ne (ι.monotone' h.le) (fun he => h.ne (ι.toRingHom.injective he))

theorem towerCoordinates_infinitesimal (M : OrderedFieldModel) (n : ℕ) :
    ∀ i : Fin n, PositiveInfinitesimal (baseEmbed M n) (towerCoordinates M n i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    cases i using Fin.cases with
    | zero =>
      rw [towerCoordinates_zero]
      refine ⟨epsilon_pos (Tower M n), ?_⟩
      intro r hr
      have hpos : 0 < baseEmbed M n r := by
        have h := orderedFieldHom_strictMono (baseEmbed M n) hr
        simpa only [map_zero] using h
      exact epsilon_lt_embed (Tower M n) hpos
    | succ i =>
      rw [towerCoordinates_succ]
      refine ⟨?_, ?_⟩
      · have h := orderedFieldHom_strictMono (stepEmbed M n) (ih i).1
        simpa only [map_zero] using h
      · intro r hr
        exact orderedFieldHom_strictMono (stepEmbed M n) ((ih i).2 r hr)

/-- Multiplying any later infinitesimal by any positive original-base constant
still leaves it strictly below every earlier infinitesimal. -/
theorem towerCoordinates_scaled_lt (M : OrderedFieldModel) (n : ℕ) :
    ∀ (i j : Fin n), i < j → ∀ C : M.Carrier, 0 < C →
      baseEmbed M n C * towerCoordinates M n i < towerCoordinates M n j := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i j hij C hC
    have hpos : 0 < baseEmbed M n C := by
      have h := orderedFieldHom_strictMono (baseEmbed M n) hC
      simpa only [map_zero] using h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        rw [towerCoordinates_zero, towerCoordinates_succ]
        have he := epsilon_lt_embed (Tower M n)
          (div_pos (towerCoordinates_infinitesimal M n j).1 hpos)
        rw [map_div₀] at he
        have hpos' : 0 < embed (Tower M n) (baseEmbed M n C) := by
          simpa only [map_zero] using (embed_lt_iff (Tower M n)).mpr hpos
        have h := (lt_div_iff₀ hpos').mp he
        change embed (Tower M n) (baseEmbed M n C) * epsilon (Tower M n) <
          embed (Tower M n) (towerCoordinates M n j)
        simpa only [mul_comm] using h
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero i.succ hij).elim
      | succ j =>
        have h := ih i j (Fin.succ_lt_succ_iff.mp hij) C hC
        have hh := orderedFieldHom_strictMono (stepEmbed M n) h
        rw [towerCoordinates_succ, towerCoordinates_succ]
        change stepEmbed M n (baseEmbed M n C) * stepEmbed M n (towerCoordinates M n i) <
          stepEmbed M n (towerCoordinates M n j)
        simpa only [map_mul] using hh

/-- Source chronology: index 0 is dominant, index 15 is newest and smallest. -/
def chronologicalEpsilon (i : Fin 16) : SixteenLevelField :=
  towerCoordinates realModel 16 i.rev

theorem chronologicalEpsilon_infinitesimal (i : Fin 16) :
    PositiveInfinitesimal realEmbedding16 (chronologicalEpsilon i) :=
  towerCoordinates_infinitesimal realModel 16 i.rev

theorem chronologicalEpsilon_algebraicIndependent :
    letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
    AlgebraicIndependent ℝ chronologicalEpsilon := by
  letI : Algebra ℝ SixteenLevelField := towerAlgebra realModel 16
  exact sixteen_algebraicIndependent.comp Fin.rev Fin.rev_injective

/-- The exact numerical domination required by equation (40), in the actual final field. -/
theorem nine_halves_epsilon_one_lt_zero :
    (9 / 2 : SixteenLevelField) * chronologicalEpsilon 1 < chronologicalEpsilon 0 := by
  have h := towerCoordinates_scaled_lt realModel 16 (1 : Fin 16).rev (0 : Fin 16).rev
    (by decide) (9 / 2) (by norm_num)
  simpa only [chronologicalEpsilon, map_div₀, map_ofNat] using h

#print axioms chronologicalEpsilon_algebraicIndependent
#print axioms nine_halves_epsilon_one_lt_zero
end W3.Infinitesimal
