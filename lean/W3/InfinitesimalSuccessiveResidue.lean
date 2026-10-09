import W3.InfinitesimalRationalTower
import W3.InfinitesimalResidue

/-! # A finite successive residue chain with a descending algebraic presentation -/
noncomputable section
namespace W3.Infinitesimal
set_option backward.isDefEq.respectTransparency false

/-- Exactly n preceding-field residue operations, ending in the original real field. -/
def SuccessiveResidue : (n : ℕ) → Tower realModel n → ℝ → Prop
  | 0, x, r => x = r
  | n + 1, x, r => ∃ q : Tower realModel n,
      HasRelativeResidue (Tower realModel n) x q ∧ SuccessiveResidue n q r

/-- The root chosen at each level remains in the same original real interval,
and algebraicity descends in the explicit rational presentation. -/
theorem successiveResidue_exists (n : ℕ) {x : Tower realModel n} {a b : ℝ}
    (ha : baseEmbed realModel n a ≤ x) (hb : x ≤ baseEmbed realModel n b)
    (halg : letI := rationalTowerAlgebra n; IsAlgebraic (RationalTower n) x) :
    ∃ r : ℝ, a ≤ r ∧ r ≤ b ∧ SuccessiveResidue n x r := by
  induction n with
  | zero => exact ⟨x, ha, hb, rfl⟩
  | succ n ih =>
    change Extension (Tower realModel n) at x
    have hx : BaseBounded (Tower realModel n) x := by
      refine ⟨baseEmbed realModel n ((|a| + |b| + 1) : ℝ), ?_, ?_⟩
      · have h : 0 < (|a| + |b| + 1 : ℝ) := by positivity
        simpa only [map_zero] using (orderedFieldHom_strictMono (baseEmbed realModel n)) h
      · apply abs_le.mpr
        constructor
        · have hr : -(|a| + |b| + 1) ≤ a := by linarith [neg_abs_le a, abs_nonneg b]
          have h : baseEmbed realModel (n + 1) (-(|a| + |b| + 1) : ℝ) ≤
              baseEmbed realModel (n + 1) a := (baseEmbed realModel (n + 1)).monotone' hr
          rw [map_neg] at h
          exact h.trans ha
        · have hr : b ≤ |a| + |b| + 1 := by linarith [le_abs_self b, abs_nonneg a]
          exact hb.trans ((baseEmbed realModel (n + 1)).monotone' hr)
    obtain ⟨q, hq, hqa⟩ := rationalTower_residue_step n hx halg
    have hbnds := relativeResidue_interval (Tower realModel n) hq ha hb
    obtain ⟨r, har, hrb, hchain⟩ := ih hbnds.1 hbnds.2 hqa
    exact ⟨r, har, hrb, q, hq, hchain⟩

theorem successiveResidue_unique (n : ℕ) {x : Tower realModel n} {r s : ℝ}
    (hr : SuccessiveResidue n x r) (hs : SuccessiveResidue n x s) : r = s := by
  induction n with
  | zero => exact hr.symm.trans hs
  | succ n ih =>
    obtain ⟨q, hq, hr⟩ := hr
    obtain ⟨p, hp, hs⟩ := hs
    have heq := relativeResidue_unique (Tower realModel n) hq hp
    subst p
    exact ih hr hs

/-- A successive residue differs from the original element by less than every
positive real tolerance, interpreted in the full tower. -/
theorem successiveResidue_real_close (n : ℕ) {x : Tower realModel n} {r : ℝ}
    (hr : SuccessiveResidue n x r) :
    ∀ δ : ℝ, 0 < δ → |x - baseEmbed realModel n r| < baseEmbed realModel n δ := by
  induction n with
  | zero =>
    intro δ hδ
    change x = r at hr
    subst x
    change |r - r| < δ
    simpa only [sub_self, abs_zero] using hδ
  | succ n ih =>
    change Extension (Tower realModel n) at x
    obtain ⟨q, hq, hchain⟩ := hr
    intro δ hδ
    have hhalf : 0 < δ / 2 := by positivity
    have hhalf' : 0 < baseEmbed realModel n ((δ / 2) : ℝ) := by
      simpa only [map_zero] using (orderedFieldHom_strictMono (baseEmbed realModel n)) hhalf
    have h1 := hq (baseEmbed realModel n ((δ / 2) : ℝ)) hhalf'
    have h2 := (orderedFieldHom_strictMono (embed (Tower realModel n))) (ih hchain (δ / 2) hhalf)
    rw [embed_abs, map_sub] at h2
    have htri := abs_add_le (x - embed (Tower realModel n) q)
      (embed (Tower realModel n) q - embed (Tower realModel n) (baseEmbed realModel n r))
    have hsum := htri.trans_lt (add_lt_add h1 h2)
    have hs : baseEmbed realModel n ((δ / 2) : ℝ) + baseEmbed realModel n ((δ / 2) : ℝ) =
        baseEmbed realModel n δ := by rw [← map_add]; congr 1; ring
    rw [← map_add, hs] at hsum
    change |x - embed (Tower realModel n) (baseEmbed realModel n r)| <
      embed (Tower realModel n) (baseEmbed realModel n δ)
    simpa only [sub_add_sub_cancel] using hsum

/-- The finite successive extraction agrees with the independently constructed
real residue map, so previously established physical residue identities apply. -/
theorem successiveResidue_eq_stdPart (n : ℕ) {x : Tower realModel n} {r : ℝ}
    (hr : SuccessiveResidue n x r) : ArchimedeanClass.stdPart x = r := by
  apply ArchimedeanClass.stdPart_eq (baseEmbed realModel n)
  · intro s hs
    have h := successiveResidue_real_close n hr (r - s) (sub_pos.mpr hs)
    rw [map_sub] at h
    have hl := (abs_lt.mp h).1
    change baseEmbed realModel n s ≤ x
    linarith
  · intro s hs
    have h := successiveResidue_real_close n hr (s - r) (sub_pos.mpr hs)
    rw [map_sub] at h
    have hu := (abs_lt.mp h).2
    change x ≤ baseEmbed realModel n s
    linarith

/-- Unique finite successive residue exists for every bounded algebraic presentation. -/
theorem sixteen_successiveResidue_exists_unique {x : SixteenLevelField} {a b : ℝ}
    (ha : realEmbedding16 a ≤ x) (hb : x ≤ realEmbedding16 b)
    (halg : letI := rationalTowerAlgebra 16; IsAlgebraic (RationalTower 16) x) :
    ∃! r : ℝ, SuccessiveResidue 16 x r := by
  obtain ⟨r, _, _, hr⟩ := successiveResidue_exists 16 ha hb halg
  exact ⟨r, hr, fun s hs => successiveResidue_unique 16 hs hr⟩

#print axioms successiveResidue_exists
#print axioms successiveResidue_real_close
#print axioms successiveResidue_eq_stdPart
end W3.Infinitesimal
