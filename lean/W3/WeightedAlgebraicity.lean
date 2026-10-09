import W3.WeightedExact
import Mathlib.RingTheory.Algebraic.Integral

/-! Algebraicity of the actual selected-root construction over a coefficient
field F, including a rational-function base embedded in the ordered field L. -/
noncomputable section
namespace W3.Weighted
open W3.Elimination Polynomial
section Algebraic
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

lemma algebraic_div {x y : L} (hx : IsAlgebraic F x) (hy : IsAlgebraic F y) :
    IsAlgebraic F (x/y) := by
  rw [div_eq_mul_inv]
  exact hx.mul hy.inv

lemma algebraic_eval₂ {x : L} (hx : IsAlgebraic F x) (p : F[X]) :
    IsAlgebraic F (p.eval₂ (algebraMap F L) x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact hp.add hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact (isAlgebraic_algebraMap a).mul (hx.pow n)

variable [LinearOrder L] [IsStrictOrderedRing L]

/-- Nonzero mapped sextic roots are algebraic over the genuine coefficient
field; the theorem does not silently enlarge that field to the ambient L. -/
theorem selected_phase_algebraic (p q : PhaseRow F) (t u : L)
    (hS : phaseSextic p q ≠ 0)
    (hm : (t,u) ∈ phaseCandidates (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)) :
    IsAlgebraic F t ∧ IsAlgebraic F u := by
  classical
  unfold phaseCandidates at hm
  obtain ⟨v,hroot,heq⟩ := Finset.mem_image.mp hm
  have hvt : v = t := congrArg Prod.fst heq
  subst v
  have hroot' : ((phaseSextic p q).map (algebraMap F L)).eval t = 0 := by
    rw [map_phaseSextic]
    exact (mem_roots (by rw [← map_phaseSextic]; exact (Polynomial.map_ne_zero_iff (RingHom.injective _)).mpr hS)).mp
      (Multiset.mem_toFinset.mp hroot)
  have ht : IsAlgebraic F t := ⟨phaseSextic p q,hS,by simpa only [Polynomial.aeval_def,Polynomial.eval_map] using hroot'⟩
  have hu := (congrArg Prod.snd heq).symm
  change u = -(phaseLinearZero (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)).eval t /
    (phaseLinearOne (mapRow (algebraMap F L) p) (mapRow (algebraMap F L) q)).eval t at hu
  rw [hu,← map_phaseLinearZero,← map_phaseLinearOne,Polynomial.eval_map,Polynomial.eval_map]
  exact ⟨ht,algebraic_div (algebraic_eval₂ ht _).neg (algebraic_eval₂ ht _)⟩


def AlgebraicPair (F : Type*) [Field F] [Algebra F L] (z : ComplexPair L) : Prop :=
  IsAlgebraic F z.re ∧ IsAlgebraic F z.im

def AlgebraicPoint (F : Type*) [Field F] [Algebra F L] (x : SpectrumPoint L) : Prop :=
  IsAlgebraic F x.r₁ ∧ IsAlgebraic F x.r₂ ∧ IsAlgebraic F x.r₃ ∧
  AlgebraicPair F x.q ∧ AlgebraicPair F x.v

lemma algebraicPair_mul {z w : ComplexPair L} (hz : AlgebraicPair F z) (hw : AlgebraicPair F w) :
    AlgebraicPair F (ComplexPair.mul z w) :=
  ⟨(hz.1.mul hw.1).sub (hz.2.mul hw.2),(hz.1.mul hw.2).add (hz.2.mul hw.1)⟩
lemma algebraicPair_conj {z : ComplexPair L} (hz : AlgebraicPair F z) :
    AlgebraicPair F (ComplexPair.conj z) := ⟨hz.1,hz.2.neg⟩
lemma algebraicPair_scale {a : L} {z : ComplexPair L} (ha : IsAlgebraic F a) (hz : AlgebraicPair F z) :
    AlgebraicPair F (ComplexPair.scale a z) := ⟨ha.mul hz.1,ha.mul hz.2⟩
lemma algebraic_onePhase : AlgebraicPair F (onePhase : ComplexPair L) :=
  ⟨isAlgebraic_one,isAlgebraic_zero⟩

lemma algebraic_circlePoint {x y : L} (hx : IsAlgebraic F x) (hy : IsAlgebraic F y) :
    AlgebraicPair F (circlePoint x y) := by
  have hd := (hx.pow 2).add (hy.pow 2)
  exact ⟨algebraic_div ((hx.pow 2).sub (hy.pow 2)) hd,
    algebraic_div (((isAlgebraic_natCast 2).mul hx).mul hy) hd⟩

/-- All rational full-support reconstruction coordinates are algebraic over
F once the selected sextic/root-recovery coordinates are algebraic over F. -/
theorem fullPoint_algebraic (w : WeightedData F) (t u : L)
    (ht : IsAlgebraic F t) (hu : IsAlgebraic F u) :
    AlgebraicPoint F (fullPoint (mapWeighted (algebraMap F L) w) t u) := by
  have hq := algebraic_circlePoint (isAlgebraic_one (R:=F) (A:=L)) ht
  have hv := algebraic_circlePoint (isAlgebraic_one (R:=F) (A:=L)) hu
  have hd₁₂ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₂ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have hd₁₃ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₁₃ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have hd₂₃ : AlgebraicPair F (toSpectrum (mapWeighted (algebraMap F L) w)).d₂₃ :=
    ⟨isAlgebraic_algebraMap _,isAlgebraic_algebraMap _⟩
  have hs₁₂ := (algebraicPair_mul hd₁₂ hq).2
  have hs₁₃ := (algebraicPair_mul hd₁₃ hv).2
  have hs₂₃ := (algebraicPair_mul hd₂₃ (algebraicPair_mul hv (algebraicPair_conj hq))).2
  have hD := (hs₂₃.sub hs₁₃).add hs₁₂
  exact ⟨algebraic_div hs₂₃ hD,algebraic_div hs₁₃.neg hD,algebraic_div hs₁₂ hD,hq,hv⟩

/-- Direct actual-list version: sextic membership supplies both root algebraicity
hypotheses, including the recovered second coordinate. -/
theorem selected_fullPoint_algebraic (w : WeightedData F) (t u : L)
    (hS : phaseSextic (weightedP w) (weightedQ w) ≠ 0)
    (hm : (t,u) ∈ phaseCandidates (weightedP (mapWeighted (algebraMap F L) w))
      (weightedQ (mapWeighted (algebraMap F L) w))) :
    AlgebraicPoint F (fullPoint (mapWeighted (algebraMap F L) w) t u) := by
  rw [← map_weightedP,← map_weightedQ] at hm
  obtain ⟨ht,hu⟩ := selected_phase_algebraic (weightedP w) (weightedQ w) t u hS hm
  exact fullPoint_algebraic w t u ht hu

end Algebraic
end W3.Weighted
