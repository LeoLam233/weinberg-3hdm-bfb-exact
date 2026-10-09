import W3.StrataTransferFormula
import W3.StrataTransferReal
import W3.InfinitesimalRealBase

/-! Actual transfer of the proved stationary-stratum theorem to every level of
the concrete ultrapower tower. No transfer, encoding, or coverage premise is assumed. -/
noncomputable section
namespace W3.StrataTransfer
open W3.RealModel W3.Infinitesimal

/-- The fully specified first-order formula is a theorem of the real base field. -/
theorem real_stationaryStrataFormula (v : Fin 27 → ℝ) : stationaryStrataFormula.Realize v := by
  apply (stationaryStrataFormula_realize v).mpr
  rintro ⟨hm,hmin⟩
  exact real_minimum_strata (parameters27 v) (fields27 v) hm hmin

/-- The formula holds for arbitrary extension-valued couplings and fields,
not merely images of real parameters. -/
theorem tower_stationaryStrataFormula (n : ℕ) (v : Fin 27 → Tower realModel n) :
    stationaryStrataFormula.Realize v :=
  orderedPolynomialFormula_universal_tower realModel n stationaryStrataFormula real_stationaryStrataFormula v

/-- An actual universal physical minimum in any tower stage has one of the
explicit neutral/charged polynomial stationary forms. -/
theorem tower_minimum_stationary_strata (n : ℕ)
    (k : Parameters (Tower realModel n)) (x : RealFields (Tower realModel n))
    (hm : mass x=1)
    (hmin : ∀ y : RealFields (Tower realModel n),mass y=1→twiceQuartic k x≤twiceQuartic k y) :
    StrataConclusion k x := by
  have h := (stationaryStrataFormula_realize (Fin.append k x)).mp
    (tower_stationaryStrataFormula n (Fin.append k x))
  have hk : parameters27 (Fin.append k x)=k := by funext i; simp [parameters27]
  have hx : fields27 (Fin.append k x)=x := by funext i; simp [fields27]
  rw [hk,hx] at h
  exact h ⟨hm,hmin⟩

/-- The requested sixteen-level nonarchimedean stationary-stratum theorem. -/
theorem sixteen_minimum_stationary_strata
    (k : Parameters SixteenLevelField) (x : RealFields SixteenLevelField)
    (hm : mass x=1)
    (hmin : ∀ y : RealFields SixteenLevelField,mass y=1→twiceQuartic k x≤twiceQuartic k y) :
    StrataConclusion k x :=
  tower_minimum_stationary_strata 16 k x hm hmin

#print axioms real_minimum_strata
#print axioms stationaryStrataFormula_realize
#print axioms tower_minimum_stationary_strata
#print axioms sixteen_minimum_stationary_strata
end W3.StrataTransfer
