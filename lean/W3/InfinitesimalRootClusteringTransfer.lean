import W3.InfinitesimalRootClustering
import W3.InfinitesimalFormulaTransfer

/-! # Explicit bounded-degree root-clustering formula and transfer to every tower stage. -/
noncomputable section
namespace W3.Infinitesimal
open scoped BigOperators
open Polynomial

/-- A coefficient-vector presentation of an arbitrary polynomial of bounded degree. -/
def coefficientValue {A : Type*} [CommRing A] {N : ℕ} (c : Fin N → A) (y : A) : A :=
  ∑ i : Fin N, c i * y ^ i.val

lemma intPolynomialEval_coefficientValue {A : Type*} [CommRing A] {N n : ℕ}
    (c : Fin N → MvPolynomial (Fin n) ℤ) (y : MvPolynomial (Fin n) ℤ) (v : Fin n → A) :
    intPolynomialEval (coefficientValue c y) v =
      coefficientValue (fun i => intPolynomialEval (c i) v) (intPolynomialEval y v) := by
  simp only [intPolynomialEval, coefficientValue, map_sum, map_mul, map_pow]

def polynomialLe {n : ℕ} (p q : MvPolynomial (Fin n) ℤ) : OrderedPolynomialFormula n :=
  .nonneg (q - p)

def polynomialLt {n : ℕ} (p q : MvPolynomial (Fin n) ℤ) : OrderedPolynomialFormula n :=
  .neg (.nonneg (p - q))

@[simp] lemma realize_polynomialLe {A : Type*} [CommRing A] [LinearOrder A]
    [IsStrictOrderedRing A] {n : ℕ} (p q : MvPolynomial (Fin n) ℤ) (v : Fin n → A) :
    (polynomialLe p q).Realize v ↔ intPolynomialEval p v ≤ intPolynomialEval q v := by
  simp only [polynomialLe, OrderedPolynomialFormula.Realize, intPolynomialEval,
    map_sub, sub_nonneg]

@[simp] lemma realize_polynomialLt {A : Type*} [CommRing A] [LinearOrder A]
    [IsStrictOrderedRing A] {n : ℕ} (p q : MvPolynomial (Fin n) ℤ) (v : Fin n → A) :
    (polynomialLt p q).Realize v ↔ intPolynomialEval p v < intPolynomialEval q v := by
  simp only [polynomialLt, OrderedPolynomialFormula.Realize, intPolynomialEval,
    map_sub, not_le, sub_lt_zero]

/-- Free variables: B,delta, then N coefficients. Quantified variables are eta,y,q.
The syntax contains no topology, polynomial root oracle or transfer premise. -/
def rootClusteringFormula (N : ℕ) : OrderedPolynomialFormula (N + 2) :=
  .implies (polynomialLt 0 (MvPolynomial.X (Fin.succ 0)))
    (.ex (.conj (polynomialLt 0 (MvPolynomial.X 0))
      (.all (.implies
        (.conj (polynomialLe (-MvPolynomial.X (Fin.succ (Fin.succ 0))) (MvPolynomial.X 0))
          (.conj (polynomialLe (MvPolynomial.X 0) (MvPolynomial.X (Fin.succ (Fin.succ 0))))
            (.conj
              (polynomialLt (-MvPolynomial.X (Fin.succ 0))
                (coefficientValue (fun i : Fin N => MvPolynomial.X i.succ.succ.succ.succ)
                  (MvPolynomial.X 0)))
              (polynomialLt
                (coefficientValue (fun i : Fin N => MvPolynomial.X i.succ.succ.succ.succ)
                  (MvPolynomial.X 0)) (MvPolynomial.X (Fin.succ 0))))))
        (.ex (.conj
          (.eqZero (coefficientValue
            (fun i : Fin N => MvPolynomial.X i.succ.succ.succ.succ.succ) (MvPolynomial.X 0)))
          (.conj
            (polynomialLt (-MvPolynomial.X (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) (MvPolynomial.X (Fin.succ 0) - MvPolynomial.X 0))
            (polynomialLt (MvPolynomial.X (Fin.succ 0) - MvPolynomial.X 0) (MvPolynomial.X (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))))))))))))

lemma rootClusteringFormula_realize {A : Type*} [CommRing A] [LinearOrder A]
    [IsStrictOrderedRing A] {N : ℕ} (c : Fin N → A) (B δ : A) :
    (rootClusteringFormula N).Realize (Fin.cons B (Fin.cons δ c)) ↔
      (0 < δ → ∃ η : A, 0 < η ∧ ∀ y : A,
        (-B ≤ y ∧ y ≤ B ∧ -η < coefficientValue c y ∧ coefficientValue c y < η) →
        ∃ q : A, coefficientValue c q = 0 ∧ -δ < y - q ∧ y - q < δ) := by
  simp only [rootClusteringFormula, OrderedPolynomialFormula.realize_implies,
    OrderedPolynomialFormula.realize_all, OrderedPolynomialFormula.Realize,
    realize_polynomialLt, realize_polynomialLe, intPolynomialEval_coefficientValue]
  simp only [intPolynomialEval, MvPolynomial.eval₂Hom_X', map_zero, map_neg, map_sub,
    Fin.cons_zero, Fin.cons_succ]

theorem real_rootClusteringFormula (N : ℕ) :
    ∀ v : Fin (N + 2) → ℝ, (rootClusteringFormula N).Realize v := by
  intro v
  have hv : v = Fin.cons (v 0) (Fin.cons (v (Fin.succ 0))
      (fun i : Fin N => v i.succ.succ)) := by
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases <;> rfl
  rw [hv]
  apply (rootClusteringFormula_realize _ _ _).mpr
  intro hδ
  let c : Fin N → ℝ := fun i => v i.succ.succ
  let p : ℝ[X] := ∑ i : Fin N, Polynomial.monomial i.val (c i)
  have hp (y : ℝ) : p.eval y = coefficientValue c y := by
    simp only [p, coefficientValue, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  obtain ⟨η, hη, hcluster⟩ := real_polynomial_root_clustering p (v 0) (v (Fin.succ 0)) hδ
  refine ⟨η, hη, ?_⟩
  intro y hy
  obtain ⟨q, hq, hdist⟩ := hcluster y (abs_le.mpr ⟨hy.1, hy.2.1⟩)
    (by rw [hp]; exact abs_lt.mpr ⟨hy.2.2.1, hy.2.2.2⟩)
  refine ⟨q, ?_, (abs_lt.mp hdist).1, (abs_lt.mp hdist).2⟩
  change p.eval q = 0 at hq
  rwa [hp] at hq

/-- The compactness conclusion is now proved in every actual non-Archimedean
stage by explicit finite-formula transfer. -/
theorem tower_coefficient_root_clustering (k : ℕ) {N : ℕ}
    (c : Fin N → Tower realModel k) (B δ : Tower realModel k) (hδ : 0 < δ) :
    ∃ η : Tower realModel k, 0 < η ∧ ∀ y : Tower realModel k,
      |y| ≤ B → |coefficientValue c y| < η →
      ∃ q : Tower realModel k, coefficientValue c q = 0 ∧ |y - q| < δ := by
  have hf := orderedPolynomialFormula_universal_tower realModel k
    (rootClusteringFormula N) (real_rootClusteringFormula N) (Fin.cons B (Fin.cons δ c))
  obtain ⟨η, hη, hcluster⟩ := (rootClusteringFormula_realize c B δ).mp hf hδ
  refine ⟨η, hη, ?_⟩
  intro y hy hsmall
  obtain ⟨q, hq, hdist₁, hdist₂⟩ := hcluster y
    ⟨(abs_le.mp hy).1, (abs_le.mp hy).2, (abs_lt.mp hsmall).1, (abs_lt.mp hsmall).2⟩
  exact ⟨q, hq, abs_lt.mpr ⟨hdist₁, hdist₂⟩⟩

/-- Root-clustering for an arbitrary polynomial over any of the actual tower fields. -/
theorem tower_polynomial_root_clustering (k : ℕ) (p : (Tower realModel k)[X])
    (B δ : Tower realModel k) (hδ : 0 < δ) :
    ∃ η : Tower realModel k, 0 < η ∧ ∀ y : Tower realModel k,
      |y| ≤ B → |p.eval y| < η →
      ∃ q : Tower realModel k, p.IsRoot q ∧ |y - q| < δ := by
  let c : Fin (p.natDegree + 1) → Tower realModel k := fun i => p.coeff i.val
  have hp (y : Tower realModel k) : coefficientValue c y = p.eval y := by
    unfold coefficientValue c
    exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => p.coeff i * y ^ i)
      (n := p.natDegree + 1)).trans (Polynomial.eval_eq_sum_range y).symm
  obtain ⟨η, hη, hcluster⟩ := tower_coefficient_root_clustering k c B δ hδ
  refine ⟨η, hη, ?_⟩
  intro y hy hsmall
  obtain ⟨q, hq, hdist⟩ := hcluster y hy (by rwa [hp])
  exact ⟨q, by simpa only [hp, Polynomial.IsRoot] using hq, hdist⟩

#print axioms rootClusteringFormula_realize
#print axioms tower_polynomial_root_clustering
end W3.Infinitesimal
