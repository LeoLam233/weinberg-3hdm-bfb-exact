import W3.InfinitesimalFiniteNormalization
import W3.InfinitesimalFiniteSelection
import W3.InfinitesimalCoefficientPresentation

/-! # Correctness of the finite selected-root residue procedure
Inputs: a nonzero finite annihilator and a real-root enumeration oracle.
Normalization and selection themselves are explicit terminating recursions.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The real-root enumeration interface; multiplicities are allowed and do not
change the selection. It makes no rational-density assumption. -/
structure RealRootEnumeration where
  roots : K[X] → List K
  correct : ∀ p : K[X], p ≠ 0 → ∀ q : K, q ∈ roots p ↔ p.IsRoot q

/-- The mathematical finite root enumeration. Effective implementations can
replace it with exact algebraic/Thom root data having the same specification. -/
def polynomialRootsEnumeration : RealRootEnumeration K where
  roots p := p.roots.toList
  correct p hp q := Multiset.mem_toList.trans (Polynomial.mem_roots hp)

def selectEnumeratedRoot (x : Extension K) : List K → Option K
  | [] => none
  | a :: xs => some (finiteArgmin (fun q => |x - embed K q|) a xs)

lemma selectEnumeratedRoot_eq (oracle : RealRootEnumeration K) {p : K[X]} (hp : p ≠ 0)
    {x : Extension K} {q : K} (hq : p.IsRoot q) (hres : HasRelativeResidue K x q) :
    selectEnumeratedRoot K x (oracle.roots p) = some q := by
  have hmem := (oracle.correct p hp q).mpr hq
  cases hlist : oracle.roots p with
  | nil => simp only [hlist, List.not_mem_nil] at hmem
  | cons a xs =>
    rw [hlist] at hmem
    simp only [hlist, selectEnumeratedRoot]
    exact congrArg some (finiteArgmin_relativeResidue K hres hmem)

/-- This program performs at most degree(P)+1 constant-coefficient tests,
one finite root enumeration, and a finite list of exact comparisons. -/
def finiteResidueProgram (oracle : RealRootEnumeration K) (P : K[X][X])
    (x : Extension K) : Option K :=
  selectEnumeratedRoot K x (oracle.roots ((normalizeInitial P).2.coeff 0))

/-- Correct for every bounded algebraic branch, including repeated specialized roots. -/
theorem finiteResidueProgram_correct (k : ℕ)
    (oracle : RealRootEnumeration (Tower realModel k)) (P : (Tower realModel k)[X][X])
    (hP : P ≠ 0) {x : Extension (Tower realModel k)}
    (hx : BaseBounded (Tower realModel k) x) (hroot : bivariateEval (Tower realModel k) P x = 0) :
    ∃ q : Tower realModel k,
      finiteResidueProgram (Tower realModel k) oracle P x = some q ∧
      HasRelativeResidue (Tower realModel k) x q := by
  obtain ⟨hQ, heq⟩ := normalizeInitial_correct P hP
  have hrootQ : bivariateEval (Tower realModel k) (normalizeInitial P).2 x = 0 := by
    unfold bivariateEval at hroot ⊢
    rw [heq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ (epsilon_pos _).ne')
  obtain ⟨B, hB, hbound⟩ := hx
  obtain ⟨q, hq, hres⟩ := tower_relativeResidue_of_infinitesimal_polynomial k hQ hbound
    (constantCoefficient_small_of_annihilator _ _ ⟨B, hB, hbound⟩ hrootQ)
  exact ⟨q, selectEnumeratedRoot_eq _ oracle hQ hq hres, hres⟩

#print axioms finiteResidueProgram_correct
end W3.Infinitesimal
