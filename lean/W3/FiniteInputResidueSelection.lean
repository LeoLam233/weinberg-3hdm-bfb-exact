import W3.FiniteInputSyntax
import W3.InfinitesimalCoefficientResidueProgram

/-! # Finite-input residue root selection
The output is an actual member of the finite root-index program family. All
comparisons are interpreted distances; no semantic residue or chosen root is
supplied to the selector. The normalization bridge is an explicit equality of
coefficient programs and the existing normalized polynomial. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal

lemma finiteArgmin_map {α β γ : Type*} [LinearOrder γ]
    (value : α → β) (score : β → γ) (a : α) (xs : List α) :
    value (finiteArgmin (fun x => score (value x)) a xs) =
      finiteArgmin score (value a) (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [finiteArgmin, List.map_cons]
    rw [← ih]
    split_ifs <;> rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Structurally terminating exact selection retaining the finite program. -/
def selectCodedRoot {α : Type*} (value : α → K) (x : Extension K) : List α → Option α
  | [] => none
  | a :: xs => some (finiteArgmin (fun c => |x - embed K (value c)|) a xs)

theorem selectCodedRoot_map {α : Type*} (value : α → K) (x : Extension K)
    (xs : List α) :
    (selectCodedRoot value x xs).map value = selectEnumeratedRoot K x (xs.map value) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    simp only [selectCodedRoot, List.map_cons, selectEnumeratedRoot, Option.map_some]
    exact congrArg some (finiteArgmin_map value (fun q => |x - embed K q|) a xs)

theorem selectCodedRoot_mem {α : Type*} (value : α → K) (x : Extension K)
    (xs : List α) {c : α} (hc : selectCodedRoot value x xs = some c) : c ∈ xs := by
  cases xs with
  | nil => simp [selectCodedRoot] at hc
  | cons a xs =>
    simp only [selectCodedRoot, Option.some.injEq] at hc
    subst c
    exact (finiteArgmin_spec (fun c => |x - embed K (value c)|) a xs).1

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [Algebra F K]

/-- Inputs include the complete finite polynomial coefficient program. -/
def codedResidueRootProgram {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (cs : List (CoefficientCode n)) (x : Extension K) :
    Option (Code n) :=
  selectCodedRoot (fun c => (c.run input epsilon O).value) x
    (rootFamily input epsilon O cs)

theorem codedResidueRootProgram_map {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration K) (cs : List (CoefficientCode n)) (x : Extension K)
    (hp : coefficientPolynomial input epsilon cs ≠ 0) :
    (codedResidueRootProgram input epsilon O cs x).map
      (fun c => (c.run input epsilon O).value) =
    selectEnumeratedRoot K x
      (O.roots ((coefficientPolynomial input epsilon cs).map (algebraMap F K))) := by
  rw [codedResidueRootProgram, selectCodedRoot_map, rootFamily_correct input epsilon O cs hp]

theorem codedResidueRootProgram_is_root_code {n : Nat}
    (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)
    (cs : List (CoefficientCode n)) (x : Extension K) {c : Code n}
    (hc : codedResidueRootProgram input epsilon O cs x = some c) :
    ∃ i : Nat, c = .root cs i ∧
      i < (O.roots ((coefficientPolynomial input epsilon cs).map (algebraMap F K))).length := by
  have hm := selectCodedRoot_mem (fun c : Code n => (c.run input epsilon O).value) x
    (rootFamily input epsilon O cs) hc
  simp only [rootFamily, List.mem_ofFn] at hm
  obtain ⟨i, hi⟩ := hm
  exact ⟨i.val, hi.symm, i.isLt⟩

/-- Correctness is inherited from the verified normalized coefficient program,
but the selected root's finite ordinal is retained in the actual result. -/
theorem codedResidueRootProgram_correct (k n : Nat)
    {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Algebra F (Tower realModel k)]
    (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration (Tower realModel k))
    (P : F[X][X]) (hP : P ≠ 0) (cs : List (CoefficientCode n))
    (hcs : coefficientPolynomial input epsilon cs = (normalizeInitial P).2.coeff 0)
    {x : Extension (Tower realModel k)} (hx : BaseBounded (Tower realModel k) x)
    (hroot : bivariateEval (Tower realModel k) (mapBivariate (algebraMap F (Tower realModel k)) P) x = 0) :
    ∃ c : Code n,
      codedResidueRootProgram input epsilon O cs x = some c ∧
      HasRelativeResidue (Tower realModel k) x (c.run input epsilon O).value ∧
      ∃ i : Nat, c = .root cs i ∧
        i < (O.roots ((coefficientPolynomial input epsilon cs).map
          (algebraMap F (Tower realModel k)))).length := by
  have hp : coefficientPolynomial input epsilon cs ≠ 0 := by
    rw [hcs]
    exact (normalizeInitial_correct P hP).1
  have hm := codedResidueRootProgram_map input epsilon O cs x hp
  rw [hcs] at hm
  obtain ⟨q, hq, hr, _⟩ := coefficientResidueProgram_correct k
    (algebraMap F (Tower realModel k)) O P hP hx hroot
  change selectEnumeratedRoot (Tower realModel k) x
    (O.roots (((normalizeInitial P).2.coeff 0).map
      (algebraMap F (Tower realModel k)))) = some q at hq
  rw [hq] at hm
  cases hc : codedResidueRootProgram input epsilon O cs x with
  | none => simp [hc] at hm
  | some c =>
    simp only [hc, Option.map_some, Option.some.injEq] at hm
    refine ⟨c, rfl, ?_, codedResidueRootProgram_is_root_code input epsilon O cs x hc⟩
    rwa [hm]

#print axioms codedResidueRootProgram_correct
#print axioms codedResidueRootProgram_is_root_code
end W3.FiniteInput
