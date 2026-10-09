import W3.FiniteInputCandidatesArithmetic
import W3.PivotedGramFactor

/-! Finite sign-tested quadratic root selection for the coded Eq. (41) program.
The selected result is a member of an actual finite square-root code family.
Neither a real scalar leaf nor a semantic square-root witness is added to code. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal W3.Weighted

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [Algebra F ℝ]
variable {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration ℝ)

/-- First nonnegative entry, with a rational-zero fallback on an empty list.
Every branching operation is an exact scalar sign test on an interpreted code. -/
def firstNonnegativeCode : List (Code n) → Code n
  | [] => 0
  | c :: cs => if 0 ≤ (c.run input epsilon O).value then c
      else firstNonnegativeCode cs

theorem firstNonnegativeCode_spec (cs : List (Code n))
    (hex : ∃ c ∈ cs, 0 ≤ (c.run input epsilon O).value) :
    firstNonnegativeCode input epsilon O cs ∈ cs ∧
      0 ≤ ((firstNonnegativeCode input epsilon O cs).run input epsilon O).value := by
  induction cs with
  | nil => simp at hex
  | cons c cs ih =>
    by_cases hc : 0 ≤ (c.run input epsilon O).value
    · simp [firstNonnegativeCode,hc]
    · have ht : ∃ d ∈ cs, 0 ≤ (d.run input epsilon O).value := by
        obtain ⟨d,hd,hv⟩ := hex
        rcases List.mem_cons.mp hd with he | he
        · subst d; exact (hc hv).elim
        · exact ⟨d,he,hv⟩
      obtain ⟨hm,hv⟩ := ih ht
      exact ⟨by simpa [firstNonnegativeCode,hc] using List.mem_cons_of_mem c hm,
        by simpa [firstNonnegativeCode,hc] using hv⟩

/-- Finite enumeration followed by sign tests; the ordinal remains in the code. -/
def nonnegativeSquareRootCode (a : Code n) : Code n :=
  firstNonnegativeCode input epsilon O (squareRootFamily input epsilon O a)

theorem squareRootFamily_nonnegative_exists (a : Code n)
    (ha : 0 ≤ (a.run input epsilon O).value) :
    ∃ c ∈ squareRootFamily input epsilon O a,
      0 ≤ (c.run input epsilon O).value := by
  let v := (a.run input epsilon O).value
  have hp : (X^2-C v : ℝ[X]) ≠ 0 :=
    (monic_X_pow_sub_C v (by decide : (2 : Nat) ≠ 0)).ne_zero
  have hs : (X^2-C v : ℝ[X]).IsRoot (Real.sqrt v) := by
    simpa [Polynomial.IsRoot] using sub_eq_zero.mpr (Real.sq_sqrt ha)
  have hm := (O.correct (X^2-C v) hp (Real.sqrt v)).mpr hs
  rw [← squareRootFamily_correct input epsilon O a] at hm
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  exact ⟨c,hc,he.symm ▸ Real.sqrt_nonneg v⟩

theorem nonnegativeSquareRootCode_mem (a : Code n)
    (ha : 0 ≤ (a.run input epsilon O).value) :
    nonnegativeSquareRootCode input epsilon O a ∈ squareRootFamily input epsilon O a :=
  (firstNonnegativeCode_spec input epsilon O _
    (squareRootFamily_nonnegative_exists input epsilon O a ha)).1

/-- Correctness uses uniqueness of the nonnegative quadratic root only after
finite root-list synthesis and sign-tested selection have produced the code. -/
theorem nonnegativeSquareRootCode_correct (a : Code n)
    (ha : 0 ≤ (a.run input epsilon O).value) :
    ((nonnegativeSquareRootCode input epsilon O a).run input epsilon O).value =
      Real.sqrt (a.run input epsilon O).value := by
  let v := (a.run input epsilon O).value
  let c := nonnegativeSquareRootCode input epsilon O a
  have hs := firstNonnegativeCode_spec input epsilon O _
    (squareRootFamily_nonnegative_exists input epsilon O a ha)
  have hm : (c.run input epsilon O).value ∈ O.roots (X^2-C v) := by
    rw [← squareRootFamily_correct input epsilon O a]
    exact List.mem_map.mpr ⟨c,hs.1,rfl⟩
  have hp : (X^2-C v : ℝ[X]) ≠ 0 :=
    (monic_X_pow_sub_C v (by decide : (2 : Nat) ≠ 0)).ne_zero
  have he := (O.correct (X^2-C v) hp _).mp hm
  have hsq : (c.run input epsilon O).value ^ 2 = v := by
    simpa [Polynomial.IsRoot,sub_eq_zero] using he
  exact ((Real.sqrt_eq_iff_eq_sq ha hs.2).mpr hsq.symm).symm

/-- The selected code carries a valid finite root ordinal, not an arbitrary
semantic constant or a witness extracted from an existence theorem. -/
theorem nonnegativeSquareRootCode_ordinal (a : Code n)
    (ha : 0 ≤ (a.run input epsilon O).value) :
    ∃ i : Nat, nonnegativeSquareRootCode input epsilon O a = .squareRoot a i ∧
      i < (O.roots (X^2-C (a.run input epsilon O).value)).length := by
  have hm := nonnegativeSquareRootCode_mem input epsilon O a ha
  simp only [squareRootFamily,List.mem_ofFn] at hm
  obtain ⟨i,hi⟩ := hm
  exact ⟨i.val,hi.symm,i.isLt⟩

#print axioms nonnegativeSquareRootCode_correct
#print axioms nonnegativeSquareRootCode_ordinal
end W3.FiniteInput
