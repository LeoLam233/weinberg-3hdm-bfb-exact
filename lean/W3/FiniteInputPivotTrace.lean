import W3.FiniteInputPivotReconstruction
import W3.TransferOperatorPhysical

/-! Root-index trace certificates and the nine-coordinate residue interface.
In particular `Code 0` has no epsilon leaves and no arbitrary real leaves. -/
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal W3.Weighted

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [Algebra F ℝ]
variable {n : Nat} (input : Fin 15 → F) (epsilon : Fin n → F)
    (O : RealRootEnumeration ℝ)

theorem codedPivotAlgorithm_firstPivot (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    (codedPivotAlgorithm input epsilon O A hA).firstPivot =
      PivotedGram.positivePivot (pivotMatrixValue input epsilon O A)
        (PivotedGram.physical_positive_pivot _ hA) := by
  unfold codedPivotAlgorithm
  dsimp only
  split_ifs <;> rfl

theorem codedPivotAlgorithm_firstRoot_ordinal (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    let r := codedPivotAlgorithm input epsilon O A hA
    ∃ j : Nat, r.firstRoot = .squareRoot (A r.firstPivot r.firstPivot).re j ∧
      j < (O.roots (X^2-C ((A r.firstPivot r.firstPivot).re.run input epsilon O).value)).length := by
  let K := pivotMatrixValue input epsilon O A
  let i := PivotedGram.positivePivot K (PivotedGram.physical_positive_pivot K hA)
  have hi : 0 < (K i i).re := PivotedGram.positivePivot_spec K _
  unfold codedPivotAlgorithm
  dsimp only
  split_ifs <;> exact nonnegativeSquareRootCode_ordinal input epsilon O (A i i).re hi.le

/-- The optional second square root carries a valid ordinal in precisely the
quadratic family over the coded Schur diagonal selected by the second pivot. -/
theorem codedPivotAlgorithm_secondRoot_ordinal (A : PivotMatrixCode n)
    (hA : W3.PhysicalGram (pivotMatrixValue input epsilon O A)) :
    let r := codedPivotAlgorithm input epsilon O A hA
    ∀ k, r.secondPivot = some k →
      ∃ j : Nat, r.secondRoot = some (.squareRoot (r.remainder k k).re j) ∧
        j < (O.roots (X^2-C ((r.remainder k k).re.run input epsilon O).value)).length := by
  classical
  unfold codedPivotAlgorithm
  dsimp only
  split_ifs with hz
  · intro k hk
    simp at hk
  · intro k hk
    simp only [Option.some.injEq] at hk
    subst k
    have hpos := PivotedGram.positivePivot_spec
      (pivotMatrixValue input epsilon O (schurRemainderCode input epsilon O A
        (PivotedGram.positivePivot (pivotMatrixValue input epsilon O A)
          (PivotedGram.physical_positive_pivot _ hA))))
      (by
        rw [schurRemainderCode_correct input epsilon O A _
          (PivotedGram.positivePivot_spec _ _).le]
        apply PivotedGram.schur_positive_pivot _ hA _ (PivotedGram.positivePivot_spec _ _)
        intro he
        apply hz
        apply (pivotMatrixZeroTest_correct input epsilon O _).mpr
        exact (schurRemainderCode_correct input epsilon O A _
          (PivotedGram.positivePivot_spec _ _).le).trans he)
    obtain ⟨j,hj,hlt⟩ := nonnegativeSquareRootCode_ordinal input epsilon O _ hpos.le
    exact ⟨j,congrArg some hj,hlt⟩

/-- The original nine-real-coordinate order, using only rational zero and
negation in the Hermitian completion. -/
def pivotMatrixCode9 (y : Fin 9 → Code n) : PivotMatrixCode n :=
  !![⟨y 0,0⟩,⟨y 3,y 4⟩,⟨y 5,y 6⟩;
     ⟨y 3,-y 4⟩,⟨y 1,0⟩,⟨y 7,y 8⟩;
     ⟨y 5,-y 6⟩,⟨y 7,-y 8⟩,⟨y 2,0⟩]

theorem pivotMatrixCode9_correct (y : Fin 9 → Code n) :
    pivotMatrixValue input epsilon O (pivotMatrixCode9 y) =
      W3.StrataTransfer.complexMatrix
        (W3.TransferOperator.hermitianRe (fun j => (y j |>.run input epsilon O).value))
        (W3.TransferOperator.hermitianIm (fun j => (y j |>.run input epsilon O).value)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pivotMatrixValue,pivotComplexValue,pivotMatrixCode9,
      W3.StrataTransfer.complexMatrix,W3.TransferOperator.hermitianRe,
      W3.TransferOperator.hermitianIm]

/-- The exact finite-input endpoint after all infinitesimal residues. The only
coefficient leaves available in these returned programs are the given fifteen
inputs and rationals; `Fin 0` supplies no infinitesimal generator. -/
def codedRealPivotAlgorithm (input : Fin 15 → F) (O : RealRootEnumeration ℝ)
    (y : Fin 9 → Code 0)
    (hy : W3.PhysicalGram (pivotMatrixValue input Fin.elim0 O (pivotMatrixCode9 y))) :
    CodedPivotResult 0 := codedPivotAlgorithm input Fin.elim0 O (pivotMatrixCode9 y) hy

theorem codedRealPivotAlgorithm_gram (input : Fin 15 → F) (O : RealRootEnumeration ℝ)
    (y : Fin 9 → Code 0)
    (hy : W3.PhysicalGram (pivotMatrixValue input Fin.elim0 O (pivotMatrixCode9 y))) :
    W3.gram ((codedRealPivotAlgorithm input O y hy).fields input Fin.elim0 O) =
      pivotMatrixValue input Fin.elim0 O (pivotMatrixCode9 y) :=
  codedPivotedFields_gram input Fin.elim0 O (pivotMatrixCode9 y) hy

#print axioms codedPivotAlgorithm_firstRoot_ordinal
#print axioms codedPivotAlgorithm_secondRoot_ordinal
#print axioms codedRealPivotAlgorithm_gram
end W3.FiniteInput
