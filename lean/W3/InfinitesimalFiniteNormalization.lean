import W3.InfinitesimalAnnihilator

/-! # Terminating removal of a common initial power
The number of coefficient tests is bounded by one more than the input degree.
-/
noncomputable section
namespace W3.Infinitesimal
open Polynomial

/-- A fuel-bounded algorithm: test the constant coefficient, divide by X only
when it vanishes, and count the removed factors. -/
def stripInitial {R : Type*} [CommRing R] [DecidableEq R] : ℕ → R[X] → ℕ × R[X]
  | 0, p => (0, p)
  | fuel + 1, p => if p.coeff 0 = 0 then
      let out := stripInitial fuel p.divX
      (out.1 + 1, out.2)
    else (0, p)

theorem stripInitial_correct {R : Type*} [CommRing R] [DecidableEq R]
    (fuel : ℕ) (p : R[X]) (hp : p ≠ 0) (hdeg : p.natDegree < fuel) :
    (stripInitial fuel p).2.coeff 0 ≠ 0 ∧
      p = X ^ (stripInitial fuel p).1 * (stripInitial fuel p).2 := by
  induction fuel generalizing p with
  | zero => omega
  | succ fuel ih =>
    by_cases hc : p.coeff 0 = 0
    · have heq : p.divX * X = p := by
        simpa only [hc, Polynomial.C_0, add_zero] using Polynomial.divX_mul_X_add p
      have hdiv : p.divX ≠ 0 := by
        intro h
        apply hp
        simpa only [h, zero_mul] using heq.symm
      have hpos : 0 < p.natDegree := by
        by_contra h
        have hn : p.natDegree = 0 := by omega
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hn
        rw [hc, Polynomial.C_0] at hC
        exact hp hC
      have hdeg' : p.divX.natDegree < fuel := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        omega
      obtain ⟨hq, hfactor⟩ := ih p.divX hdiv hdeg'
      simp only [stripInitial, hc, ite_true, Prod.fst, Prod.snd]
      refine ⟨hq, ?_⟩
      calc
        p = p.divX * X := heq.symm
        _ = (X ^ (stripInitial fuel p.divX).1 * (stripInitial fuel p.divX).2) * X :=
          congrArg (fun z => z * X) hfactor
        _ = X ^ ((stripInitial fuel p.divX).1 + 1) * (stripInitial fuel p.divX).2 := by
          rw [pow_succ]
          ring
    · simp only [stripInitial, hc, ite_false, Prod.fst, Prod.snd, pow_zero, one_mul]
      exact ⟨hc, True.intro⟩

/-- The normalization program uses a concrete sufficient finite fuel bound. -/
def normalizeInitial {R : Type*} [CommRing R] [DecidableEq R] (p : R[X]) : ℕ × R[X] :=
  stripInitial (p.natDegree + 1) p

theorem normalizeInitial_correct {R : Type*} [CommRing R] [DecidableEq R]
    (p : R[X]) (hp : p ≠ 0) :
    (normalizeInitial p).2.coeff 0 ≠ 0 ∧
      p = X ^ (normalizeInitial p).1 * (normalizeInitial p).2 :=
  stripInitial_correct _ p hp (Nat.lt_succ_self _)

#print axioms normalizeInitial_correct
end W3.Infinitesimal
