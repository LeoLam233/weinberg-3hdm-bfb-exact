import W3.FiniteInputAnnihilatorRing


/-! Semantic coefficient tests select finite degrees and zero branches. The
outputs are free-ring polynomials constructed solely from coded arithmetic. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.FiniteInput
open Polynomial W3.Infinitesimal

variable {n : Nat} {F : Type*} [Field F] [CharZero F] [DecidableEq F]
variable (input : Fin 15 → F) (epsilon : Fin n → F)
namespace FreeCoefficientRing

/-- Monicization in a free ring: the top coefficient is literally one, and
all lower coefficients explicitly multiply their input code by a coded inverse.
The finite degree is obtained by exact coefficient tests after specialization. -/
def monicLift (p : (FreeCoefficientRing n)[X]) : (FreeCoefficientRing n)[X] :=
  let d := (p.map (specialize input epsilon)).natDegree
  X^d + polynomialOfList (List.ofFn fun i : Fin d =>
    MvPolynomial.X (.mul ((p.coeff i).lower) (.inv ((p.coeff d).lower))))

theorem polynomialOfList_degree_lt {R : Type*} [Semiring R] (cs : List R) :
    (polynomialOfList cs).degree < cs.length := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [polynomialOfList_coeff]
  rw [List.getElem?_eq_none (by omega)]
  rfl

theorem polynomialOfList_ofFn_degree_lt {R : Type*} [Semiring R] {d : Nat}
    (cs : Fin d → R) : (polynomialOfList (List.ofFn cs)).degree < d := by
  simpa only [List.length_ofFn] using polynomialOfList_degree_lt (List.ofFn cs)

theorem monicLift_monic (p : (FreeCoefficientRing n)[X]) :
    (monicLift input epsilon p).Monic := by
  classical
  exact monic_X_pow_add (polynomialOfList_ofFn_degree_lt _)

theorem monicLift_map (p : (FreeCoefficientRing n)[X])
    (hp : p.map (specialize input epsilon) ≠ 0) :
    (monicLift input epsilon p).map (specialize input epsilon) =
      p.map (specialize input epsilon) *
        C (p.map (specialize input epsilon)).leadingCoeff⁻¹ := by
  classical
  let f := specialize input epsilon
  let q := p.map f
  have hq : q ≠ 0 := hp
  have hmap : p.map (specialize input epsilon) = q := rfl
  have hcoeff (j : Nat) : specialize input epsilon (p.coeff j) = q.coeff j := by
    simp only [q, f, Polynomial.coeff_map]
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, coeff_mul_C]
  change f ((monicLift input epsilon p).coeff i) = q.coeff i * q.leadingCoeff⁻¹
  simp only [monicLift, coeff_add, coeff_X_pow, polynomialOfList_coeff]
  rw [hmap, List.getElem?_ofFn]
  by_cases hi : i < q.natDegree
  · have hid : i ≠ q.natDegree := by omega
    simp only [hid, ite_false, dif_pos hi, Option.getD_some, zero_add,
      f, specialize_X, CoefficientCode.eval, lower_correct, hcoeff, coeff_natDegree]
  · simp only [dif_neg hi, Option.getD_none, add_zero]
    by_cases hid : i = q.natDegree
    · subst i
      simp only [ite_true, map_one, coeff_natDegree]
      exact (mul_inv_cancel₀ hl).symm
    · simp only [hid, ite_false, map_zero,
        coeff_eq_zero_of_natDegree_lt (show q.natDegree < i by omega), zero_mul]

/-- Only a bounded sequence of mapped constant-coefficient tests is used. -/
def stripMapped : Nat → (FreeCoefficientRing n)[X] → Nat × (FreeCoefficientRing n)[X]
  | 0, p => (0,p)
  | fuel+1, p => if specialize input epsilon (p.coeff 0) = 0 then
      let out := stripMapped fuel p.divX
      (out.1+1,out.2)
    else (0,p)

theorem stripMapped_map (fuel : Nat) (p : (FreeCoefficientRing n)[X]) :
    ((stripMapped input epsilon fuel p).1,
      (stripMapped input epsilon fuel p).2.map (specialize input epsilon)) =
    stripInitial fuel (p.map (specialize input epsilon)) := by
  classical
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    simp only [stripMapped, stripInitial, Polynomial.coeff_map]
    split_ifs with h
    · have hh := ih p.divX
      have hd : (p.divX).map (specialize input epsilon) =
          (p.map (specialize input epsilon)).divX := by
        ext i
        simp only [Polynomial.coeff_map, Polynomial.coeff_divX]
      rw [hd] at hh
      exact congrArg (fun out => (out.1+1,out.2)) hh
    · rfl

/-- Reverse the boundedly stripped polynomial at its specialized degree.
Using explicit reflection avoids any implicit degree-preservation assumption. -/
def inverseRaw (p : (FreeCoefficientRing n)[X]) : (FreeCoefficientRing n)[X] :=
  let q := (stripMapped input epsilon
    ((p.map (specialize input epsilon)).natDegree+1) p).2
  q.reflect (q.map (specialize input epsilon)).natDegree

theorem inverseRaw_map (p : (FreeCoefficientRing n)[X]) :
    (inverseRaw input epsilon p).map (specialize input epsilon) =
      (normalizeInitial (p.map (specialize input epsilon))).2.reverse := by
  have h := congrArg Prod.snd (stripMapped_map input epsilon
    ((p.map (specialize input epsilon)).natDegree+1) p)
  change (stripMapped input epsilon ((p.map (specialize input epsilon)).natDegree+1) p).2.map
    (specialize input epsilon) = (normalizeInitial (p.map (specialize input epsilon))).2 at h
  simp only [inverseRaw, ← reflect_map, h, reverse]

end FreeCoefficientRing

/-- The initial coefficient list is inserted literally into the free ring. -/
def liftCoefficientPolynomial (cs : List (CoefficientCode n)) : (FreeCoefficientRing n)[X] :=
  polynomialOfList (cs.map MvPolynomial.X)

theorem polynomialOfList_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (cs : List R) :
    (polynomialOfList cs).map f = polynomialOfList (cs.map f) := by
  induction cs with
  | nil => simp [polynomialOfList]
  | cons c cs ih => simp [polynomialOfList, ih]

@[simp] theorem liftCoefficientPolynomial_map (cs : List (CoefficientCode n)) :
    (liftCoefficientPolynomial cs).map (FreeCoefficientRing.specialize input epsilon) =
      coefficientPolynomial input epsilon cs := by
  simp only [liftCoefficientPolynomial, polynomialOfList_map, List.map_map,
    Function.comp_def, FreeCoefficientRing.specialize_X, coefficientPolynomial]
end W3.FiniteInput
