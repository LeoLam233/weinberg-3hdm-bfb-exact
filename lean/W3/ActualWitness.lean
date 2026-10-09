import W3.ActualStability

/-! Entrywise residue of an actual perturbed minimizing direction is an exact
physical minimizing direction of the original potential. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace W3.Infinitesimal
open W3.RealModel ArchimedeanClass
open scoped BigOperators

abbrev Finite16 := FiniteElement SixteenLevelField

def finiteValue : Finite16 →+* SixteenLevelField where
  toFun := fun x => x.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma mass_natural {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : RealFields A) : f (mass x) = mass (fun i => f (x i)) := by
  simp [mass]

lemma twiceQuartic_natural {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (κ : Parameters A) (x : RealFields A) :
    f (twiceQuartic κ x) = twiceQuartic (fun i => f (κ i)) (fun i => f (x i)) := by
  have h := intPolynomialEval_natural f potentialPolynomial (Sum.elim κ x)
  have hv : (fun j => f (Sum.elim κ x j)) = Sum.elim (fun i => f (κ i)) (fun i => f (x i)) := by
    funext j; cases j <;> rfl
  rw [hv, w3_potential_intEval, w3_potential_intEval] at h
  exact h

lemma normalized_coordinate_bounds {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : RealFields K) (hx : mass x = 1) (i : Fin 12) : -1 ≤ x i ∧ x i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 12))) => sq_nonneg (x j))
    (Finset.mem_univ i)
  change x i^2 ≤ mass x at h
  rw [hx] at h
  constructor <;> nlinarith [sq_nonneg (x i-1),sq_nonneg (x i+1)]

def finitePoint (x : RealFields SixteenLevelField) (hx : mass x = 1) : RealFields Finite16 :=
  fun i => boundedElement realEmbedding16 (x i) (a := (-1:ℝ)) (b := (1:ℝ))
    (by rw [map_neg, map_one]; exact (normalized_coordinate_bounds x hx i).1)
    (by rw [map_one]; exact (normalized_coordinate_bounds x hx i).2)

@[simp] lemma finitePoint_value (x : RealFields SixteenLevelField) (hx : mass x = 1) (i : Fin 12) :
    finiteValue (finitePoint x hx i) = x i := rfl

def finiteReal (r : ℝ) : Finite16 :=
  FiniteElement.mk (realEmbedding16 r) (mk_map_nonneg_of_archimedean realEmbedding16 r)

@[simp] lemma finiteReal_value (r : ℝ) : finiteValue (finiteReal r) = realEmbedding16 r := rfl
@[simp] lemma finiteReal_residue (r : ℝ) : realResidue (finiteReal r) = r :=
  realResidue_real realEmbedding16 r

def finiteEpsilon (i : Fin 16) : Finite16 :=
  boundedElement realEmbedding16 (chronologicalEpsilon i) (a := (0:ℝ)) (b := (1:ℝ))
    (by rw [map_zero]; exact (chronologicalEpsilon_infinitesimal i).1.le)
    ((chronologicalEpsilon_infinitesimal i).2 1 (by norm_num)).le

@[simp] lemma finiteEpsilon_value (i : Fin 16) : finiteValue (finiteEpsilon i) = chronologicalEpsilon i := rfl
@[simp] lemma finiteEpsilon_residue (i : Fin 16) : realResidue (finiteEpsilon i) = 0 := by
  rw [realResidue_eq_stdPart]
  exact stdPart_infinitesimal realEmbedding16 (chronologicalEpsilon_infinitesimal i)

def finiteParameters (κ : Parameters ℝ) (i : Fin 15) : Finite16 :=
  finiteReal (κ i) + (if i.val < 6 then 2*finiteEpsilon 0 else 0) + finiteEpsilon i.succ

@[simp] lemma finiteParameters_value (κ : Parameters ℝ) (i : Fin 15) :
    finiteValue (finiteParameters κ i) = actualParameters κ i := by
  unfold finiteParameters actualParameters deformedParameters coefficientEpsilon
  split_ifs <;> simp [map_ofNat]

@[simp] lemma finiteParameters_residue (κ : Parameters ℝ) (i : Fin 15) :
    realResidue (finiteParameters κ i) = κ i := by
  unfold finiteParameters
  split_ifs <;> simp [map_ofNat]

def residuePoint (x : RealFields SixteenLevelField) (hx : mass x = 1) : RealFields ℝ :=
  fun i => realResidue (finitePoint x hx i)

lemma residuePoint_normalized (x : RealFields SixteenLevelField) (hx : mass x = 1) :
    mass (residuePoint x hx) = 1 := by
  have hfin : mass (finitePoint x hx) = (1 : Finite16) := by
    apply FiniteElement.ext
    change finiteValue (mass (finitePoint x hx)) = finiteValue 1
    rw [mass_natural, map_one]
    simpa using hx
  change mass (fun i => realResidue (finitePoint x hx i)) = 1
  calc
    _ = realResidue (mass (finitePoint x hx)) :=
      (mass_natural (realResidue (L := SixteenLevelField)).toRingHom (finitePoint x hx)).symm
    _ = 1 := by rw [hfin, map_one]

lemma finite_minimum_bounds (κ : Parameters ℝ) :
    realEmbedding16 (realMinimum κ-3) ≤ deformedMinimum κ ∧
      deformedMinimum κ ≤ realEmbedding16 (realMinimum κ+3) := by
  have h := abs_le.mp (actual_minimum_bound κ)
  have he := (chronologicalEpsilon_infinitesimal 0).1
  have he1 := (chronologicalEpsilon_infinitesimal 0).2 1 (by norm_num)
  have hb := nine_halves_epsilon_one_lt_zero
  simp only [map_one] at he1
  simp only [map_sub, map_add, map_ofNat]
  constructor <;> linarith

def finiteMinimum (κ : Parameters ℝ) : Finite16 :=
  boundedElement realEmbedding16 (deformedMinimum κ) (finite_minimum_bounds κ).1 (finite_minimum_bounds κ).2

@[simp] lemma finiteMinimum_value (κ : Parameters ℝ) :
    finiteValue (finiteMinimum κ) = deformedMinimum κ := rfl
@[simp] lemma finiteMinimum_residue (κ : Parameters ℝ) :
    realResidue (finiteMinimum κ) = realMinimum κ := by
  rw [realResidue_eq_stdPart]
  exact (actual_minimum_signs_and_residue κ).2.2.2.2

/-- Any normalized perturbed minimizing point, not only the chosen one, yields
an exact original normalized minimizer by entrywise residue. -/
theorem residuePoint_minimizing (κ : Parameters ℝ) (x : RealFields SixteenLevelField)
    (hx : mass x = 1) (hv : quarticReal (actualParameters κ) x = deformedMinimum κ) :
    mass (residuePoint x hx) = 1 ∧ quarticReal κ (residuePoint x hx) = realMinimum κ := by
  have hfin : twiceQuartic (finiteParameters κ) (finitePoint x hx) = 2*finiteMinimum κ := by
    apply FiniteElement.ext
    change finiteValue (twiceQuartic (finiteParameters κ) (finitePoint x hx)) = finiteValue (2*finiteMinimum κ)
    rw [twiceQuartic_natural, map_mul, map_ofNat]
    simp only [finiteParameters_value, finitePoint_value, finiteMinimum_value]
    dsimp only [quarticReal] at hv
    linarith
  have hres := congrArg (realResidue : Finite16 → ℝ) hfin
  have hnat := twiceQuartic_natural (realResidue (L := SixteenLevelField)).toRingHom
    (finiteParameters κ) (finitePoint x hx)
  replace hres := hnat.symm.trans hres
  rw [map_mul, map_ofNat] at hres
  have hp : (fun i => (realResidue (L := SixteenLevelField)).toRingHom (finiteParameters κ i)) = κ := by
    funext i
    exact finiteParameters_residue κ i
  rw [hp, finiteMinimum_residue] at hres
  refine ⟨residuePoint_normalized x hx, ?_⟩
  change twiceQuartic κ (residuePoint x hx) = 2*realMinimum κ at hres
  rw [quarticReal,hres]
  ring

/-- The field-direction witness is a genuine pair of complex doublet components
and can be negative or flat according to the original minimum. -/
theorem residue_physical_minimizer (κ : Parameters ℝ) :
    let x := deformedMinimumPoint κ
    let xr := residuePoint x (deformedMinimumPoint_spec κ).1
    ‖fields xr‖ = 1 ∧ W3.quartic (couplings κ) (fields xr) = realMinimum κ := by
  dsimp only
  obtain ⟨hn,hv⟩ := residuePoint_minimizing κ (deformedMinimumPoint κ)
    (deformedMinimumPoint_spec κ).1 rfl
  rw [mass_fields] at hn
  refine ⟨?_, ?_⟩
  · nlinarith [norm_nonneg (fields (residuePoint (deformedMinimumPoint κ) (deformedMinimumPoint_spec κ).1))]
  · rwa [quarticReal_fields] at hv

#print axioms residuePoint_minimizing
#print axioms residue_physical_minimizer
end W3.Infinitesimal
