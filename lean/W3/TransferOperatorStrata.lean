import W3.TransferOperatorEnergy

/-! Actual minimum strata in the same ring-generic coordinates as the inverse operator. -/
noncomputable section
namespace W3.TransferOperator
open W3.StrataTransfer W3.RealModel W3.Infinitesimal Matrix

section RingModel
variable {K : Type*} [CommRing K]

@[simp] theorem hermitianRe_smul_add (a b : K) (y w : HermitianCoordinates K) (i j : Fin 3) :
    hermitianRe (a • y+b • w) i j=a*hermitianRe y i j+b*hermitianRe w i j := by
  fin_cases i <;> fin_cases j <;> simp [hermitianRe,Pi.smul_apply,smul_eq_mul]

@[simp] theorem hermitianIm_smul_add (a b : K) (y w : HermitianCoordinates K) (i j : Fin 3) :
    hermitianIm (a • y+b • w) i j=a*hermitianIm y i j+b*hermitianIm w i j := by
  fin_cases i <;> fin_cases j <;> simp [hermitianIm,Pi.smul_apply,smul_eq_mul] <;> ring

/-- Neutral and charged stationary equations in the actual nine-coordinate operator. -/
def CoordinateStrata (k : Parameters K) (y : HermitianCoordinates K) (f : K)
    (z : RealVector K) (mu : K) : Prop :=
  zMass z=1 ∧
    ((y=hermitianProjector z ∧
      ∀ i,actionRe (hermitianRe (hermitianOperator k y)) (hermitianIm (hermitianOperator k y)) z i=f*zRe z i ∧
        actionIm (hermitianRe (hermitianOperator k y)) (hermitianIm (hermitianOperator k y)) z i=f*zIm z i) ∨
     ((∀ i,actionRe (hermitianRe y) (hermitianIm y) z i=0 ∧
        actionIm (hermitianRe y) (hermitianIm y) z i=0) ∧
      hermitianOperator k y=f • hermitianIdentity+mu • hermitianProjector z))

theorem normal_coordinates_iff (k : Parameters K) (x : RealFields K) (z : RealVector K) (f mu : K) :
    (∀ i j,operatorRe k x i j=(if i=j then f else 0)+mu*projectorRe z i j ∧
      operatorIm k x i j=mu*projectorIm z i j) ↔
    hermitianOperator k (gramCoordinates x)=f • hermitianIdentity+mu • hermitianProjector z := by
  constructor
  · intro h
    apply hermitianCoordinates_ext
    · intro i j
      simpa only [hermitianRe_operator_gramCoordinates,hermitianRe_smul_add,
        hermitianRe_identity,hermitianRe_projector,mul_ite,mul_one,mul_zero] using (h i j).1
    · intro i j
      simpa only [hermitianIm_operator_gramCoordinates,hermitianIm_smul_add,
        hermitianIm_identity,hermitianIm_projector,mul_zero,zero_add] using (h i j).2
  · intro h i j
    have hre := congrArg (fun y=>hermitianRe y i j) h
    have him := congrArg (fun y=>hermitianIm y i j) h
    constructor
    · simpa only [hermitianRe_operator_gramCoordinates,hermitianRe_smul_add,
        hermitianRe_identity,hermitianRe_projector,mul_ite,mul_one,mul_zero] using hre
    · simpa only [hermitianIm_operator_gramCoordinates,hermitianIm_smul_add,
        hermitianIm_identity,hermitianIm_projector,mul_zero,zero_add] using him

theorem projector_coordinates_iff (x : RealFields K) (z : RealVector K) :
    (∀ i j,gramRe x i j=projectorRe z i j ∧ gramIm x i j=projectorIm z i j) ↔
    gramCoordinates x=hermitianProjector z := by
  constructor
  · intro h
    apply hermitianCoordinates_ext
    · intro i j
      simpa only [hermitianRe_gramCoordinates,hermitianRe_projector] using (h i j).1
    · intro i j
      simpa only [hermitianIm_gramCoordinates,hermitianIm_projector] using (h i j).2
  · intro h i j
    constructor
    · simpa only [hermitianRe_gramCoordinates,hermitianRe_projector] using
        congrArg (fun y=>hermitianRe y i j) h
    · simpa only [hermitianIm_gramCoordinates,hermitianIm_projector] using
        congrArg (fun y=>hermitianIm y i j) h

theorem strataWitness_coordinates_iff (k : Parameters K) (x : RealFields K) (z : RealVector K) (mu : K) :
    StrataWitness k x z mu ↔ CoordinateStrata k (gramCoordinates x) (twiceQuartic k x) z mu := by
  simp only [StrataWitness,CoordinateStrata,hermitianRe_gramCoordinates,hermitianIm_gramCoordinates,
    hermitianRe_operator_gramCoordinates,hermitianIm_operator_gramCoordinates,
    projector_coordinates_iff,normal_coordinates_iff]

end RingModel

/-- Universal minimum theorem specialized to the explicit sixteen-level coordinate operator. -/
theorem sixteen_minimum_coordinate_strata (k : Parameters SixteenLevelField) (x : RealFields SixteenLevelField)
    (hm : mass x=1) (hmin : ∀ y,mass y=1 → twiceQuartic k x≤twiceQuartic k y) :
    ∃ z : RealVector SixteenLevelField,∃ mu : SixteenLevelField,
      CoordinateStrata k (gramCoordinates x) (twiceQuartic k x) z mu := by
  obtain ⟨z,mu,h⟩ := sixteen_minimum_stationary_strata k x hm hmin
  exact ⟨z,mu,(strataWitness_coordinates_iff k x z mu).mp h⟩

/-- In the charged branch the physical filter hypotheses are already available. -/
theorem sixteen_minimum_neutral_or_charged (k : Parameters SixteenLevelField) (x : RealFields SixteenLevelField)
    (hm : mass x=1) (hmin : ∀ y,mass y=1 → twiceQuartic k x≤twiceQuartic k y) :
    ∃ z : RealVector SixteenLevelField, zMass z=1 ∧
      ((gramCoordinates x=hermitianProjector z ∧
        ∀ i,actionRe (hermitianRe (hermitianOperator k (hermitianProjector z)))
          (hermitianIm (hermitianOperator k (hermitianProjector z))) z i=twiceQuartic k x*zRe z i ∧
        actionIm (hermitianRe (hermitianOperator k (hermitianProjector z)))
          (hermitianIm (hermitianOperator k (hermitianProjector z))) z i=twiceQuartic k x*zIm z i) ∨
      (NormalizedKernel (gramCoordinates x) z ∧ hermitianPurity (gramCoordinates x)≤1 ∧
        ∃ mu : SixteenLevelField,hermitianOperator k (gramCoordinates x)=
          twiceQuartic k x • hermitianIdentity+mu • hermitianProjector z)) := by
  obtain ⟨z,mu,hz,h⟩ := sixteen_minimum_coordinate_strata k x hm hmin
  refine ⟨z,hz,?_⟩
  rcases h with ⟨hp,he⟩ | ⟨hk,hn⟩
  · exact Or.inl ⟨hp,by simpa only [hp] using he⟩
  · have hnker : NormalizedKernel (gramCoordinates x) z :=
      ⟨by simpa using hm,hz,hk⟩
    have hpurity := (sixteen_physical_equivalence (gramCoordinates x) z hnker).mpr
      ⟨x,hm,(gramMatches_iff x (gramCoordinates x)).mpr rfl⟩
    exact Or.inr ⟨hnker,hpurity,mu,hn⟩

#print axioms strataWitness_coordinates_iff
#print axioms sixteen_minimum_neutral_or_charged
end W3.TransferOperator
