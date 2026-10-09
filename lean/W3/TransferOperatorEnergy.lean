import W3.TransferOperatorPhysical

/-! Ring-generic Gram-coordinate evaluation of the original quartic. -/
noncomputable section
namespace W3.TransferOperator
open W3.StrataTransfer W3.RealModel Matrix
open scoped BigOperators

section RingModel
variable {K : Type*} [CommRing K]

/-- The nine independent real coordinates of the actual two-row Gram matrix. -/
def gramCoordinates (x : RealFields K) : HermitianCoordinates K :=
  ![radii x 0,radii x 1,radii x 2,offRe x 0,offIm x 0,
    offRe x 1,offIm x 1,offRe x 2,offIm x 2]

/-- Twice the quartic, evaluated on an arbitrary Hermitian matrix. -/
def hermitianEnergy (k : Parameters K) (y : HermitianCoordinates K) : K :=
  k 0*(y 0)^2+k 1*(y 1)^2+k 2*(y 2)^2+
  2*(k 3*y 0*y 1+k 4*y 0*y 2+k 5*y 1*y 2)+
  2*(k 6*((y 3)^2+(y 4)^2)+k 7*((y 5)^2+(y 6)^2)+k 8*((y 7)^2+(y 8)^2))+
  2*(k 9*((y 3)^2-(y 4)^2)-2*k 10*y 3*y 4+
    k 11*((y 5)^2-(y 6)^2)-2*k 12*y 5*y 6+
    k 13*((y 7)^2-(y 8)^2)-2*k 14*y 7*y 8)

/-- The trace pairing on Hermitian coordinates. -/
def hermitianPair (y w : HermitianCoordinates K) : K :=
  y 0*w 0+y 1*w 1+y 2*w 2+
  2*(y 3*w 3+y 4*w 4+y 5*w 5+y 6*w 6+y 7*w 7+y 8*w 8)

/-- Exact structured coupling operator in the nine real coordinates. -/
def hermitianOperator (k : Parameters K) (y : HermitianCoordinates K) : HermitianCoordinates K :=
  ![k 0*y 0+k 3*y 1+k 4*y 2,k 3*y 0+k 1*y 1+k 5*y 2,k 4*y 0+k 5*y 1+k 2*y 2,
    (k 6+k 9)*y 3-k 10*y 4,(k 6-k 9)*y 4-k 10*y 3,
    (k 7+k 11)*y 5-k 12*y 6,(k 7-k 11)*y 6-k 12*y 5,
    (k 8+k 13)*y 7-k 14*y 8,(k 8-k 13)*y 8-k 14*y 7]

/-- Coordinates of the identity Hermitian matrix. -/
def hermitianIdentity : HermitianCoordinates K := ![1,1,1,0,0,0,0,0,0]

/-- Coordinates of the rank-one matrix z z†. -/
def hermitianProjector (z : RealVector K) : HermitianCoordinates K :=
  ![(zRe z 0)^2+(zIm z 0)^2,(zRe z 1)^2+(zIm z 1)^2,(zRe z 2)^2+(zIm z 2)^2,
    projectorRe z 0 1,projectorIm z 0 1,projectorRe z 0 2,projectorIm z 0 2,
    projectorRe z 1 2,projectorIm z 1 2]

theorem hermitianCoordinates_ext {y w : HermitianCoordinates K}
    (hre : ∀ i j,hermitianRe y i j=hermitianRe w i j)
    (him : ∀ i j,hermitianIm y i j=hermitianIm w i j) : y=w := by
  funext i
  fin_cases i
  · exact hre 0 0
  · exact hre 1 1
  · exact hre 2 2
  · exact hre 0 1
  · exact him 0 1
  · exact hre 0 2
  · exact him 0 2
  · exact hre 1 2
  · exact him 1 2

@[simp] theorem hermitianRe_projector (z : RealVector K) :
    hermitianRe (hermitianProjector z)=projectorRe z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianRe,hermitianProjector,projectorRe,projectorIm] <;> ring

@[simp] theorem hermitianIm_projector (z : RealVector K) :
    hermitianIm (hermitianProjector z)=projectorIm z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianIm,hermitianProjector,projectorRe,projectorIm] <;> ring

@[simp] theorem hermitianRe_identity (i j : Fin 3) :
    hermitianRe (hermitianIdentity : HermitianCoordinates K) i j=if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hermitianRe,hermitianIdentity]

@[simp] theorem hermitianIm_identity (i j : Fin 3) :
    hermitianIm (hermitianIdentity : HermitianCoordinates K) i j=0 := by
  fin_cases i <;> fin_cases j <;> simp [hermitianIm,hermitianIdentity]

@[simp] theorem hermitianTrace_projector (z : RealVector K) :
    hermitianTrace (hermitianProjector z)=zMass z := by
  simp [hermitianTrace,hermitianProjector,zMass,Fin.sum_univ_three]

@[simp] theorem hermitianPair_identity_left (y : HermitianCoordinates K) :
    hermitianPair hermitianIdentity y=hermitianTrace y := by
  simp [hermitianPair,hermitianIdentity,hermitianTrace]

@[simp] theorem hermitianPair_identity_right (y : HermitianCoordinates K) :
    hermitianPair y hermitianIdentity=hermitianTrace y := by
  simp [hermitianPair,hermitianIdentity,hermitianTrace]

/-- The real expectation value, without any complex-field structure. -/
theorem hermitianPair_projector (y : HermitianCoordinates K) (z : RealVector K) :
    hermitianPair (hermitianProjector z) y=
      ∑ i,(zRe z i*actionRe (hermitianRe y) (hermitianIm y) z i+
        zIm z i*actionIm (hermitianRe y) (hermitianIm y) z i) := by
  simp [hermitianPair,hermitianProjector,projectorRe,projectorIm,actionRe,actionIm,
    hermitianRe,hermitianIm,Fin.sum_univ_three]
  ring

theorem hermitianPair_projector_of_kernel (y : HermitianCoordinates K) (z : RealVector K)
    (h : ∀ i,actionRe (hermitianRe y) (hermitianIm y) z i=0 ∧
      actionIm (hermitianRe y) (hermitianIm y) z i=0) :
    hermitianPair (hermitianProjector z) y=0 := by
  rw [hermitianPair_projector]
  apply Finset.sum_eq_zero
  intro i _
  rw [(h i).1,(h i).2]
  simp

@[simp] theorem actionRe_projector (z : RealVector K) (i : Fin 3) :
    actionRe (hermitianRe (hermitianProjector z)) (hermitianIm (hermitianProjector z)) z i=
      zMass z*zRe z i := by
  rw [hermitianRe_projector,hermitianIm_projector]
  fin_cases i <;> simp [actionRe,projectorRe,projectorIm,zMass,Fin.sum_univ_three] <;> ring

@[simp] theorem actionIm_projector (z : RealVector K) (i : Fin 3) :
    actionIm (hermitianRe (hermitianProjector z)) (hermitianIm (hermitianProjector z)) z i=
      zMass z*zIm z i := by
  rw [hermitianRe_projector,hermitianIm_projector]
  fin_cases i <;> simp [actionIm,projectorRe,projectorIm,zMass,Fin.sum_univ_three] <;> ring

@[simp] theorem hermitianPair_projector_self (z : RealVector K) :
    hermitianPair (hermitianProjector z) (hermitianProjector z)=(zMass z)^2 := by
  rw [hermitianPair_projector]
  simp only [actionRe_projector,actionIm_projector]
  simp [zMass,Fin.sum_univ_three]
  ring

@[simp] theorem hermitianRe_gramCoordinates (x : RealFields K) :
    hermitianRe (gramCoordinates x)=gramRe x := by rfl
@[simp] theorem hermitianIm_gramCoordinates (x : RealFields K) :
    hermitianIm (gramCoordinates x)=gramIm x := by rfl

@[simp] theorem hermitianTrace_gramCoordinates (x : RealFields K) :
    hermitianTrace (gramCoordinates x)=mass x := by
  simp [hermitianTrace,gramCoordinates,radii,mass,Fin.sum_univ_succ]
  ring

@[simp] theorem hermitianEnergy_gramCoordinates (k : Parameters K) (x : RealFields K) :
    hermitianEnergy k (gramCoordinates x)=twiceQuartic k x := by rfl

@[simp] theorem gramMatches_iff (x : RealFields K) (y : HermitianCoordinates K) :
    GramMatches x y ↔ gramCoordinates x=y := by
  constructor
  · intro h
    funext i
    fin_cases i
    · exact (h 0 0).1
    · exact (h 1 1).1
    · exact (h 2 2).1
    · exact (h 0 1).1
    · exact (h 0 1).2
    · exact (h 0 2).1
    · exact (h 0 2).2
    · exact (h 1 2).1
    · exact (h 1 2).2
  · rintro rfl
    intro i j
    exact ⟨rfl,rfl⟩

theorem gramMatches_energy (k : Parameters K) {x : RealFields K} {y : HermitianCoordinates K}
    (h : GramMatches x y) : twiceQuartic k x=hermitianEnergy k y := by
  rw [← hermitianEnergy_gramCoordinates,(gramMatches_iff x y).mp h]

theorem gramMatches_mass {x : RealFields K} {y : HermitianCoordinates K}
    (h : GramMatches x y) : mass x=hermitianTrace y := by
  rw [← hermitianTrace_gramCoordinates,(gramMatches_iff x y).mp h]

@[simp] theorem hermitianRe_operator_gramCoordinates (k : Parameters K) (x : RealFields K) :
    hermitianRe (hermitianOperator k (gramCoordinates x))=operatorRe k x := by rfl
@[simp] theorem hermitianIm_operator_gramCoordinates (k : Parameters K) (x : RealFields K) :
    hermitianIm (hermitianOperator k (gramCoordinates x))=operatorIm k x := by rfl

theorem hermitianEnergy_eq_pair (k : Parameters K) (y : HermitianCoordinates K) :
    hermitianEnergy k y=hermitianPair y (hermitianOperator k y) := by
  simp [hermitianEnergy,hermitianPair,hermitianOperator]
  ring

theorem hermitianPair_self (y : HermitianCoordinates K) :
    hermitianPair y y=hermitianPurity y := by
  simp [hermitianPair,hermitianPurity]
  ring

theorem hermitianPair_comm (y w : HermitianCoordinates K) :
    hermitianPair y w=hermitianPair w y := by
  simp [hermitianPair]
  ring

theorem hermitianOperator_selfadjoint (k : Parameters K) (y w : HermitianCoordinates K) :
    hermitianPair y (hermitianOperator k w)=hermitianPair (hermitianOperator k y) w := by
  simp [hermitianPair,hermitianOperator]
  ring

end RingModel

/-- A retained target-field matrix comes with an actual field and its exact original value. -/
theorem sixteen_physical_energy_witness (k : Parameters W3.Infinitesimal.SixteenLevelField)
    (y : HermitianCoordinates W3.Infinitesimal.SixteenLevelField)
    (z : RealVector W3.Infinitesimal.SixteenLevelField)
    (hn : NormalizedKernel y z) (hpurity : hermitianPurity y≤1) :
    ∃ x : RealFields W3.Infinitesimal.SixteenLevelField,
      mass x=1 ∧ GramMatches x y ∧ twiceQuartic k x=hermitianEnergy k y := by
  obtain ⟨x,hm,hgram⟩ := (sixteen_physical_equivalence y z hn).mp hpurity
  exact ⟨x,hm,hgram,gramMatches_energy k hgram⟩

#print axioms gramMatches_energy
#print axioms sixteen_physical_energy_witness
end W3.TransferOperator
