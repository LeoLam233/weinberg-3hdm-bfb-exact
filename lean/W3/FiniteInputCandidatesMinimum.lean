import W3.FiniteInputCandidatesLists

/-! Structural finite argmin returns its original code-bearing candidate. -/
noncomputable section
set_option linter.unusedSectionVars false
namespace W3.FiniteInput
open Polynomial W3.Elimination W3.Weighted W3.Infinitesimal
variable {n : Nat}
variable {F K : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Field K] [Algebra F K] [LinearOrder K] [IsStrictOrderedRing K]
variable (input : Fin 15 → F) (epsilon : Fin n → F) (O : RealRootEnumeration K)

/-- A list recursion, not a choice from a proof that a minimum exists. -/
def codeArgmin {α : Type*} (score : α → Code n) : List α → Option α
  | [] => none
  | a :: as => some (finiteArgmin (fun x => ((score x).run input epsilon O).value) a as)

theorem codeArgmin_spec {α : Type*} (score : α → Code n) (xs : List α) (a : α)
    (h : codeArgmin input epsilon O score xs = some a) :
    a ∈ xs ∧ ∀ b ∈ xs, ((score a).run input epsilon O).value ≤ ((score b).run input epsilon O).value := by
  cases xs with
  | nil => simp [codeArgmin] at h
  | cons x xs =>
    simp only [codeArgmin,Option.some.injEq] at h
    subst a
    exact finiteArgmin_spec _ _ _

theorem codeArgmin_exists {α : Type*} (score : α → Code n) (xs : List α) (h : xs ≠ []) :
    ∃ a, codeArgmin input epsilon O score xs = some a := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => exact ⟨_,rfl⟩

theorem codeArgmin_minimum {α : Type*} (score : α → Code n) (xs : List α) (a : α)
    (h : codeArgmin input epsilon O score xs = some a) (s : Finset K) (hne : s.Nonempty)
    (hm : ∀ v, v ∈ xs.map (fun b => ((score b).run input epsilon O).value) ↔ v ∈ s) :
    ((score a).run input epsilon O).value = s.min' hne := by
  classical
  obtain ⟨ha,hle⟩ := codeArgmin_spec input epsilon O score xs a h
  apply le_antisymm
  · obtain ⟨b,hb,hbv⟩ := List.mem_map.mp ((hm _).mpr (Finset.min'_mem s hne))
    exact hbv ▸ hle b hb
  · apply Finset.min'_le
    exact (hm _).mp (List.mem_map.mpr ⟨a,ha,rfl⟩)

variable [IsRealClosed K]
def commonValuesProgram (w : WeightedData (CoefficientCode n)) : List (Code n) :=
  (spectrumProgram input epsilon O w).map (valueCode (liftWeighted w))

theorem commonValuesProgram_correct (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0) (v : K) :
    v ∈ (commonValuesProgram input epsilon O w).map (fun c => (c.run input epsilon O).value) ↔
      v ∈ spectrumValues (runWeighted (K := K) input epsilon w)
        (canonicalMagnitudes (runWeighted (K := K) input epsilon w)) := by
  classical
  simp only [commonValuesProgram,List.map_map,List.mem_map,Function.comp_def,run_value,
    spectrumValues,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨runPoint input epsilon O x,
      (spectrumProgram_correct input epsilon O w hS _).mp (List.mem_map.mpr ⟨x,hx,rfl⟩),rfl⟩
  · rintro ⟨x,hx,hv⟩
    obtain ⟨c,hc,hcx⟩ := List.mem_map.mp ((spectrumProgram_correct input epsilon O w hS x).mpr hx)
    exact ⟨c,hc,by rw [hcx]; exact hv⟩

theorem commonValuesProgram_card (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0) :
    ((commonValuesProgram input epsilon O w).map (fun c => (c.run input epsilon O).value)).toFinset.card ≤ 15 := by
  classical
  have heq : ((commonValuesProgram input epsilon O w).map (fun c => (c.run input epsilon O).value)).toFinset =
      spectrumValues (runWeighted (K := K) input epsilon w)
        (canonicalMagnitudes (runWeighted (K := K) input epsilon w)) := by
    ext v
    exact List.mem_toFinset.trans (commonValuesProgram_correct input epsilon O w hS v)
  rw [heq]
  exact spectrumValues_card_le_fifteen _ _

/-- The selected record contains the literal point-coordinate and scalar codes. -/
def commonMinimumProgram (w : WeightedData (CoefficientCode n)) :
    Option (SpectrumPoint (Code n) × Code n) :=
  codeArgmin input epsilon O Prod.snd (candidateProgram input epsilon O w)

theorem commonMinimumProgram_coordinates (w : WeightedData (CoefficientCode n))
    (a : SpectrumPoint (Code n) × Code n)
    (h : commonMinimumProgram input epsilon O w = some a) :
    a.1 ∈ spectrumProgram input epsilon O w ∧ a.2 = valueCode (liftWeighted w) a.1 := by
  have ha := (codeArgmin_spec input epsilon O Prod.snd _ a h).1
  obtain ⟨x,hx,heq⟩ := List.mem_map.mp ha
  cases heq
  exact ⟨hx,rfl⟩

theorem commonMinimumProgram_exists (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0)
    (hg : (runWeighted (K := K) input epsilon w).g1 ≠ 0) :
    ∃ a, commonMinimumProgram input epsilon O w = some a := by
  obtain ⟨x,hx⟩ := spectrumCandidates_nonempty (runWeighted (K := K) input epsilon w)
    (canonicalMagnitudes _) hg
  obtain ⟨c,hc,_⟩ := List.mem_map.mp ((spectrumProgram_correct input epsilon O w hS x).mpr hx)
  have hmem : (c,valueCode (liftWeighted w) c) ∈ candidateProgram input epsilon O w :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  exact codeArgmin_exists input epsilon O Prod.snd _ (List.ne_nil_of_mem hmem)

theorem commonMinimumProgram_minimum (w : WeightedData (CoefficientCode n))
    (hS : phaseSextic (weightedP (runWeighted (K := K) input epsilon w))
      (weightedQ (runWeighted (K := K) input epsilon w)) ≠ 0)
    (hg : (runWeighted (K := K) input epsilon w).g1 ≠ 0)
    (a : SpectrumPoint (Code n) × Code n)
    (h : commonMinimumProgram input epsilon O w = some a) :
    (a.2.run input epsilon O).value =
      (spectrumValues (runWeighted (K := K) input epsilon w)
        (canonicalMagnitudes (runWeighted (K := K) input epsilon w))).min'
        (spectrumValues_nonempty _ _ hg) := by
  apply codeArgmin_minimum input epsilon O Prod.snd _ a h
  intro v
  simpa only [candidateProgram,commonValuesProgram,List.map_map,Function.comp_def]
    using commonValuesProgram_correct input epsilon O w hS v

#print axioms spectrumProgram_correct
#print axioms commonValuesProgram_correct
#print axioms codeArgmin_minimum
end W3.FiniteInput
