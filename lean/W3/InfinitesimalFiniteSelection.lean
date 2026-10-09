import W3.InfinitesimalAlgebraicPresentation

/-! # A terminating exact finite comparison selector for the algebraic residue
After a real-root oracle supplies the roots of the normalized nonzero polynomial,
this structural recursion uses only finitely many arithmetic/order comparisons.
It is equivalent to selecting the interval bounded by adjacent-root midpoints.
-/
noncomputable section
namespace W3.Infinitesimal

/-- Structural finite argmin, requiring only comparisons of the supplied scores. -/
def finiteArgmin {α β : Type*} [LinearOrder β] (score : α → β) (a : α) : List α → α
  | [] => a
  | b :: bs => let c := finiteArgmin score a bs
      if score b ≤ score c then b else c

lemma finiteArgmin_spec {α β : Type*} [LinearOrder β] (score : α → β) (a : α) (xs : List α) :
    finiteArgmin score a xs ∈ a :: xs ∧
      ∀ b ∈ a :: xs, score (finiteArgmin score a xs) ≤ score b := by
  induction xs with
  | nil => exact ⟨by simp [finiteArgmin], by simp [finiteArgmin]⟩
  | cons b bs ih =>
    simp only [finiteArgmin]
    split_ifs with h
    · refine ⟨by simp, ?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.trans (ih.2 c (by simp))
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · exact h.trans (ih.2 c (by simp [hc]))
    · refine ⟨?_, ?_⟩
      · rcases List.mem_cons.mp ih.1 with hmem | hmem
        · simp [hmem]
        · simp [hmem]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ih.2 c (by simp)
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact (le_of_not_ge h)
          · exact ih.2 c (by simp [hc])

variable (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The true relative residue is strictly closer than every different base-field value. -/
theorem relativeResidue_strictly_closest {x : Extension K} {q r : K}
    (hq : HasRelativeResidue K x q) (hqr : q ≠ r) :
    |x - embed K q| < |x - embed K r| := by
  have hd : 0 < |q - r| := abs_pos.mpr (sub_ne_zero.mpr hqr)
  have hδ : 0 < |q - r| / 3 := div_pos hd (by norm_num)
  have hsmall := hq (|q - r| / 3) hδ
  rw [map_div₀, map_ofNat, embed_abs, map_sub] at hsmall
  have htri := abs_sub_le (embed K q) x (embed K r)
  rw [abs_sub_comm (embed K q) x] at htri
  have hnonneg := abs_nonneg (x - embed K q)
  linarith

/-- Given any finite complete root enumeration containing the selected residue,
the terminating exact selector identifies it uniquely. -/
theorem finiteArgmin_relativeResidue {x : Extension K} {q a : K} {xs : List K}
    (hq : HasRelativeResidue K x q) (hmem : q ∈ a :: xs) :
    finiteArgmin (fun r => |x - embed K r|) a xs = q := by
  have hs := (finiteArgmin_spec (fun r => |x - embed K r|) a xs).2 q hmem
  by_contra h
  exact (relativeResidue_strictly_closest K hq (Ne.symm h)).not_ge hs

/-- Midpoint cuts are exact too: no rational tolerance or numerical approximation
is needed to distinguish two distinct possible residues. -/
theorem relativeResidue_midpoint {x : Extension K} {q r : K}
    (hq : HasRelativeResidue K x q) (hqr : q < r) :
    x < embed K ((q + r) / 2) := by
  apply relativeResidue_lt K hq
  linarith

/-- Each nontrivial distance comparison in the finite selector is precisely
an adjacent-style midpoint comparison. Equal roots simply give a harmless tie. -/
theorem distance_comparison_midpoint {x a b : K} (hab : a < b) :
    (|x - a| ≤ |x - b| ↔ x ≤ (a + b) / 2) := by
  rw [← sq_le_sq₀ (abs_nonneg (x - a)) (abs_nonneg (x - b)), sq_abs, sq_abs]
  constructor
  · intro h
    by_contra hnot
    have hpos : 0 < (b - a) * (2 * x - a - b) := by
      apply mul_pos (sub_pos.mpr hab)
      linarith
    nlinarith
  · intro h
    have hnonneg : 0 ≤ (b - a) * (a + b - 2 * x) := by
      apply mul_nonneg (sub_nonneg.mpr hab.le)
      linarith
    nlinarith

#print axioms finiteArgmin_relativeResidue
end W3.Infinitesimal
