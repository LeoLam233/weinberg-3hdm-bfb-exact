import W3.InfinitesimalRootClusteringTransfer

/-! # Actual relative residue from a nonzero polynomial with infinitesimal value.
Unlike arbitrary bounded ultrapower elements, these selected elements have a
proved unique residue in the preceding non-Archimedean field.
-/
noncomputable section
namespace W3.Infinitesimal
open Filter Polynomial

/-- Root-clustering in the preceding tower field, finite-root ultrafilter selection,
and a finite minimum of root distances construct an actual unique relative residue. -/
theorem tower_relativeResidue_of_infinitesimal_polynomial (k : ℕ)
    {p : (Tower realModel k)[X]} (hp : p ≠ 0)
    {x : Extension (Tower realModel k)} {B : Tower realModel k}
    (hbound : |x| ≤ embed (Tower realModel k) B)
    (hsmall : ∀ η : Tower realModel k, 0 < η →
      |p.eval₂ (embed (Tower realModel k)).toRingHom x| < embed (Tower realModel k) η) :
    ∃ q : Tower realModel k, p.IsRoot q ∧
      HasRelativeResidue (Tower realModel k) x q := by
  apply relativeResidue_of_root_approximations (Tower realModel k) hp
  intro δ hδ
  obtain ⟨η, hη, hcluster⟩ := tower_polynomial_root_clustering k p B δ hδ
  have hsmallη := hsmall η hη
  induction x using Germ.inductionOn with
  | h g =>
    change |p.eval₂ (embed (Tower realModel k)).toRingHom
      (germRingHom (Tower realModel k) g)| < embed (Tower realModel k) η at hsmallη
    rw [polynomial_eval₂_germ] at hsmallη
    have heB : ∀ᶠ i in (extensionUltrafilter (Tower realModel k) : Filter (Tower realModel k)),
        |g i| ≤ B := Germ.coe_le.mp hbound
    have heη : ∀ᶠ i in (extensionUltrafilter (Tower realModel k) : Filter (Tower realModel k)),
        |p.eval (g i)| < η := Germ.coe_lt.mp hsmallη
    have heRoots : ∀ᶠ i in (extensionUltrafilter (Tower realModel k) : Filter (Tower realModel k)),
        ∃ q ∈ {q : Tower realModel k | p.IsRoot q}, |g i - q| < δ :=
      (heB.and heη).mono (fun i hi => hcluster (g i) hi.1 hi.2)
    obtain ⟨q, hq, heq⟩ :=
      (Ultrafilter.eventually_exists_mem_iff (p.finite_setOfPred_isRoot hp)).mp heRoots
    exact ⟨q, hq, Germ.coe_lt.mpr heq⟩

#print axioms tower_relativeResidue_of_infinitesimal_polynomial
end W3.Infinitesimal
