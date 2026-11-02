import EinsteinFull.Calculus.U4PhysicalGeneratorH2

open EinsteinRelation MeasureTheory
open scoped NNReal Topology BigOperators

namespace EinsteinFull

/-- Both physical evolutions have weak second derivatives at positive times. -/
theorem u4_physical_positive_time_H2 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ S ∈ [P, Pdag], ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∀ t : ℝ≥0, 0 < t →
      ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
        (∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) := by
  intro S hS f t ht
  obtain ⟨⟨g, hg⟩, ⟨gdag, hgdag⟩⟩ :=
    c18_physical_positive_time_generator_pairs hΛ hell hsmooth hP hPdag f t ht
  obtain ⟨C, _, hH2⟩ := u4_physical_generator_pair_H2 hΛ hell hsmooth (i := i) (ζ := ζ)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with hS | hS
  · subst S
    obtain ⟨G, H, hG, hH, _⟩ := hH2 (P t f) g (Or.inl hg)
    exact ⟨G, H, hG, hH⟩
  · subst S
    obtain ⟨G, H, hG, hH, _⟩ := hH2 (Pdag t f) gdag (Or.inr hgdag)
    exact ⟨G, H, hG, hH⟩

end EinsteinFull
