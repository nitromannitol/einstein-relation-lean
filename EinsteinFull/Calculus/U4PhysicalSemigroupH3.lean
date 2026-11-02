import EinsteinFull.Calculus.U4PhysicalSemigroupH2
import EinsteinFull.Calculus.U4PhysicalGeneratorH3

open EinsteinRelation MeasureTheory
open scoped NNReal Topology BigOperators

namespace EinsteinFull

/-- At positive times both actual evolutions admit two successive generator
pairs, with weak second derivatives for each of the first two entries. -/
theorem u4_physical_positive_time_chain_H2 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1) (hsmooth : IsSmoothWithBounds M ω)
    (hP : IsPhysicalComplexSemigroup ω.1 i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag) :
    ∀ S ∈ [P, Pdag], ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∀ t : ℝ≥0, 0 < t →
    ∃ g h : Lp ℂ 2 (volume : Measure (Vec d)),
      ((IsPhysicalComplexGeneratorPair ω.1 i ζ (S t f) g ∧
          IsPhysicalComplexGeneratorPair ω.1 i ζ g h) ∨
       (IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (S t f) g ∧
          IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ g h)) ∧
      (∀ v ∈ [S t f, g],
        ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        ∃ H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalH1Graph volume (Or.inl rfl) v G ∧
          ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) := by
  intro S hS f t ht
  obtain ⟨u, v, hu, hv, hchain⟩ :=
    c18_physical_positive_time_generator_chains hΛ hell hsmooth hP hPdag 2 f t ht
  obtain ⟨C, hC, hH2⟩ := u4_physical_generator_pair_H2 hΛ hell hsmooth (i := i) (ζ := ζ)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with hS | hS
  · subst S
    have h₀ : IsPhysicalComplexGeneratorPair ω.1 i ζ (P t f) (u 1) := by
      have hc := (hchain 0).1
      change IsPhysicalComplexGeneratorPair ω.1 i ζ (u 0) (u 1) at hc
      rw [hu] at hc
      exact hc
    have h₁ : IsPhysicalComplexGeneratorPair ω.1 i ζ (u 1) (u 2) := by
      simpa using (hchain 1).1
    refine ⟨u 1, u 2, Or.inl ⟨h₀, h₁⟩, ?_⟩
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · obtain ⟨G, H, hG, hH, _⟩ := hH2 (P t f) (u 1) (Or.inl h₀)
      exact ⟨G, H, hG, hH⟩
    · obtain ⟨G, H, hG, hH, _⟩ := hH2 (u 1) (u 2) (Or.inl h₁)
      exact ⟨G, H, hG, hH⟩
  · subst S
    have h₀ : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (Pdag t f) (v 1) := by
      have hc := (hchain 0).2
      change IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v 0) (v 1) at hc
      rw [hv] at hc
      exact hc
    have h₁ : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (v 1) (v 2) := by
      simpa using (hchain 1).2
    refine ⟨v 1, v 2, Or.inr ⟨h₀, h₁⟩, ?_⟩
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · obtain ⟨G, H, hG, hH, _⟩ := hH2 (Pdag t f) (v 1) (Or.inr h₀)
      exact ⟨G, H, hG, hH⟩
    · obtain ⟨G, H, hG, hH, _⟩ := hH2 (v 1) (v 2) (Or.inr h₁)
      exact ⟨G, H, hG, hH⟩


/-- Both physical evolutions have three weak spatial derivatives at positive times. -/
theorem u4_physical_positive_time_H3 {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
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
    ∃ K : Fin d → Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (S t f) G ∧
      (∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) ∧
      (∀ j k, IsPhysicalH1Graph volume (Or.inl rfl) (H j k) (K j k)) := by
  intro S hS f t ht
  obtain ⟨g, h, hpairs, hH2⟩ :=
    u4_physical_positive_time_chain_H2 hΛ hell hsmooth hP hPdag S hS f t ht
  obtain ⟨G, H, hG, hH⟩ := hH2 (S t f) (by simp)
  obtain ⟨J, L, hJ, hL⟩ := hH2 g (by simp)
  have hpair : IsPhysicalComplexGeneratorPair ω.1 i ζ (S t f) g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (S t f) g :=
    hpairs.elim (fun hp => Or.inl hp.1) (fun hp => Or.inr hp.1)
  obtain ⟨K, hK⟩ := u4h3_generator_pair_H3 H hΛ hell hsmooth hpair hG hH hJ
  exact ⟨G, H, K, hG, hH, hK⟩

end EinsteinFull

