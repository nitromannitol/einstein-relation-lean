import EinsteinRelation.Correctors.CanonicalCoefficientMeasurability
import EinsteinRelation.Correctors.RapidGradientApproximation

/-!
# Coefficient-only scalar approximations

Source: `paper/main.tex:693-698`. Project horizontal Sobolev approximants
onto coefficient observations. The projected scalar and its full gradient
factor through coefficients, and contraction preserves the rapid error bound.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Scalar coefficient projection intertwines the full Euclidean gradient. -/
theorem coefficientProjection_horizontalH1 {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) :
    ∃ g : horizontalH1 Q hQ,
      (g : Lp ℝ 2 Q) = coefficientProjection Q ℝ (f : Lp ℝ 2 Q) ∧
      horizontalEuclideanGradient Q hQ g =
        coefficientProjection Q (EuclideanSpace ℝ (Fin d))
          (horizontalEuclideanGradient Q hQ f) := by
  obtain ⟨g, hg, hd⟩ := horizontalH1_of_commuting_operator Q hQ
    (coefficientProjection Q ℝ) (coefficientProjection_translationLp Q hQ) f
  refine ⟨g, hg, ?_⟩
  apply Lp.ext
  have hc : ∀ i : Fin d, ∀ᵐ ω ∂Q,
      horizontalEuclideanGradient Q hQ g ω i =
        coefficientProjection Q (EuclideanSpace ℝ (Fin d))
          (horizontalEuclideanGradient Q hQ f) ω i := by
    intro i
    have heq : (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 Q
        (coefficientProjection Q (EuclideanSpace ℝ (Fin d))
          (horizontalEuclideanGradient Q hQ f)) = horizontalH1Gradient Q hQ g i := by
      rw [coefficientProjection_coordinateLp, horizontalEuclideanGradient_coordinateLp, hd]
    filter_upwards [horizontalEuclideanGradient_coordinates Q hQ g i,
      (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL
        (coefficientProjection Q (EuclideanSpace ℝ (Fin d))
          (horizontalEuclideanGradient Q hQ f))] with ω h1 h2
    exact h1.trans ((congrArg (fun u : Lp ℝ 2 Q => u ω) heq).symm.trans h2)
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  ext i
  exact hω i

/-- Canonical gradients have rapidly convergent scalar Sobolev approximants
whose scalar and gradient representatives depend only on coefficients. -/
theorem exists_canonical_coefficient_scalar_approximation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ f : ℕ → horizontalH1 (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q),
      ∃ u : ℕ → CoefficientField d → ℝ,
      ∃ g : ℕ → CoefficientField d → EuclideanSpace ℝ (Fin d),
      (∀ n, StronglyMeasurable (u n) ∧ StronglyMeasurable (g n)) ∧
      (∀ n, (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) =ᵐ[reducedEnvironmentLaw Q]
        fun ω => u n ω.1) ∧
      (∀ n, horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) (f n) =ᵐ[reducedEnvironmentLaw Q]
          fun ω => g n ω.1) ∧
      ∀ n, ‖horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) (f n) - (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ ≤ (1 / 2 : ℝ)^n := by
  let μ := reducedEnvironmentLaw Q
  let hμ := reducedEnvironmentLaw_stationary Q
  let G := (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
  obtain ⟨f, hf⟩ := exists_rapid_horizontal_gradient_approximation μ hμ G
    (canonicalCorrectorGradient Q i).property
  choose k hk hgrad using fun n => coefficientProjection_horizontalH1 μ hμ (f n)
  choose u hu huf using fun n => exists_coefficient_factor_of_projection μ (f n : Lp ℝ 2 μ)
  choose g hg hgf using fun n => exists_coefficient_factor_of_projection μ
    (horizontalEuclideanGradient μ hμ (f n))
  refine ⟨k, u, g, fun n => ⟨hu n, hg n⟩, ?_, ?_, ?_⟩
  · intro n
    simpa only [← hk n] using huf n
  · intro n
    simpa only [← hgrad n] using hgf n
  · intro n
    rw [hgrad n]
    have hfix : coefficientProjection μ (EuclideanSpace ℝ (Fin d)) G = G :=
      coefficientProjection_canonicalCorrectorGradient Q i
    calc
      _ = ‖coefficientProjection μ (EuclideanSpace ℝ (Fin d))
          (horizontalEuclideanGradient μ hμ (f n) - G)‖ := by rw [map_sub, hfix]
      _ ≤ ‖horizontalEuclideanGradient μ hμ (f n) - G‖ := norm_coefficientProjection_le μ _
      _ ≤ _ := hf n

end EinsteinRelation.Correctors
