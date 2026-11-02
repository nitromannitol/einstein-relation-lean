import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-! # The second moment of the canonical corrector gradient

The exponent-two case of the gradient assertion in Lemma 5.1
(`paper/main.tex:704-713`) follows directly from ellipticity and the variational
identity. No stochastic homogenization estimate is needed for this case.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

private theorem euclideanSq_ofLp_eq_norm_sq {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) : euclideanSq u.ofLp = ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

private theorem euclideanNorm_ofLp_eq_norm {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) : euclideanNorm u.ofLp = ‖u‖ := by
  rw [euclideanNorm, euclideanSq_ofLp_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Pointwise ellipticity integrated on the reduced environment space.
Source: `paper/main.tex:693-697`, the energy pairing of the corrector equation. -/
theorem reducedOriginCoefficientAction_coercive {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * ‖u‖ ^ 2 ≤
      inner ℝ u (reducedOriginCoefficientAction Q u) := by
  have hsq : Integrable (fun ω => ‖u ω‖ ^ 2) (reducedEnvironmentLaw Q) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) u u
  have henergy := L2.integrable_inner (𝕜 := ℝ) u (reducedOriginCoefficientAction Q u)
  have hpoint : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (Real.exp (2 * Λ₀) * Λ₀)⁻¹ * ‖u ω‖ ^ 2 ≤
        inner ℝ (u ω) (reducedOriginCoefficientAction Q u ω) := by
    filter_upwards [ae_reducedEnvironmentLaw_origin_elliptic Q,
      reducedOriginCoefficientAction_coeFn Q u] with ω hω hA
    have h := ((hω 0).2 (u ω).ofLp).1
    rw [euclideanSq_ofLp_eq_norm_sq] at h
    convert h using 1
    simp only [dot, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hA]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hnorm : ‖u‖ ^ 2 = ∫ ω, ‖u ω‖ ^ 2 ∂reducedEnvironmentLaw Q := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hnorm, ← integral_const_mul, L2.inner_def]
  exact integral_mono_ae (hsq.const_mul _) henergy hpoint

/-- A uniform deterministic `L²` bound for the canonical gradient. This proves the
energy estimate needed for the exponent-two part of `paper/main.tex:712`. -/
theorem norm_canonicalCorrectorGradient_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ‖(canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ ≤
        (Real.exp (2 * Λ₀) * Λ₀) ^ 2 := by
  set K := Real.exp (2 * Λ₀) * Λ₀
  set G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hK : 0 < K := correctorEllipticityConstant_pos Q
  have hconst : ‖correctorAffineField Q i‖ = 1 := by
    rw [correctorAffineField,
      Lp.norm_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) (by norm_num),
      probReal_univ, Real.one_rpow, mul_one]
    simp [correctorUnitVector]
  have hvar := correctorEnergyForm_canonical_variational Q i (canonicalCorrectorGradient Q i)
  have henergy : inner ℝ G (reducedOriginCoefficientAction Q G) =
      -inner ℝ (reducedOriginCoefficientAction Q (correctorAffineField Q i)) G := hvar
  have hupper : inner ℝ G (reducedOriginCoefficientAction Q G) ≤ K * ‖G‖ := by
    rw [henergy, ← inner_neg_left]
    calc inner ℝ (-reducedOriginCoefficientAction Q (correctorAffineField Q i)) G
        ≤ ‖-reducedOriginCoefficientAction Q (correctorAffineField Q i)‖ * ‖G‖ :=
          real_inner_le_norm _ _
      _ ≤ (K * ‖correctorAffineField Q i‖) * ‖G‖ := by
          rw [norm_neg]
          exact mul_le_mul_of_nonneg_right (norm_reducedOriginCoefficientAction_le Q _)
            (norm_nonneg _)
      _ = K * ‖G‖ := by rw [hconst, mul_one]
  have hlow := (reducedOriginCoefficientAction_coercive Q G).trans hupper
  change K⁻¹ * ‖G‖ ^ 2 ≤ K * ‖G‖ at hlow
  have hsq : ‖G‖ ^ 2 ≤ K ^ 2 * ‖G‖ := by
    have h := mul_le_mul_of_nonneg_left hlow hK.le
    rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at h
    nlinarith only [h]
  rcases eq_or_lt_of_le (norm_nonneg G) with hzero | hpos
  · rw [← hzero]
    exact sq_nonneg K
  · nlinarith only [hsq, hpos]

/-- The exponent-two instance of the gradient assertion in Lemma 5.1, with the
same representative and measure as `CorrectorGradientMoments`
(`paper/main.tex:704-713`). The constant precedes the environment law. -/
theorem canonicalCorrectorGradient_secondMoment_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∫⁻ ω, ENNReal.ofReal
        (euclideanNorm
          ((StationarySpatialRealization.spatialRealization (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            ((0 : Vec d), ω)).ofLp) ^ (2 : ℝ))
      ∂reducedEnvironmentLaw Q ≤ ENNReal.ofReal ((Real.exp (2 * Λ₀) * Λ₀) ^ 4) := by
  set G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have hsq : Integrable (fun ω => ‖G ω‖ ^ 2) (reducedEnvironmentLaw Q) := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) G G
  have hnorm : (∫ ω, ‖G ω‖ ^ 2 ∂reducedEnvironmentLaw Q) = ‖G‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simp only [StationarySpatialRealization.spatialRealization, translate_zero,
    euclideanNorm_ofLp_eq_norm, Real.rpow_two]
  rw [← ofReal_integral_eq_lintegral_ofReal hsq (ae_of_all _ fun ω => sq_nonneg _), hnorm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖G‖ ^ 2 ≤ ((Real.exp (2 * Λ₀) * Λ₀) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg G) (norm_canonicalCorrectorGradient_le Q i) 2
    _ = (Real.exp (2 * Λ₀) * Λ₀) ^ 4 := by ring

end EinsteinRelation.Correctors

