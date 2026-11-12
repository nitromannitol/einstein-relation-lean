import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.Correctors.AKMStretchedExponentialMoments

/-!
# Finite moments of the stationary AKM representatives

Source: `paper/main.tex:724-731`. These consequences of (4.5), (6.8) and
(6.14) retain the source representatives and their gradients. In (6.14)
the source quantity is squared, so its stochastic moment is `p / 2`.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The stationary scalar representative has every positive cell L² moment. -/
theorem akm_stationary_scalar_cell_moments (h45 : ScalarStationaryEstimate)
    (d : ℕ) (hd : 2 < d) (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e < 1 → ∀ (φ : Corrector P e),
        ∃ ψ : Corrector P e,
          Measurable (fun q : Coefficient d K × Vec d => ψ.potential q.1 q.2) ∧
          (∀ᵐ a ∂P, ψ.grad a =ᵐ[volume] φ.grad a) ∧
          ScalarStationary P ψ.potential ∧
          (∫ a, ⨍ x in unitCell d, ψ.potential a x ∂volume ∂P) = 0 ∧
          (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (⨍ x in unitCell d, |ψ.potential a x| ^ 2 ∂volume)) ^ p) ∂P) ≤
            ENNReal.ofReal C := by
  obtain ⟨δ, θ, hδ, hθ, hest⟩ := h45 d hd K hK
  refine ⟨2 * θ ^ p * (p / (2 + δ)) ^ (p / (2 + δ)), by positivity, ?_⟩
  intro P hP e he φ
  obtain ⟨ψ, hm, hg, hs, hz, hb⟩ := hest P hP e he φ
  refine ⟨ψ, hm, hg, hs, hz, ?_⟩
  simpa only [max_eq_left (Real.sqrt_nonneg _)] using hb.moment_le hp

/-- The literal heat-selected flux gradient has every positive local L² moment. -/
theorem akm_flux_gradient_L2_moments (h68 : FluxGradientEstimate)
    (d : ℕ) (hd : 2 ≤ d) (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e = 1 → ∀ (φ : Corrector P e),
        Nonempty (FluxCorrector φ) ∧ ∀ (S : FluxCorrector φ) (j k : Fin d),
          (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) ^ p) ∂P) ≤
            ENNReal.ofReal C := by
  obtain ⟨δ, θ, hδ, hθ, hest⟩ := h68 d hd K hK
  refine ⟨2 * θ ^ p * (p / (2 + δ)) ^ (p / (2 + δ)), by positivity, ?_⟩
  intro P hP e he φ
  obtain ⟨hne, hb⟩ := hest P hP e he φ
  refine ⟨hne, ?_⟩
  intro S j k
  simpa only [max_eq_left (Real.sqrt_nonneg _)] using (hb S j k).moment_le hp

/-- The squared source estimate (6.14) gives moments of the unsquared
cell L² norm, while retaining the stationary, zero-mean flux representative. -/
theorem akm_stationary_flux_cell_moments (h614 : FluxStationaryEstimate)
    (d : ℕ) (hd : 2 < d) (K p : ℝ) (hK : 1 < K) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Measure (Coefficient d K)), LawHypotheses P →
      ∀ (e : Vec d), euclideanNorm e = 1 → ∀ (φ : Corrector P e)
        (S : FluxCorrector φ), ∃ T : FluxCorrector φ,
          (∀ᵐ a ∂P, ∀ j k, T.grad a j k =ᵐ[volume] S.grad a j k) ∧
          (∀ j k, ScalarStationary P (fun a x => T.potential a x j k)) ∧
          (∀ j k, (∫ a, ⨍ x in unitCell d, T.potential a x j k ∂volume ∂P) = 0) ∧
          (∫⁻ a, ENNReal.ofReal ((Real.sqrt
            (⨍ x in unitCell d, frobeniusNorm (T.potential a x) ^ 2 ∂volume)) ^ p) ∂P) ≤
            ENNReal.ofReal C := by
  obtain ⟨δ, θ, hδ, hθ, hest⟩ := h614 d hd K hK
  refine ⟨2 * θ ^ (p / 2) * ((p / 2) / (2 + δ)) ^ ((p / 2) / (2 + δ)),
    by positivity, ?_⟩
  intro P hP e he φ S
  obtain ⟨T, hg, hs, hz, hb⟩ := hest P hP e he φ S
  refine ⟨T, hg, hs, hz, ?_⟩
  have hnonneg (a : Coefficient d K) :
      0 ≤ ⨍ x in unitCell d, frobeniusNorm (T.potential a x) ^ 2 ∂volume :=
    integral_nonneg fun _ => sq_nonneg _
  have h := hb.moment_le (show 0 < p / 2 by positivity)
  simp_rw [max_eq_left (hnonneg _), Real.rpow_div_two_eq_sqrt _ (hnonneg _)] at h
  exact h

end EinsteinRelation.Correctors
