import EinsteinRelation.Correctors.AKMCoefficientFactorOrbits
import EinsteinRelation.Correctors.CoefficientScalarApproximations

/-!
# Rapid scalar orbit factors on the raw coefficient law

Source: `paper/main.tex:693-702`. The prescribed scalar H¹ approximants
are retained together with their coefficient factors and their physical
spatial identities. This preserves the approximation index for the maximal
gradient-error and scalar-orbit sublinearity arguments.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3

theorem exists_akm_rapid_scalar_orbit_factors {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ f : ℕ → horizontalH1 (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q),
    ∃ u : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ,
    ∃ g : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      (∀ n, Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => u n p.1 p.2) ∧
        Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g n p.1 p.2)) ∧
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      (∀ n, ‖horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) (f n) - (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))‖ ≤ (1 / 2 : ℝ)^n) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q,
        let a := project (r₀ := r₀) Q.ellipticity_parameter ω
        (∀ n, (fun x => u n a x) =ᵐ[volume] (fun x =>
          (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (translate x (reduce ω.1)))) ∧
        (∀ n, (fun x => g n a x) =ᵐ[volume] (fun x =>
          horizontalEuclideanGradient (reducedEnvironmentLaw Q)
            (reducedEnvironmentLaw_stationary Q) (f n) (translate x (reduce ω.1)))) ∧
        (fun x => G a x) =ᵐ[volume] (fun x => (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))) := by
  obtain ⟨f, u, g, hm, hu, hg, hrapid⟩ := exists_canonical_coefficient_scalar_approximation Q i
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  obtain ⟨F, hF, hFG⟩ := exists_coefficient_factor_of_canonicalGradient Q i
  let H := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  let D := fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) (f n)
  let U := fun n => akmUnscaledCoefficientFactor r₀ R (u n)
  let V := fun n => akmUnscaledCoefficientFactor r₀ R (g n)
  let W := akmUnscaledCoefficientFactor r₀ R F
  refine ⟨f, U, V, W, fun n => ⟨measurable_akmUnscaledCoefficientFactor r₀ R hR (u n)
    (hm n).1.measurable, measurable_akmUnscaledCoefficientFactor r₀ R hR (g n)
      (hm n).2.measurable⟩, measurable_akmUnscaledCoefficientFactor r₀ R hR F hF.measurable,
    hrapid, ?_⟩
  have hscalar := ae_all_iff.mpr fun (n : ℕ) => ae_akmUnscaledCoefficientFactor_project Q R hReq
    (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (Lp.stronglyMeasurable _).measurable
    (u n) (hm n).1.measurable (hu n)
  have hvector := ae_all_iff.mpr fun (n : ℕ) => ae_akmUnscaledCoefficientFactor_project Q R hReq
    (D n) (Lp.stronglyMeasurable _).measurable (g n) (hm n).2.measurable (hg n)
  have hlimit := ae_akmUnscaledCoefficientFactor_project Q R hReq H
    (Lp.stronglyMeasurable _).measurable F hF.measurable hFG
  filter_upwards [hscalar, hvector, hlimit] with ω huω hgω hHω
  exact ⟨fun n => Filter.EventuallyEq.symm (huω n), fun n => Filter.EventuallyEq.symm (hgω n), Filter.EventuallyEq.symm hHω⟩

end EinsteinRelation.Correctors
