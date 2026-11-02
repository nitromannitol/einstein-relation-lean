import EinsteinRelation.Correctors.AKMCoefficientFactorOrbits
import EinsteinRelation.Correctors.CoefficientScalarApproximations
import EinsteinRelation.Correctors.SamplewiseFromRapidApproximations

/-!
# Scalar AKM approximants on the actual project image

Source: `paper/main.tex:693-702`. Projected scalar Sobolev approximants
factor through coefficients. Their reconstructed raw-carrier functions
have the actual samplewise weak gradients and converge locally to the
canonical gradient under the physical project map.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport ReductionImageV3 StationarySpatialRealization

/-- The source side of raw-carrier transport consists of actual jointly
measurable functions and genuine scalar weak potentials, with all-space
canonical identification and local spatial L² convergence. -/
theorem exists_akm_scalar_approximation_pullback {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ u : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ,
    ∃ g : ℕ → Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
    ∃ G : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      (∀ n, Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => u n p.1 p.2) ∧
        Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g n p.1 p.2)) ∧
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G p.1 p.2) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q,
        let a := project (r₀ := r₀) Q.ellipticity_parameter ω
        (∀ n, HasWeakGradient Set.univ (u n a) (fun x => (g n a x).ofLp)) ∧
        (∀ n (K : Set (Vec d)), IsCompact K →
          MemLp (u n a) 2 (volume.restrict K) ∧ MemLp (g n a) 2 (volume.restrict K)) ∧
        (∀ K : Set (Vec d), IsCompact K → MemLp (G a) 2 (volume.restrict K)) ∧
        (∀ K : Set (Vec d), IsCompact K → Tendsto
          (fun n => ∫ x in K, ‖g n a x - G a x‖ ^ 2) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂(volume : Measure (Vec d)), G a x = (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x (reduce ω.1)) := by
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
  refine ⟨U, V, W, fun n => ⟨measurable_akmUnscaledCoefficientFactor r₀ R hR (u n)
    (hm n).1.measurable, measurable_akmUnscaledCoefficientFactor r₀ R hR (g n)
      (hm n).2.measurable⟩, measurable_akmUnscaledCoefficientFactor r₀ R hR F hF.measurable, ?_⟩
  have hs := samplewise_scalar_gradient_approximation_of_rapid
    (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) H f hrapid
  have hlocD := ae_all_iff.mpr fun n =>
    ae_spatialRealization_memLp_on_all_compacts (reducedEnvironmentLaw_stationary Q) (D n)
  have hlocH := ae_spatialRealization_memLp_on_all_compacts
    (reducedEnvironmentLaw_stationary Q) H
  have hsource : ∀ᵐ ω ∂physicalReferenceLaw Q,
      ((∀ n, HasWeakGradient Set.univ
        (fun x => (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (translate x (reduce ω.1)))
        (fun x => (D n (translate x (reduce ω.1))).ofLp)) ∧
       (∀ n K, IsCompact K → MemLp
        (fun x => (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (translate x (reduce ω.1)))
          2 (volume.restrict K)) ∧
       ∀ K, IsCompact K → Tendsto (fun n => ∫ x in K,
         ‖D n (translate x (reduce ω.1)) - H (translate x (reduce ω.1))‖ ^ 2) atTop (𝓝 0)) ∧
      (∀ n K, IsCompact K → MemLp (fun x => D n (translate x (reduce ω.1))) 2 (volume.restrict K)) ∧
      (∀ K, IsCompact K → MemLp (fun x => H (translate x (reduce ω.1))) 2 (volume.restrict K)) := by
    have h := ae_of_ae_map Probability.measurable_reduce.aemeasurable ((hs.and hlocD).and hlocH)
    rw [← physicalReferenceLaw_forget Q] at h
    simpa only [and_assoc] using ae_of_ae_map measurable_subtype_coe.aemeasurable h
  have hscalar := ae_all_iff.mpr fun n => ae_akmUnscaledCoefficientFactor_project Q R hReq
    (f n : Lp ℝ 2 (reducedEnvironmentLaw Q)) (Lp.stronglyMeasurable _).measurable
    (u n) (hm n).1.measurable (hu n)
  have hvector := ae_all_iff.mpr fun n => ae_akmUnscaledCoefficientFactor_project Q R hReq
    (D n) (Lp.stronglyMeasurable _).measurable (g n) (hm n).2.measurable (hg n)
  have hlimit := ae_akmUnscaledCoefficientFactor_project Q R hReq H
    (Lp.stronglyMeasurable _).measurable F hF.measurable hFG
  filter_upwards [hsource, hscalar, hvector, hlimit] with ω hω huω hgω hHω
  refine ⟨?_, ?_, ?_, ?_, Filter.EventuallyEq.symm hHω⟩
  · intro n j
    apply (hω.1.1 n j).congr_ae
    · simpa only [Measure.restrict_univ, U] using! huω n
    · simpa only [Measure.restrict_univ, V] using!
        (hgω n).mono fun x hx => congrArg (fun z => z.ofLp j) hx
  · intro n K hK
    exact ⟨(memLp_congr_ae (ae_restrict_of_ae (huω n))).mp (hω.1.2.1 n K hK),
      (memLp_congr_ae (ae_restrict_of_ae (hgω n))).mp (hω.2.1 n K hK)⟩
  · intro K hK
    exact (memLp_congr_ae (ae_restrict_of_ae hHω)).mp (hω.2.2 K hK)
  · intro K hK
    have he (n : ℕ) : (∫ x in K,
        ‖V n (project (r₀ := r₀) Q.ellipticity_parameter ω) x -
          W (project (r₀ := r₀) Q.ellipticity_parameter ω) x‖ ^ 2) =
        ∫ x in K, ‖D n (translate x (reduce ω.1)) - H (translate x (reduce ω.1))‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hgω n), ae_restrict_of_ae hHω] with x hx hy
      dsimp only [V, W]
      rw [← hx, ← hy]
    simpa only [he] using hω.1.2.2 K hK

end EinsteinRelation.Correctors
