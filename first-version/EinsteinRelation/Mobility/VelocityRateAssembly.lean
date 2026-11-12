import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinRelation.Mobility.DriftWeakDivergence
import EinsteinRelation.Density.LaplaceDensityExistence
import EinsteinRelation.Clock.CentredClockField

/-! # The velocity rate from the Abel limit and the resolvent rate

Source: `paper/main.tex` 1102-1159. `velocityRateStep_of_steps` proves `VelocityRateStep`
(`eq.reduced-velocity-rate`) from `VelocityAbelStep` (the Abel limit of the drift) and
`VelocityResolventRateStep` (`eq.velocity-resolvent-rate`), with the weak divergence `cdiv i` of
the column `a e_i` and Laplace densities `ρ_s` from `exists_reducedLaplaceDensity_of_gmp`.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation

/-- **`VelocityRateStep`** from the Abel limit and the resolvent rate. -/
theorem velocityRateStep_of_steps (hAbel : VelocityAbelStep) (hRes : VelocityResolventRateStep) :
    VelocityRateStep := by
  intro d hd Λ₀ r₀
  obtain ⟨C, lamStar, hls, hls1, hR⟩ := hRes d hd Λ₀ r₀
  refine ⟨d * C, lamStar, hls, hls1, fun Q P' hP' lam hl0 hl v hv => ?_⟩
  have hl1 : lam ≤ 1 := hl.trans hls1
  have hQ := Clock.isStationary_reducedReferenceLaw Q
  have hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw (P' lam)) := hP' lam hl0.le hl1
  have hprob := isProbabilityMeasure_of_isGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam
    hl0.le hl1 (originLaw (P' lam)) hGMP
  have hex : ∀ s : {r : ℝ // 0 < r}, ∃ rho : FieldPair d → ℝ,
      Carriers.IsReducedLaplaceDensity Q.measure (P' lam) hprob s rho := fun s =>
    exists_reducedLaplaceDensity_of_gmp hd Q hl0 hl1 (P' lam) hprob hGMP s
  choose rhoS hrhoS using hex
  set rhoOf : ℝ → FieldPair d → ℝ := fun s => if hs : 0 < s then rhoS ⟨s, hs⟩ else 0 with hrdef
  have hrho : ∀ s : {r : ℝ // 0 < r},
      Carriers.IsReducedLaplaceDensity Q.measure (P' lam) hprob s (rhoOf s.1) := by
    intro s
    have e : rhoOf s.1 = rhoS s := by simp only [hrdef, dif_pos s.2]
    rw [e]
    exact hrhoS s
  have hdiv := fun i : Fin d => DriftH5.hasWeakHorizontalDivergence_reducedColumn Q hQ i
  have hK : ∀ i : Fin d, ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ lam ^ 2 →
      |(∫ ω, rhoOf s ω * ((1 / 2 : ℝ) * DriftH5.cdiv i ω + lam * (ω.1 0) (firstIdx hd) i)
          ∂(Carriers.reducedReferenceLaw Q)) - lam * abar Q (firstIdx hd) i| ≤
        C * lam ^ 2 + C * s * K := fun i =>
    hR Q P' hP' lam hl0 hl hQ i (DriftH5.cdiv i) (hdiv i) hprob rhoOf hrho
  choose K hKb using hK
  have hlim : ∀ i : Fin d, Tendsto (fun s : ℝ => ∫ ω, rhoOf s ω *
      ((1 / 2 : ℝ) * DriftH5.cdiv i ω + lam * (ω.1 0) (firstIdx hd) i)
        ∂(Carriers.reducedReferenceLaw Q)) (𝓝[>] 0) (𝓝 (v i)) := fun i =>
    hAbel d hd Λ₀ r₀ Q P' hP' lam hl0 hl1 v hv hQ i (DriftH5.cdiv i) (hdiv i) hprob rhoOf hrho
  have h := velocity_rate_of_component_rates hd Q hl0 v
    (fun i s => ∫ ω, rhoOf s ω * ((1 / 2 : ℝ) * DriftH5.cdiv i ω + lam * (ω.1 0) (firstIdx hd) i)
      ∂(Carriers.reducedReferenceLaw Q)) K hlim hKb
  calc euclideanNorm (lam⁻¹ • v - abarE1 hd Q) ≤ d * (C * lam) := h
    _ = d * C * lam := by ring

end EinsteinRelation
