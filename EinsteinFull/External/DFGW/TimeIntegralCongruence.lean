import EinsteinFull.External.DFGW.JointIntegrability

/-! # Time integrals of almost everywhere equal observables

Stationarity transports almost everywhere identities on the state space to almost every
trajectory and almost every time in a fixed bounded interval.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Almost everywhere equal state observables have equal time integrals on almost every trajectory. -/
theorem ae_time_integral_congr (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {f g : S → ℝ} (hfg : f =ᵐ[μ] g) {t : ℝ} (ht : 0 ≤ t) :
    (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, f (η u)) =ᵐ[P]
      fun η => ∫ u in (0 : ℝ)..t, g (η u) := by
  let : IsProbabilityMeasure P := hP.probability
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 t)
  have hev : Measurable (fun z : ℝ × C(ℝ, S) => z.2 z.1) := by
    have hc : Continuous (fun z : C(ℝ, S) × ℝ => z.1 z.2) := continuous_eval
    exact hc.measurable.comp measurable_swap
  have hq : Measure.QuasiMeasurePreserving (fun z : ℝ × C(ℝ, S) => z.2 z.1)
      (ν.prod P) μ := by
    refine ⟨hev, Measure.AbsolutelyContinuous.mk ?_⟩
    intro A hA hAμ
    rw [Measure.map_apply hev hA, Measure.prod_apply (hev hA)]
    have hz : (fun u : ℝ => P (Prod.mk u ⁻¹' ((fun z : ℝ × C(ℝ, S) => z.2 z.1) ⁻¹' A))) = 0 := by
      funext u
      have hm := Measure.map_apply (μ := P) (continuous_eval_const u).measurable hA
      rw [hP.marginal, hAμ] at hm
      change P ((fun η : C(ℝ, S) => η u) ⁻¹' A) = 0
      exact hm.symm
    rw [hz, lintegral_zero_fun]
  have hp : ∀ᵐ z ∂(P.prod ν), f (z.1 z.2) = g (z.1 z.2) := by
    have h := (Measure.measurePreserving_swap (μ := P) (ν := ν)).quasiMeasurePreserving.ae (hq.ae hfg)
    exact h
  filter_upwards [Measure.ae_ae_of_ae_prod hp] with η hη
  simp only [intervalIntegral.integral_of_le ht]
  exact integral_congr_ae hη

end EinsteinFull.External.DFGW
