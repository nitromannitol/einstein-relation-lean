import EinsteinFull.Calculus.ComplexCommonTemporalSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport

/-!
# The actual centering source and its temporal mean balance

Constant testing of the full generator graph identifies the derivative of the
mean distributionally, including the integrable gradient singularity at zero.
The source uses the actual anisotropic coefficient column and arbitrary complex
force. Subtracting the mean preserves the actual horizontal gradient.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

private def meanCLM {d : ℕ} (μ : Measure (FieldPair d)) [IsFiniteMeasure μ] :
    Lp ℂ 2 μ →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2 (Lp.const 2 μ 1)

private theorem meanCLM_apply {d : ℕ} (μ : Measure (FieldPair d))
    [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) : meanCLM μ f = ∫ ω, f ω ∂μ := by
  unfold meanCLM
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℂ)] with ω hω
  simp only [hω, Function.const_apply, ContinuousLinearMap.mul_apply', one_mul]

/-- Expectation commutes with a genuine Bochner integral of complex L2 classes. -/
theorem integral_complexL2_integral {d : ℕ} (μ : Measure (FieldPair d))
    [IsFiniteMeasure μ] {u : ℝ → Lp ℂ 2 μ} {ν : Measure ℝ} (hu : Integrable u ν) :
    (∫ ω, (∫ s, u s ∂ν) ω ∂μ) = ∫ s, (∫ ω, u s ω ∂μ) ∂ν := by
  simpa only [meanCLM_apply] using ((meanCLM μ).integral_comp_comm hu).symm

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- The literal scalar source removed when centering the actual forward orbit.
The positive-time gradient is extended by zero for nonpositive times. -/
def IsComplexEnvironmentSemigroup.centeringSource
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) : ℂ :=
  ζ * (∫ ω, ∑ j, (ω.1 0 j i : ℂ) * (hP.gradientOrbit f s) j ω ∂reducedLaw Q)

private theorem centeringSource_eq
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) :
    hP.centeringSource f s = ζ * meanCLM (reducedLaw Q)
      (complexForceDrift Q i (hP.gradientOrbit f s)) := by
  rw [IsComplexEnvironmentSemigroup.centeringSource, meanCLM_apply,
    integral_congr_ae (complexForceDrift_coe Q i (hP.gradientOrbit f s))]

/-- The actual centering source is integrable on every finite positive window,
without an initial gradient or generator-domain hypothesis. -/
theorem IsComplexEnvironmentSemigroup.integrableOn_centeringSource
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IntegrableOn (hP.centeringSource f) (Icc (0 : ℝ) (t : ℝ)) := by
  have hi := ((meanCLM (reducedLaw Q)).comp (complexForceDrift Q i)).integrable_comp
    (hP.integrableOn_gradientOrbit f t)
  change Integrable (fun s => hP.centeringSource f s) _
  simp_rw [centeringSource_eq]
  exact hi.const_mul ζ

/-- Constant testing and temporal integration by parts give the actual source
balance, with the sign and force factor retained. -/
theorem IsComplexEnvironmentSemigroup.timeTest_mean_balance
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    (∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
      (∫ ω, P s.toNNReal f ω ∂reducedLaw Q)) =
      -(∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * hP.centeringSource f s) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hg := hP.generator_timeTest_allData f η η' hη hη' t hzero ht
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hg
  obtain ⟨H, hH, hm⟩ := hg.integral_eq
  have hHe := hH.unique (hP.weighted_integral_orbit_gradient f η hηc t)
  subst H
  have hu := (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)).continuousOn_smul
    hη'.continuousOn isCompact_Icc
  have hgrad := (hP.integrableOn_gradientOrbit f t).continuousOn_smul
    hηc.continuousOn isCompact_Icc
  let G := ∫ s in Icc (0 : ℝ) (t : ℝ), η s • hP.gradientOrbit f s
  have hG (j : Fin d) : G j =
      ∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j := by
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integral_comp_comm hgrad).symm
  have hl : (∫ ω, (-(∫ s in Icc (0 : ℝ) (t : ℝ), η' s • P s.toNNReal f)) ω
      ∂reducedLaw Q) =
      -(∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
        (∫ ω, P s.toNNReal f ω ∂reducedLaw Q)) := by
    rw [← meanCLM_apply, map_neg, ← (meanCLM (reducedLaw Q)).integral_comp_comm hu]
    simp only [← meanCLM_apply, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_eq_mul]
    rfl
  have hr : ζ * (∫ ω, ∑ j, (ω.1 0 j i : ℂ) *
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • (hP.gradientOrbit f s) j) ω ∂reducedLaw Q) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * hP.centeringSource f s := by
    simp_rw [← hG]
    rw [← integral_congr_ae (complexForceDrift_coe Q i G), ← meanCLM_apply]
    change ζ * (((meanCLM (reducedLaw Q)).comp (complexForceDrift Q i)) G) = _
    rw [← ((meanCLM (reducedLaw Q)).comp (complexForceDrift Q i)).integral_comp_comm hgrad,
      ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun s => by
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, smul_eq_mul, centeringSource_eq,
        ContinuousLinearMap.comp_apply]
      exact mul_left_comm ζ (η s : ℂ) _
  rw [hl, hr] at hm
  linear_combination -hm

/-- Centering a positive-time orbit changes no actual horizontal derivative. -/
theorem IsComplexEnvironmentSemigroup.centered_gradientOrbit_spec
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {s : ℝ} (hs : 0 < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P s.toNNReal f)) (hP.gradientOrbit f s) := by
  intro j
  have he (t : ℝ) :
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j)
        (centeredComplexLp Q (P s.toNNReal f)) - centeredComplexLp Q (P s.toNNReal f) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j)
        (P s.toNNReal f) - P s.toNNReal f := by
    change complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j)
      (P s.toNNReal f - Lp.const 2 (reducedLaw Q) _) -
        (P s.toNNReal f - Lp.const 2 (reducedLaw Q) _) = _
    rw [map_sub, complexTranslation_const]
    abel
  unfold HasComplexHorizontalDerivative
  simp_rw [he]
  exact hP.gradientOrbit_spec f hs j

end EinsteinFull
