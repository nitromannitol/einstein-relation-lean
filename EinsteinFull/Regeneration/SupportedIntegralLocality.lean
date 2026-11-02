import EinsteinRelation.Probability.FiniteHistoryStopping
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# From supported event locality to integral locality

Restrict the actual law to the support of a test, on its exact sigma algebra.
Event locality makes these restricted laws a kernel for the local parameter
sigma algebra. Integration against this kernel then gives integral locality.
The ambient law is only trimmed; its path, endpoint and coin objects do not
change. No integrability assumption is needed for this measurable transfer.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration

/-- Locality of all measurable events supported in `B` implies locality of
the integral of every measurable test supported there. The law may originally
live on a larger sigma algebra than the one seen by the test. -/
theorem measurable_integral_of_supported_events
    {Ω S : Type*} [mΩ : MeasurableSpace Ω] [m₀ : MeasurableSpace S]
    (m : MeasurableSpace S) (hm : m ≤ m₀) (μ : Ω → @Measure S m₀) (B : Set S)
    (hlocal : ∀ U : Set S, MeasurableSet[m] U → U ⊆ B →
      Measurable (fun ω => μ ω U))
    (F : S → ℝ) (hF : Measurable[m] F) (hsupport : Function.support F ⊆ B) :
    Measurable (fun ω => letI : MeasurableSpace S := m₀; ∫ z, F z ∂μ ω) := by
  have hs : MeasurableSet[m] (Function.support F) := measurableSet_support hF
  let κ : @Kernel Ω S mΩ m :=
    { toFun := fun ω => @Measure.restrict S m ((μ ω).trim hm) (Function.support F)
      measurable' := by
        apply Measure.measurable_of_measurable_coe
        intro U hU
        have h := hlocal (U ∩ Function.support F) (hU.inter hs)
          (fun _ hz => hsupport hz.2)
        simpa only [Measure.restrict_apply hU, trim_measurableSet_eq hm (hU.inter hs)]
          using h }
  have hκ := hF.stronglyMeasurable.integral_kernel (κ := κ)
  have heq (ω : Ω) : (letI : MeasurableSpace S := m₀; ∫ z, F z ∂μ ω) =
      (letI : MeasurableSpace S := m; ∫ z, F z ∂κ ω) := by
    rw [integral_trim hm hF.stronglyMeasurable]
    letI : MeasurableSpace S := m
    change (∫ z, F z ∂(μ ω).trim hm) =
      ∫ z in Function.support F, F z ∂(μ ω).trim hm
    rw [← integral_indicator hs]
    simp only [Set.indicator_support]
  convert hκ.measurable using 1
  exact funext heq

/-- The supported-event transfer for the literal closed finite path/coin
history. The endpoint and all coins strictly before `n` are retained. -/
theorem measurable_integral_finiteHistory_of_local_events
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    (μ : Ω → Measure (EinsteinRelation.Regeneration.CoupledSample d))
    (B : Set (EinsteinRelation.Regeneration.CoupledSample d))
    (hlocal : ∀ U, MeasurableSet[EinsteinRelation.Regeneration.finiteHistorySigma Δ n] U →
      U ⊆ B → Measurable (fun ω => μ ω U))
    (F : EinsteinRelation.Regeneration.CoupledSample d → ℝ)
    (hF : Measurable[EinsteinRelation.Regeneration.finiteHistorySigma Δ n] F)
    (hsupport : Function.support F ⊆ B) :
    Measurable (fun ω => ∫ z, F z ∂μ ω) :=
  measurable_integral_of_supported_events _
    (EinsteinRelation.Probability.finiteHistorySigma_le Δ n) μ B hlocal F hF hsupport

/-- A test of the exact time-zero history is constant under any probability
law starting at `x`. No coin is visible in this sigma algebra. -/
theorem integral_zero_history_eq {d : ℕ} (Δ : ℝ≥0)
    (μ : Measure (EinsteinRelation.Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (x : EinsteinRelation.Vec d) (hstart : ∀ᵐ z ∂μ, z.1 0 = x)
    (F : EinsteinRelation.Regeneration.CoupledSample d → ℝ)
    (hF : Measurable[EinsteinRelation.Regeneration.finiteHistorySigma Δ 0] F) :
    (∫ z, F z ∂μ) = F (⟨fun _ => x, continuous_const⟩, fun _ => false) := by
  let z₀ : EinsteinRelation.Regeneration.CoupledSample d :=
    (⟨fun _ => x, continuous_const⟩, fun _ => false)
  have hconst : ∀ᵐ z ∂μ, F z = F z₀ := by
    filter_upwards [hstart] with z hz
    rw [← EinsteinRelation.Probability.finiteHistory_test_stopped Δ 0 F hF z,
      ← EinsteinRelation.Probability.finiteHistory_test_stopped Δ 0 F hF z₀]
    congr 1
    apply Prod.ext
    · apply ContinuousMap.ext
      intro t
      simpa only [EinsteinRelation.Probability.stoppedHistorySample, Nat.cast_zero,
        zero_mul, min_eq_right (zero_le (a := t)), z₀, ContinuousMap.coe_mk] using hz
    · funext k
      simp only [EinsteinRelation.Probability.stoppedHistorySample, Nat.not_lt_zero, if_false]
  calc
    (∫ z, F z ∂μ) = ∫ _, F z₀ ∂μ := integral_congr_ae hconst
    _ = F z₀ := by simp only [integral_const, probReal_univ, one_smul]

end EinsteinFull.Regeneration
