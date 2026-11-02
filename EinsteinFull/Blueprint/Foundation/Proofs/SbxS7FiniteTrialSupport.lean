import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.Continuity

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.ConditionalTrialExhaustion

/-- Iterating an integrated failure estimate requires no independence. -/
theorem finite_product_of_failure_step {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Set Ω) (q : ℝ≥0∞)
    (hstep : ∀ n, μ (F (n + 1)) ≤ q * μ (F n)) (N : ℕ) :
    μ (F N) ≤ q ^ N * μ (F 0) := by
  induction N with
  | zero => simp only [pow_zero, one_mul, le_refl]
  | succ n ih =>
    calc
      μ (F (n + 1)) ≤ q * μ (F n) := hstep n
      _ ≤ q * (q ^ n * μ (F 0)) := mul_le_mul_right ih q
      _ = q ^ (n + 1) * μ (F 0) := by rw [pow_succ]; ac_rfl

/-- Integrate the conditional failure bound on the event known at the trial's
history. The failure indicator is integrable under the probability law. -/
theorem measure_inter_le_of_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (S T : Set Ω) (hS : MeasurableSet[H] S) (hT : @MeasurableSet Ω mΩ T)
    (q : ℝ) (hq : 0 ≤ q)
    (hcond : ∀ᵐ x ∂μ, x ∈ S →
      (μ[T.indicator (fun _ => (1 : ℝ)) | H]) x ≤ q) :
    μ (S ∩ T) ≤ ENNReal.ofReal q * μ S := by
  let : MeasurableSpace Ω := mΩ
  have hInt : Integrable (T.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hT
  have hbound : μ.real (S ∩ T) ≤ q * μ.real S := by
    calc
      μ.real (S ∩ T) = ∫ x in S, T.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [setIntegral_indicator hT, setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ x in S, (μ[T.indicator (fun _ => (1 : ℝ)) | H]) x ∂μ :=
        (setIntegral_condExp hH hInt hS).symm
      _ ≤ ∫ _ in S, q ∂μ :=
        integral_mono_ae integrable_condExp.integrableOn (integrable_const q)
          ((ae_restrict_iff' (hH S hS)).mpr hcond)
      _ = q * μ.real S := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  have h := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul hq, ofReal_measureReal (measure_ne_top μ (S ∩ T)),
    ofReal_measureReal (measure_ne_top μ S)] at h
  exact h

/-- Adapted nested failures satisfy the product bound under conditional
estimates. Each prefix is measurable in the history used for that step. -/
theorem finite_product_of_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℕ → MeasurableSpace Ω) (hH : ∀ n, H n ≤ mΩ)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[H n] (F n))
    (hnest : ∀ n, F (n + 1) ⊆ F n) (q : ℝ) (hq : 0 ≤ q)
    (hcond : ∀ n, ∀ᵐ x ∂μ, x ∈ F n →
      (μ[(F (n + 1)).indicator (fun _ => (1 : ℝ)) | H n]) x ≤ q) (N : ℕ) :
    μ (F N) ≤ ENNReal.ofReal q ^ N * μ (F 0) := by
  apply finite_product_of_failure_step
  intro n
  have h := measure_inter_le_of_condExp μ (H n) (hH n) (F n) (F (n + 1))
    (hF n) (hH (n + 1) _ (hF (n + 1))) q hq (hcond n)
  simpa only [Set.inter_eq_right.mpr (hnest n)] using h

/-- Continuity from above and geometric decay exclude infinite failure. -/
theorem measure_iInter_eq_zero_of_failure_step {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet (F n))
    (hanti : Antitone F) (q : ℝ≥0∞) (hq : q < 1)
    (hstep : ∀ n, μ (F (n + 1)) ≤ q * μ (F n)) :
    μ (⋂ n, F n) = 0 := by
  rw [hanti.measure_iInter (fun n => (hF n).nullMeasurableSet)
    ⟨0, measure_ne_top μ (F 0)⟩]
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
  intro n
  calc
    ⨅ k, μ (F k) ≤ μ (F n) := iInf_le _ n
    _ ≤ q ^ n * μ (F 0) := finite_product_of_failure_step μ F q hstep n
    _ ≤ q ^ n * 1 := mul_le_mul_right (prob_le_one : μ (F 0) ≤ 1) _
    _ = q ^ n := mul_one _

/-- An integrated conditional success estimate bounds the complementary
failure event. The factor is formed after choosing the success constant. -/
theorem measure_sdiff_le_of_success_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Set Ω)
    (hG : MeasurableSet G) (ε : ℝ) (hε : ε ≤ 1)
    (hwin : ε * μ.real E ≤ μ.real (E ∩ G)) :
    μ (E \ G) ≤ ENNReal.ofReal (1 - ε) * μ E := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := E) hG
  have hbound : μ.real (E \ G) ≤ (1 - ε) * μ.real E := by
    linarith only [hwin, hsplit]
  have h := ENNReal.ofReal_le_ofReal hbound
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr hε),
    ofReal_measureReal (measure_ne_top μ (E \ G)),
    ofReal_measureReal (measure_ne_top μ E)] at h
  exact h

/-- Adapted conditional estimates with a strict contraction exclude an
infinite nested failure sequence. -/
theorem measure_iInter_eq_zero_of_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℕ → MeasurableSpace Ω) (hH : ∀ n, H n ≤ mΩ)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[H n] (F n))
    (hnest : ∀ n, F (n + 1) ⊆ F n) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hcond : ∀ n, ∀ᵐ x ∂μ, x ∈ F n →
      (μ[(F (n + 1)).indicator (fun _ => (1 : ℝ)) | H n]) x ≤ q) :
    μ (⋂ n, F n) = 0 := by
  apply measure_iInter_eq_zero_of_failure_step μ F (fun n => hH n _ (hF n))
    (antitone_nat_of_succ_le hnest) (ENNReal.ofReal q) (ENNReal.ofReal_lt_one.mpr hq1)
  intro n
  have h := measure_inter_le_of_condExp μ (H n) (hH n) (F n) (F (n + 1))
    (hF n) (hH (n + 1) _ (hF (n + 1))) q hq (hcond n)
  simpa only [Set.inter_eq_right.mpr (hnest n)] using h

/-- A conditional success lower bound integrates on the actual history event. -/
theorem measure_inter_ge_of_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (S T : Set Ω) (hS : MeasurableSet[H] S) (hT : @MeasurableSet Ω mΩ T)
    (η : ℝ) (hη : 0 ≤ η)
    (hcond : ∀ᵐ x ∂μ, x ∈ S →
      η ≤ (μ[T.indicator (fun _ => (1 : ℝ)) | H]) x) :
    ENNReal.ofReal η * μ S ≤ μ (S ∩ T) := by
  have hInt : Integrable (T.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hT
  have hbound : η * μ.real S ≤ μ.real (S ∩ T) := by
    calc
      η * μ.real S = ∫ _ in S, η ∂μ := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in S, (μ[T.indicator (fun _ => (1 : ℝ)) | H]) x ∂μ :=
        integral_mono_ae (integrable_const η) integrable_condExp.integrableOn
          ((ae_restrict_iff' (hH S hS)).mpr hcond)
      _ = ∫ x in S, T.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        setIntegral_condExp hH hInt hS
      _ = μ.real (S ∩ T) := by
        rw [setIntegral_indicator hT, setIntegral_const, smul_eq_mul, mul_one]
  have h := ENNReal.ofReal_le_ofReal hbound
  rwa [ENNReal.ofReal_mul hη, ofReal_measureReal (measure_ne_top μ S),
    ofReal_measureReal (measure_ne_top μ (S ∩ T))] at h


end EinsteinFull.Blueprint.ConditionalTrialExhaustion
