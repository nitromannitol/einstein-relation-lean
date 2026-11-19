import EinsteinFull.Regeneration.ExponentialTailMoment
import EinsteinRelation.Regeneration.RegenerationGrid
import EinsteinRelation.Regeneration.Measurability

/-!
# Regeneration endpoint moment from trial moments

Shen's geometric summation bounds the first-regeneration endpoint once the
weighted actual trial-start moments have a geometric bound.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] trialStartSequence firstRegenerationTime

/-- Geometrically summable weighted trial moments give the first endpoint moment. -/
theorem first_regeneration_endpoint_moment_of_trial_bounds {d : ℕ}
    (μ : Measure (FieldPair d × CoupledSample d)) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R a : ℝ) (i : Fin d) (B q : ℝ) (hB : 0 ≤ B) (hq : 0 ≤ q) (hq1 : q < 1)
    (hfinite : ∀ᵐ z ∂μ, firstRegenerationTime Δ lam R z.2 i ≠ ⊤)
    (htrial : ∀ n : ℕ,
      let E := {z : FieldPair d × CoupledSample d | trialStartSequence Δ lam R z.2 i n ≠ ⊤}
      let F := fun z : FieldPair d × CoupledSample d => ENNReal.ofReal (Real.exp (a *
        (lam * (z.2.1 (trialStartSequence Δ lam R z.2 i n).toNNReal i - z.2.1 0 i))))
      (∫⁻ z, E.indicator F z ∂μ) ≤ ENNReal.ofReal (B * q ^ n)) :
    Integrable (fun z : FieldPair d × CoupledSample d => Real.exp (a *
      (lam * (z.2.1 (firstRegenerationTime Δ lam R z.2 i).toNNReal i - z.2.1 0 i)))) μ ∧
    (∫ z : FieldPair d × CoupledSample d, Real.exp (a *
      (lam * (z.2.1 (firstRegenerationTime Δ lam R z.2 i).toNNReal i - z.2.1 0 i))) ∂μ)
      ≤ B / (1 - q) := by
  let T : FieldPair d × CoupledSample d → ℝ≥0∞ := fun z => firstRegenerationTime Δ lam R z.2 i
  let S : ℕ → FieldPair d × CoupledSample d → ℝ≥0∞ :=
    fun n z => trialStartSequence Δ lam R z.2 i n
  let E : ℕ → Set (FieldPair d × CoupledSample d) := fun n => {z | S n z ≠ ⊤}
  let F : ℕ → FieldPair d × CoupledSample d → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (Real.exp (a * (lam * (z.2.1 (S n z).toNNReal i - z.2.1 0 i))))
  let V : FieldPair d × CoupledSample d → ℝ := fun z =>
    Real.exp (a * (lam * (z.2.1 (T z).toNNReal i - z.2.1 0 i)))
  have hS (n : ℕ) : Measurable (S n) :=
    (measurable_trialStartSequence Δ lam R i n).comp measurable_snd
  have hT : Measurable T := (measurable_firstRegenerationTime Δ lam R i).comp measurable_snd
  have hE (n : ℕ) : MeasurableSet (E n) := (measurableSet_eq_fun (hS n) measurable_const).compl
  have hV : Measurable V := by
    have ht : Measurable (fun z : FieldPair d × CoupledSample d => z.2.1 (T z).toNNReal) :=
      continuous_eval.measurable.comp (measurable_snd.fst.prodMk hT.ennreal_toNNReal)
    exact Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul
      (((measurable_pi_apply i).comp ht).sub ((measurable_pi_apply i).comp
        ((continuous_eval_const 0).measurable.comp measurable_snd.fst)))))
  have hF (n : ℕ) : Measurable (F n) := by
    have ht : Measurable (fun z : FieldPair d × CoupledSample d => z.2.1 (S n z).toNNReal) :=
      continuous_eval.measurable.comp (measurable_snd.fst.prodMk (hS n).ennreal_toNNReal)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.mul (((measurable_pi_apply i).comp ht).sub ((measurable_pi_apply i).comp
        ((continuous_eval_const 0).measurable.comp measurable_snd.fst))))))
  have hpoint : ∀ᵐ z ∂μ, ENNReal.ofReal (V z) ≤ ∑' n, (E n).indicator (F n) z := by
    filter_upwards [hfinite] with z hz
    obtain ⟨n, hn, heq⟩ := firstRegenerationTime_attained Δ hΔ lam R z.2 i hz
    have hm : z ∈ E n := hn.1
    have hv : ENNReal.ofReal (V z) = (E n).indicator (F n) z := by
      rw [Set.indicator_of_mem hm]
      dsimp only [V, T, F, S]
      rw [heq]
    rw [hv]
    exact ENNReal.le_tsum (f := fun k => (E k).indicator (F k) z) n
  have hlin : (∫⁻ z, ENNReal.ofReal (V z) ∂μ) ≤
      ∑' n, ENNReal.ofReal (B * q ^ n) := by
    calc
      _ ≤ ∫⁻ z, ∑' n, (E n).indicator (F n) z ∂μ := lintegral_mono_ae hpoint
      _ = ∑' n, ∫⁻ z, (E n).indicator (F n) z ∂μ :=
        lintegral_tsum (fun n => ((hF n).indicator (hE n)).aemeasurable)
      _ ≤ _ := ENNReal.tsum_le_tsum htrial
  have hsum : Summable (fun n : ℕ => B * q ^ n) :=
    (summable_geometric_of_lt_one hq hq1).mul_left B
  have hsum_eq : (∑' n : ℕ, B * q ^ n) = B / (1 - q) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq1, div_eq_mul_inv]
  have hbound : (∫⁻ z, ENNReal.ofReal (V z) ∂μ) ≤ ENNReal.ofReal (B / (1 - q)) := by
    calc
      _ ≤ _ := hlin
      _ = ENNReal.ofReal (∑' n : ℕ, B * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hB (pow_nonneg hq n)) hsum).symm
      _ = _ := by rw [hsum_eq]
  have hi : Integrable V μ := ⟨hV.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)).2
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg hB (sub_nonneg.mpr hq1.le))).mp hbound

end EinsteinFull.Regeneration
