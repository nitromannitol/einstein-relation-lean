import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski
import EinsteinRelation.Correctors.StochasticPowerTail

/-! # Stochastic time tails from local gradient RMS moments

Source: `paper/main.tex:800–808,843–849`. The estimate consumes local
spatial RMS moments of the same gradient, rather than pointwise moments.
All exceptional field and time sets remain almost-everywhere statements.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Local RMS gradient decay controls the literal infinite-time spatial
RMS remainder. Source: `paper/main.tex:800–808,843–849`. -/
theorem stochastic_local_gradient_tail_moment_le
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [SigmaFinite ν]
    (G : Ω × (ℝ × X) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C α T : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T)
    (hsections : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => G (ω,(t,x))) 2 ν)
    (hdecay : ∀ t : ℝ, T < t →
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal (C*t^(-1-α))) :
    (∀ᵐ ω ∂Q, IntegrableOn
      (fun t => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) (Ioi T)) ∧
    MemLp (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) p Q ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) p Q ≤
      ENNReal.ofReal ((C/α)*T^(-α)) := by
  let a : Ω × ℝ → ℝ := fun z => Real.sqrt (∫ x, ‖G (z.1,(z.2,x))‖^2 ∂ν)
  have hgm : Measurable (fun z : (Ω × ℝ) × X => G (z.1.1,(z.1.2,z.2))) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have ham : Measurable a :=
    ((hgm.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have htail := stochastic_power_tail_integrable_and_moment_le Q hp hpt a ham
    hC hα hT hdecay
  have hreordered : Measurable (fun z : (Ω × X) × ℝ => G (z.1.1,(z.2,z.1.2))) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  have hint : Measurable (fun z : Ω × X => ∫ t in Ioi T, G (z.1,(t,z.2))) :=
    hreordered.stronglyMeasurable.integral_prod_right'.measurable
  have hF : Measurable (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) :=
    ((hint.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hpoint : ∀ᵐ ω ∂Q,
      ‖Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)‖ ≤
        ‖∫ t in Ioi T, a (ω,t)‖ := by
    filter_upwards [hsections,htail.2.1] with ω hω hωi
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (integral_nonneg (fun t => Real.sqrt_nonneg _))]
    exact spatialL2_tail_integral_le_integral_spatialL2 ν hT
      (fun z => G (ω,z)) (hG.comp (measurable_const.prodMk measurable_id)) hω hωi
  have hnorm := (eLpNorm_mono_ae hpoint).trans htail.2.2
  exact ⟨htail.2.1,⟨hF.aestronglyMeasurable,lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩,hnorm⟩

end EinsteinRelation.Correctors
