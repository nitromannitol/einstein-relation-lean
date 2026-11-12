import EinsteinRelation.Correctors.CenteredScalarMoments

/-! Spatial mean recentering in `paper/main.tex:751-753`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The mean recentering inequality requires only integrability of the
scalar field. An infinite source moment is permitted. -/
theorem lintegral_abs_sub_mean_rpow_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (u : X → ℝ) (c p : ℝ) (hp : 1 ≤ p) (hu : Integrable u μ) :
    (∫⁻ x, ENNReal.ofReal (|u x - ∫ y, u y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) *
        (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) := by
  have hp0 : 0 < p := by linarith
  by_cases hb : (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) < ⊤
  · have heq : (∫⁻ x, ‖u x - c‖ₑ ^ (ENNReal.ofReal p).toReal ∂μ) =
        ∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ := by
      simp only [ENNReal.toReal_ofReal hp0.le]
      apply lintegral_congr_ae
      filter_upwards with x
      rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
    have hv : MemLp (fun x => u x - c) (ENNReal.ofReal p) μ :=
      ⟨(hu.sub (integrable_const c)).aestronglyMeasurable,
        (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
          (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).mpr
            (heq ▸ hb)⟩
    have hu' : MemLp u (ENNReal.ofReal p) μ := by
      convert hv.add (memLp_const c) using 1
      ext x
      simp
    exact lintegral_centered_abs_rpow_le μ u c p hp hu'
  · have htop : (∫⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) = ⊤ :=
      top_le_iff.mp (le_of_not_gt hb)
    rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))]
    exact le_top

end EinsteinRelation.Correctors
