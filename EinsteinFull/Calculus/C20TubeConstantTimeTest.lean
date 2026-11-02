import EinsteinFull.Calculus.C11TubeWeightedZeroPastRepresentative

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A spatial density times a constant contributes no time derivative to a test. -/
theorem c20_weighted_constant_time_test_integral_zero
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d) (c : ℝ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * c) * fderiv ℝ ψ z (1,0)) = 0 := by
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hz := c11_density_time_derivative_integral_zero_on ρ hell.1 κ⁻¹ hρbound
    (Set.Ioo a b) (sourceBall y r) ψ hψ hψc hψs
  have heq : (fun z : ℝ × Vec d => -(ρ z.2 * c) * fderiv ℝ ψ z (1,0)) =
      (fun z => -c * (ρ z.2 * fderiv ℝ ψ z (1,0))) := by
    funext z
    ring
  rw [heq, integral_const_mul, hz, mul_zero]

/-- Subtracting the value at zero does not change the tested time term. -/
theorem c20_weighted_time_test_sub_value_zero
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (F : ℝ → ℝ) (u : ℝ × Vec d → ℝ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0)) =
    ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hD : Continuous D := (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ (1, 0))
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hi : Integrable (fun z : ℝ × Vec d => (ρ z.2 * F 0) * D z) μ := by
    have h := hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hρbound z.2)
    have h' := (h.const_mul (F 0)).integrableOn (s := Set.Ioo a b ×ˢ sourceBall y r)
    apply h'.congr
    filter_upwards with z
    dsimp [D]
    ring
  have hz : (∫ z, (ρ z.2 * F 0) * D z ∂μ) = 0 := by
    have h := c20_weighted_constant_time_test_integral_zero hκ ρ α hell y (F 0) ψ hψ hψc hψs
    simpa [μ, D, integral_neg] using congrArg Neg.neg h
  let f : ℝ × Vec d → ℝ := fun z => -(ρ z.2 * F (u z)) * D z
  have heq : (fun z : ℝ × Vec d => -(ρ z.2 * (F (u z) - F 0)) * D z) =
      (fun z => f z + (ρ z.2 * F 0) * D z) := by
    funext z
    dsimp [f]
    ring
  rw [heq]
  by_cases hf : Integrable f μ
  · rw [integral_add hf hi, hz, add_zero]
  · have hni : ¬ Integrable (fun z => f z + (ρ z.2 * F 0) * D z) μ := by
      intro h
      have := h.sub hi
      apply hf
      convert this using 1 <;> ext z <;> simp
    rw [integral_undef hni, integral_undef hf]

end EinsteinFull.Calculus
