import EinsteinFull.Calculus.C8TubeWeightedParabolicPoincare
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open EinsteinRelation PDE MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Removing a positive regularization inside a sublinear-power integral. -/
theorem c8_weak_harnack_epsilon_integral_limit {d : ℕ}
    {a b r p : ℝ} (hab : a < b) (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 r))) :
    Tendsto (fun n : ℕ => ∫ z in Set.Ioo a b ×ˢ sourceBall 0 r,
      Real.rpow (|u z| + ((n : ℝ)+1)⁻¹) p) atTop
      (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall 0 r, Real.rpow |u z| p)) := by
  let I := Set.Ioo a b
  let U := sourceBall (0 : EinsteinRelation.Vec d) r
  have : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr (by
    by_cases h : a < b
    · simp [I]
    · exact (h hab).elim)
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr (by
    dsimp [U]; rw [c8_sourceBall_eq_euclideanBall 0 hr]
    exact PDE.volume_euclideanBall_ne_top 0 hr.le)
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have : IsFiniteMeasure (volume.restrict (I ×ˢ U)) := by rw [hprod]; infer_instance
  have hu1 : Integrable u (volume.restrict (I ×ˢ U)) :=
    memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num))
  have hb : Integrable (fun z => (2 : ℝ) + |u z|) (volume.restrict (I ×ˢ U)) :=
    (integrable_const 2).add hu1.abs
  have heps : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  apply tendsto_integral_of_dominated_convergence (fun z => 2 + |u z|)
  · intro n
    have hm : AEStronglyMeasurable (fun z => |u z|)
        (volume.restrict (I ×ˢ U)) := by
      simpa only [Real.norm_eq_abs] using hu.aestronglyMeasurable.norm
    exact (Real.continuous_rpow_const hp.le).comp_aestronglyMeasurable
      (hm.add aestronglyMeasurable_const)
  · exact hb
  · intro n
    filter_upwards with z
    have he : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have he1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hx : 0 ≤ |u z| + ((n : ℝ) + 1)⁻¹ := by positivity
    have hpow : Real.rpow (|u z| + ((n : ℝ) + 1)⁻¹) p ≤
        1 + (|u z| + ((n : ℝ) + 1)⁻¹) := by
      change (|u z| + ((n : ℝ) + 1)⁻¹) ^ p ≤ _
      by_cases h : |u z| + ((n : ℝ) + 1)⁻¹ ≤ 1
      · have := Real.rpow_le_one hx h hp.le
        linarith
      · have hh : 1 ≤ |u z| + ((n : ℝ) + 1)⁻¹ := le_of_lt (lt_of_not_ge h)
        have hh' := Real.rpow_le_rpow_of_exponent_le hh hp1.le
        rw [Real.rpow_one] at hh'
        linarith
    rw [Real.norm_eq_abs]
    change |(|u z| + ((n : ℝ) + 1)⁻¹) ^ p| ≤ _
    rw [abs_of_nonneg (Real.rpow_nonneg hx p)]
    change (|u z| + ((n : ℝ) + 1)⁻¹) ^ p ≤ _ at hpow
    linarith
  · filter_upwards with z
    have h := (Real.continuous_rpow_const hp.le).tendsto |u z|
    have ht : Tendsto (fun n : ℕ => |u z| + ((n : ℝ) + 1)⁻¹) atTop (𝓝 |u z|) := by
      simpa only [add_zero] using (tendsto_const_nhds.add heps)
    exact h.comp ht

end EinsteinFull.Calculus
