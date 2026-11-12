import EinsteinRelation.Correctors.SpatialAverageDilation

/-! Physical normalization in `paper/main.tex:722-731`. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem measurableSet_ball_dilation {d : ℕ} (z : Vec d) (ρ : ℝ) :
    MeasurableSet (ball z ρ) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- Positive dilation of a genuine, arbitrarily centered spatial integral. -/
theorem setIntegral_euclideanBall_inv_smul {d : ℕ} (f : Vec d → ℝ)
    (r R : ℝ) (hr : 0 < r) (z : Vec d) :
    (∫ x in ball z R, f (r⁻¹ • x) ∂volume) =
      r ^ d * ∫ x in ball (r⁻¹ • z) (r⁻¹ * R), f x ∂volume := by
  have hpre (x : Vec d) : r⁻¹ • x ∈ ball (r⁻¹ • z) (r⁻¹ * R) ↔ x ∈ ball z R := by
    have hpos : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
    simp only [ball, Set.mem_setOf_eq]
    rw [← smul_sub, euclideanNorm_smul _ hpos]
    exact ⟨fun h => lt_of_mul_lt_mul_left h hpos, fun h => mul_lt_mul_of_pos_left h (inv_pos.mpr hr)⟩
  have key (g : Vec d → ℝ) : (∫ x in ball z R, g (r⁻¹ • x) ∂volume) =
      r ^ d * ∫ y in ball (r⁻¹ • z) (r⁻¹ * R), g y ∂volume := by
    have hind : (fun x : Vec d => (ball (r⁻¹ • z) (r⁻¹ * R)).indicator g (r⁻¹ • x)) =
        (ball z R).indicator (fun x => g (r⁻¹ • x)) := by
      funext x
      by_cases hx : x ∈ ball z R
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hpre x).mpr hx)]
      · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hpre x).mp hx)]
    have h := Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
      ((ball (r⁻¹ • z) (r⁻¹ * R)).indicator g) hr.le
    rw [hind, integral_indicator (measurableSet_ball_dilation (r⁻¹ • z) (r⁻¹ * R)),
      integral_indicator (measurableSet_ball_dilation z R)] at h
    simpa only [Module.finrank_fin_fun, smul_eq_mul] using h
  exact key f

end EinsteinRelation.Correctors
