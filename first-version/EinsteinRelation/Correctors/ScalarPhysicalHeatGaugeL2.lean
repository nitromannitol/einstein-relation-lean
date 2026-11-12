import EinsteinRelation.Correctors.PhysicalCenteredLocalL2
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.HeatAverageDilation

/-! Source: `paper/main.tex:724-731`. Transport of planar heat-centered
scalar oscillations to the physical radius-four local L² norm. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A scalar heat-centered average moment transports to a physical local
root-integral moment. The heat gauge is chosen at the given local center. -/
theorem scalar_physical_heat_gauge_local_L2_moment
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (u : Ξ → Vec d → ℝ)
    (hu : ∀ᵐ a ∂Q, ∀ R : ℝ, 0 < R → MemLp (u a) 2 (volume.restrict (ball 0 R)))
    (r c p : ℝ) (hr : 1 ≤ r) (hp : 0 ≤ p) (z : Vec d)
    (hm : AEMeasurable (fun a => Real.sqrt (⨍ x in ball (r⁻¹ • z) 4,
      |u a x - scalarHeatAverage (u a) (r⁻¹ • z) 4| ^ 2 ∂volume)) Q)
    (B : ℝ≥0∞)
    (hb : (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball (r⁻¹ • z) 4,
      |u a x - scalarHeatAverage (u a) (r⁻¹ • z) 4| ^ 2 ∂volume)) ^ p) ∂Q) ≤ B) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
      |c * u (T ω) (r⁻¹ • x) -
        scalarHeatAverage (fun y => c * u (T ω) (r⁻¹ • y)) z (r * 4)| ^ 2
          ∂volume)) ^ p) ∂P) ≤
      ENNReal.ofReal ((Real.sqrt (c ^ 2 * r ^ d)) ^ p) *
        (ENNReal.ofReal ((Real.sqrt (volume.real (ball (0 : Vec d) 4))) ^ p) * B) := by
  let F (a : Ξ) (x : Vec d) := |u a x - scalarHeatAverage (u a) (r⁻¹ • z) 4| ^ 2
  let V := volume.real (ball (0 : Vec d) 4)
  have hV : 0 < V := ball_volume_pos_finite d 4 (by norm_num)
  have hmass : (volume.restrict (ball (r⁻¹ • z) 4)).real Set.univ = V := by
    simp only [measureReal_def, Measure.restrict_apply_univ, volume_euclideanBall_center, V]
  have hroot (a : Ξ) : Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F a x ∂volume) =
      Real.sqrt V * Real.sqrt (⨍ x in ball (r⁻¹ • z) 4, F a x ∂volume) := by
    simpa only [hmass] using sqrt_integral_eq_sqrt_mass_mul_sqrt_average
      (volume.restrict (ball (r⁻¹ • z) 4)) (F a) (by rw [hmass]; exact hV)
  have hi : ∀ᵐ a ∂Q, IntegrableOn (F a) (ball (r⁻¹ • z) 4) volume := by
    filter_upwards [hu] with a ha
    letI := isFiniteMeasure_restrict_euclideanBall (r⁻¹ • z) 4 (by norm_num)
    have hlocal := memLp_on_euclideanBall_of_origin_balls (u a) ha (r⁻¹ • z) 4 (by norm_num)
    simpa only [F, sq_abs] using
      (hlocal.sub (memLp_const (scalarHeatAverage (u a) (r⁻¹ • z) 4))).integrable_sq
  have hm' : AEMeasurable (fun a => ENNReal.ofReal
      ((Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F a x ∂volume)) ^ p)) Q := by
    simp_rw [hroot]
    exact ((aemeasurable_const.mul hm).pow_const p).ennreal_ofReal
  have hb' : (∫⁻ a, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F a x ∂volume)) ^ p) ∂Q) ≤
      ENNReal.ofReal ((Real.sqrt V) ^ p) * B := by
    simp_rw [hroot, Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt V) ^ p)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hb _
  have h := root_integral_centered_moment_measurePreserving_inv_dilation hT F r
    (c ^ 2) 4 p z hr (sq_nonneg c) le_rfl hp (fun _ _ => sq_nonneg _) hi hm'
    (ENNReal.ofReal ((Real.sqrt V) ^ p) * B) hb'
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  simpa only [scalarHeatAverage_dilation _ r c 4 hr0 (by norm_num), F,
    ← mul_sub, sq_abs, mul_pow] using h

end EinsteinRelation.Correctors
