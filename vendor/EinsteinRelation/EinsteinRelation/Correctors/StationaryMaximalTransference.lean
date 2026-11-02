import EinsteinRelation.Correctors.StationarySpatialIntegral
import EinsteinRelation.Correctors.CubeVolumeRatio

/-!
# Transferring spatial localization bounds to the environment law

Source: `paper/main.tex:693-698`. Integrating a localized spatial bound
against the stationary law replaces its two spatial integrals by their
volumes times environment expectations. The boundary enlargement disappears
as the cube grows. This step has no independence or ergodicity hypothesis.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

/-- A spatial localization bound controls the probability of the event
being localized, after sending the observation cube to infinity. -/
theorem probability_le_of_spatial_localization {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : FieldPair d → ℝ) (hf : Measurable f) (hi : Integrable f Q)
    (s : Set (FieldPair d)) (hs : MeasurableSet s) (C S : ℝ)
    (hloc : ∀ R : ℝ, 0 < R → ∀ᵐ ω ∂Q,
      (∫ x in Metric.closedBall (0 : Vec d) R,
        s.indicator (fun _ => (1 : ℝ)) (translate x ω) ∂volume) ≤
      C * ∫ x in Metric.closedBall (0 : Vec d) (R + S), f (translate x ω) ∂volume) :
    Q.real s ≤ C * ∫ ω, f ω ∂Q := by
  have hbound (R : ℝ) (hR : 0 < R) :
      Q.real s ≤ C * (volume.real (Metric.closedBall (0 : Vec d) (R + S)) /
        volume.real (Metric.closedBall (0 : Vec d) R)) * ∫ ω, f ω ∂Q := by
    let ν := volume.restrict (Metric.closedBall (0 : Vec d) R)
    let η := volume.restrict (Metric.closedBall (0 : Vec d) (R + S))
    letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
      (isCompact_closedBall (0 : Vec d) R).measure_ne_top
    letI : IsFiniteMeasure η := isFiniteMeasure_restrict.mpr
      (isCompact_closedBall (0 : Vec d) (R + S)).measure_ne_top
    have hInd := stationary_spatial_integral Q hQ ν (s.indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator hs) ((integrable_const (1 : ℝ)).indicator hs)
    have hF := stationary_spatial_integral Q hQ η f hf hi
    have h := integral_mono_ae hInd.2.1 (hF.2.1.const_mul C) (hloc R hR)
    rw [hInd.2.2, integral_const_mul, hF.2.2] at h
    simp only [integral_indicator_const _ hs, smul_eq_mul, mul_one,
      Measure.restrict_apply_univ] at h
    have hνeq : (ν Set.univ).toReal = volume.real (Metric.closedBall (0 : Vec d) R) := by
      simp [ν, Measure.real]
    have hηeq : (η Set.univ).toReal = volume.real (Metric.closedBall (0 : Vec d) (R + S)) := by
      simp [η, Measure.real]
    rw [hνeq, hηeq] at h
    have hV : 0 < volume.real (Metric.closedBall (0 : Vec d) R) := by
      rw [Measure.real, Real.volume_pi_closedBall _ hR.le, ENNReal.toReal_ofReal]
      · exact pow_pos (mul_pos (by norm_num) hR) _
      · exact pow_nonneg (mul_nonneg (by norm_num) hR.le) _
    have hdiv := (le_div_iff₀ hV).mpr (by simpa only [mul_comm] using h)
    convert hdiv using 1 <;> dsimp [ν, η, Measure.real] <;> ring
  have ht := ((tendsto_cube_volume_ratio d S).const_mul C).mul_const (∫ ω, f ω ∂Q)
  have hb := ge_of_tendsto ht ((eventually_gt_atTop (0 : ℝ)).mono fun R hR => hbound R hR)
  simpa only [mul_one] using hb

end EinsteinRelation.Correctors
