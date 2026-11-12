import EinsteinRelation.Correctors.ParabolicScaledCutoff
import EinsteinRelation.Correctors.ParabolicCutoffRms
import EinsteinRelation.Correctors.AKMFlowCutoffGradientMoments
import EinsteinRelation.Correctors.PairedPDEBallNormalization

/-! # Unweighted gradient energy on parabolic cylinders

Source: `paper/main.tex:798–806`. A constructed compact cutoff gives the
inverse-radius gain in the gradient RMS. All spatial volumes are Euclidean
and the comparison constant is independent of the cylinder's scale.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- Volume of a positive-time Euclidean cylinder in coordinates.
Source: `paper/main.tex:798–806,832–840`. -/
theorem positiveTimeCylinder_volume_real {d : ℕ} {a b R : ℝ}
    (hab : a < b) (hR : 0 < R) :
    volume.real (Set.Ioo a b ×ˢ originBall d R) =
      (b-a) * R^d * volume.real (originBall d 1) := by
  have hball : ∀ r : ℝ, originBall d r = ball (0 : Vec d) r := fun r => by
    ext x
    simp only [originBall, ball, sub_zero]
  rw [Measure.volume_eq_prod, measureReal_prod_prod]
  have ht : volume.real (Set.Ioo a b) = b-a := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
  rw [ht, hball R, paired_ball_volume_real hR, ← hball 1]
  ring

/-- Every actual weak solution satisfies the unweighted inner-cylinder
energy estimate. The cutoff and its derivative bound are constructed in
the proof. Source: `paper/main.tex:798–806`. -/
theorem parabolicSolution_cylinder_rms_le (d : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ (A : Coefficient d K) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsParabolicSolution A (Set.Ioo (r^2) (4*r^2)) (originBall d (2*r)) u G →
        vectorRms volume (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) G ≤
          C / r * scalarRms volume (Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)) u := by
  obtain ⟨B, hB, hcut⟩ := exists_parabolic_scaled_cutoff d K
  refine ⟨Real.sqrt (B*(3*2^d)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro r hr A u G hsol
  obtain ⟨ζ, hζ, hζc, hζs, _, hζ1, hζD⟩ := hcut r hr
  have hr2 := sq_pos_of_pos hr
  have hv := positiveTimeCylinder_volume_pos_finite (d := d)
    (by nlinarith : 2*r^2 < 3*r^2) hr
  have hD := positiveTimeCylinder_volume_pos_finite (d := d) (by nlinarith : r^2 < 4*r^2)
    (by positivity : 0 < 2*r)
  have hU : IsOpen (originBall d (2*r)) := by
    have heq : originBall d (2*r) = ball (0 : Vec d) (2*r) := by
      ext x; simp only [originBall, ball, sub_zero]
    rw [heq]
    exact paired_isOpen_ball _ _
  have hsub : Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r ⊆
      Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r) := by
    intro z hz
    exact ⟨⟨by nlinarith [hz.1.1], by nlinarith [hz.1.2]⟩,
      lt_of_lt_of_le hz.2 (show r ≤ 2*r by linarith only [hr])⟩
  have hvmeas : MeasurableSet (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) := by
    have heq : originBall d r = ball (0 : Vec d) r := by
      ext x; simp only [originBall, ball, sub_zero]
    rw [heq]
    exact measurableSet_Ioo.prod (paired_isOpen_ball _ _).measurableSet
  have h := parabolicSolution_inner_rms_le hK measurableSet_Ioo hU hsol hζ hζc
    (by simpa only [interior_Ioo] using hζs) hvmeas hsub hv.1 hv.2 hD.2
    (fun z hz => hζ1 z ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩)
    (div_nonneg hB.le hr2.le) (fun z _ => hζD z)
  have hvol : volume.real (Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)) /
      volume.real (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) = 3*2^d := by
    rw [positiveTimeCylinder_volume_real (by nlinarith) (by positivity),
      positiveTimeCylinder_volume_real (by nlinarith) hr, mul_pow]
    have hunit : volume.real (originBall d 1) ≠ 0 := by
      have hb : originBall d 1 = ball (0 : Vec d) 1 := by
        ext x; simp only [originBall, ball, sub_zero]
      rw [hb]
      exact (paired_ball_volume_pos_finite (d := d) (by norm_num : (0 : ℝ) < 1)).ne'
    field_simp [hr.ne', hunit]
    ring
  have hfactor : Real.sqrt ((B/r^2) *
      volume.real (Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)) /
      volume.real (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r)) =
        Real.sqrt (B*(3*2^d)) / r := by
    rw [show (B/r^2) * volume.real (Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)) /
        volume.real (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) =
        (B * (volume.real (Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)) /
          volume.real (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r))) / r^2 by ring,
      hvol, Real.sqrt_div (mul_nonneg hB.le (by positivity)), Real.sqrt_sq hr.le]
  rwa [hfactor] at h

end EinsteinRelation.Correctors
