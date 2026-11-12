import EinsteinRelation.Correctors.AKMFlowCylinderGradientMoments

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
/-- Cylinder gradient moments for any specified measurable semigroup,
retaining that exact scalar flow. Source: `paper/main.tex:798–806`. -/
theorem semigroupFlow_diffusive_cylinder_moment_le_probability
    (d : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ D : ℝ, 0 < D ∧ ∀ (P : Measure (Coefficient d K)), IsProbabilityMeasure P → ∀
      (g : Coefficient d K → Vec d → Vec d)
      (u : Coefficient d K → ℝ × Vec d → ℝ)
      (G : Coefficient d K → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
      ∀ (m : ℝ), 2 ≤ m → ∀ r : ℝ, 1 ≤ r → ∀ C : ℝ, 0 ≤ C →
      (∀ t : ℝ, r^2 ≤ t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      MemLp (fun A => vectorRms volume
        (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => vectorRms volume
        (Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r) (G A)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (D*C/r*(r^2)^(-(1 : ℝ)/2-(d : ℝ)/4))  := by
  obtain ⟨D,hD,henergy⟩ := parabolicSolution_cylinder_rms_le d K hK
  refine ⟨D,hD,?_⟩
  intro P hP g u G hum hGm hsol m hm r hr C hC hval
  letI : IsProbabilityMeasure P := hP
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hr2 : 0 < r^2 := sq_pos_of_pos hr0
  have hr21 : 1 ≤ r^2 := by nlinarith
  have hm0 : 0 < m := zero_lt_two.trans_le hm
  let V := Set.Ioo (2*r^2) (3*r^2) ×ˢ originBall d r
  let U := Set.Ioo (r^2) (4*r^2) ×ˢ originBall d (2*r)
  let E := fun A => vectorRms volume V (G A)
  let S := fun A => scalarRms volume U (u A)
  have hUmeas : MeasurableSet U := by
    have heq : originBall d (2*r) = ball (0 : Vec d) (2*r) := by
      ext x; simp only [originBall, ball, sub_zero]
    exact measurableSet_Ioo.prod (by rw [heq]; exact (paired_isOpen_ball _ _).measurableSet)
  have hvol := positiveTimeCylinder_volume_pos_finite (d := d)
    (by nlinarith : r^2 < 4*r^2) (by positivity : 0 < 2*r)
  have hscalar := scalarL2_setAverage_moment_le P volume hUmeas hvol.1 hvol.2 hm
    (mul_nonneg hC (Real.rpow_nonneg hr2.le _))
    (fun z => u z.1 z.2) hum (fun z hz => by
      have hzv := hval z.1 hz.1.1.le z.2
      refine ⟨hzv.1, hzv.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr2 hz.1.1.le (by
          have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith only [hd0])) hC)
  have hEm : Measurable E := by
    have hgm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
        euclideanSq (G z.1 z.2)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hGm).mul ((measurable_pi_apply j).comp hGm)
    have hi := (hgm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict V)).measurable
    simpa only [E, vectorRms, average_eq, measureReal_restrict_apply_univ, smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hdom : ∀ᵐ A ∂P, ‖E A‖ ≤ D/r * ‖S A‖ := by
    filter_upwards [hsol] with A hA
    have h := henergy r hr0 A (u A) (G A)
      (hA.2.1 (r^2) (4*r^2) (2*r) hr2 (by nlinarith) (by positivity))
    simpa only [E, S, vectorRms, scalarRms, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using h
  refine ⟨hscalar.1.of_le_mul hEm.aestronglyMeasurable hdom, ?_⟩
  calc
    eLpNorm E (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (D/r) * eLpNorm S (ENNReal.ofReal m) P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal (D/r) *
        ENNReal.ofReal (C * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) :=
      mul_le_mul_right hscalar.2 _
    _ = ENNReal.ofReal (D * C / r * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hD.le hr0.le)]
      apply congrArg ENNReal.ofReal
      ring

end EinsteinRelation.Correctors
