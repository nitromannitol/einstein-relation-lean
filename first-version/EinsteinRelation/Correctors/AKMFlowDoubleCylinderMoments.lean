import EinsteinRelation.Correctors.AKMFlowCylinderGradientMoments
import EinsteinRelation.Correctors.ParabolicTimeTranslation

/-! # Double-scale spatial cylinders at late times

Source: `paper/main.tex:798–806`. The actual weak energy estimate gives
double-scale cylinder gradient moments from scalar decay, before restricting to
any random-radius event. The same supplied flow is retained.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- A scalar moment estimate gives the gradient moment on the actual double-scale
cylinder immediately preceding time `3*r²`. This estimate has no inverse
radius gain; it is available without a random-radius restriction.
Source: `paper/main.tex:798–806`. -/
theorem semigroupFlow_shifted_double_cylinder_moment_le
    (d : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (P : Measure (Coefficient d K)), IsProbabilityMeasure P →
      ∀ (g : Coefficient d K → Vec d → Vec d)
        (u : Coefficient d K → ℝ × Vec d → ℝ)
        (G : Coefficient d K → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d K × (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) →
      ∀ (m : ℝ), 2 ≤ m → ∀ r : ℝ, 2 ≤ r → ∀ C : ℝ, 0 ≤ C →
      (∀ t : ℝ, r^2 ≤ t → ∀ x : Vec d,
        MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) P ∧
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (C * t^(-(1 : ℝ)/2 - (d : ℝ)/4))) →
      MemLp (fun A => vectorRms volume (Set.Ioo 8 12 ×ˢ originBall d 2)
        (fun z => G A (z.1+(3*r^2-12),z.2))) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => vectorRms volume (Set.Ioo 8 12 ×ˢ originBall d 2)
        (fun z => G A (z.1+(3*r^2-12),z.2))) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (D * C * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := by
  obtain ⟨D,hD,henergy⟩ := parabolicSolution_cylinder_rms_le d K hK
  refine ⟨D/2,div_pos hD two_pos,?_⟩
  intro P hP g u G hum hGm hsol m hm r hr C hC hval
  letI : IsProbabilityMeasure P := hP
  let c : ℝ := 3*r^2-12
  let us := fun A (z : ℝ × Vec d) => u A (z.1+c,z.2)
  let Gs := fun A (z : ℝ × Vec d) => G A (z.1+c,z.2)
  let V := Set.Ioo (8 : ℝ) 12 ×ˢ originBall d 2
  let U := Set.Ioo (4 : ℝ) 16 ×ˢ originBall d 4
  let E := fun A => vectorRms volume V (Gs A)
  let S := fun A => scalarRms volume U (us A)
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : 0 < r^2 := sq_pos_of_pos hr0
  have hr21 : 4 ≤ r^2 := by nlinarith
  have hshiftm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
      (z.1,(z.2.1+c,z.2.2))) :=
    measurable_fst.prodMk ((measurable_snd.fst.add measurable_const).prodMk measurable_snd.snd)
  have husm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => us z.1 z.2) :=
    hum.comp hshiftm
  have hGsm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => Gs z.1 z.2) :=
    hGm.comp hshiftm
  have hUmeas : MeasurableSet U := by
    have heq : originBall d 4 = ball (0 : Vec d) 4 := by
      ext x; simp only [originBall, ball, sub_zero]
    exact measurableSet_Ioo.prod (by rw [heq]; exact (paired_isOpen_ball _ _).measurableSet)
  have hvol := positiveTimeCylinder_volume_pos_finite (d := d)
    (by norm_num : (4 : ℝ) < 16) (by norm_num : (0 : ℝ) < 4)
  have hscalar := scalarL2_setAverage_moment_le P volume hUmeas hvol.1 hvol.2 hm
    (mul_nonneg hC (Real.rpow_nonneg hr2.le _))
    (fun z => us z.1 z.2) husm (fun z hz => by
      have hzt : r^2 ≤ z.1+c := by dsimp only [c]; nlinarith only [hz.1.1,hr21]
      have hzv := hval (z.1+c) hzt z.2
      refine ⟨hzv.1,hzv.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr2 hzt (by
          have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith only [hd0])) hC)
  have hEm : Measurable E := by
    have hgm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
        euclideanSq (Gs z.1 z.2)) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hGsm).mul ((measurable_pi_apply j).comp hGsm)
    have hi := (hgm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict V)).measurable
    simpa only [E,vectorRms,average_eq,measureReal_restrict_apply_univ,smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hdom : ∀ᵐ A ∂P, ‖E A‖ ≤ (D/2) * ‖S A‖ := by
    filter_upwards [hsol] with A hA
    have hshift := parabolicSolution_time_shift
      (hA.2.1 (3*r^2-8) (3*r^2+4) 4
        (by nlinarith only [hr21]) (by linarith) (by norm_num)) c
    have hl : (3*r^2-8)-c = 4 := by dsimp only [c]; ring
    have hu : (3*r^2+4)-c = 16 := by dsimp only [c]; ring
    rw [hl,hu] at hshift
    have he := henergy 2 (by norm_num) A (us A) (Gs A) (by
      norm_num only [show (2 : ℝ)^2 = 4 by norm_num,show (2 : ℝ)*4 = 8 by norm_num,
        show (4 : ℝ)*4 = 16 by norm_num,show (2 : ℝ)*2 = 4 by norm_num]
      exact hshift)
    norm_num only [show (2 : ℝ)^2 = 4 by norm_num,show (2 : ℝ)*4 = 8 by norm_num,
      show (3 : ℝ)*4 = 12 by norm_num,show (4 : ℝ)*4 = 16 by norm_num,
      show (2 : ℝ)*2 = 4 by norm_num] at he
    simpa only [E,S,V,U,vectorRms,scalarRms,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using he
  refine ⟨hscalar.1.of_le_mul hEm.aestronglyMeasurable hdom,?_⟩
  calc
    eLpNorm E (ENNReal.ofReal m) P ≤
        ENNReal.ofReal (D/2) * eLpNorm S (ENNReal.ofReal m) P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal (D/2) * ENNReal.ofReal
        (C * (r^2)^(-(1 : ℝ)/2 - (d : ℝ)/4)) := mul_le_mul_right hscalar.2 _
    _ = _ := by rw [← ENNReal.ofReal_mul (div_nonneg hD.le zero_le_two)]; congr 1; ring

end EinsteinRelation.Correctors
