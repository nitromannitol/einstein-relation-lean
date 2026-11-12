import EinsteinRelation.Correctors.AKMFlowDoubleCylinderMoments

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
/-- Uniform scalar moments on a fixed positive-time rectangular cylinder
transfer through a deterministic endpoint estimate.
Source: `paper/main.tex:798–806,850–852`. -/
theorem prescribed_rectangular_scalar_to_gradient_moments_probability
    {d : ℕ} {K : ℝ} (P : Measure (Coefficient d K)) (hP : IsProbabilityMeasure P)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (H : Coefficient d K → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => u z.1 z.2))
    (hHm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => H z.1 z.2))
    {D C m t : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hm : 2 ≤ m) (ht : 1 ≤ t)
    (hval : ∀ s : ℝ, (1/2 : ℝ) ≤ s → ∀ x : Vec d,
      MemLp (fun A => u A (s,x)) (ENNReal.ofReal m) P ∧
      eLpNorm (fun A => u A (s,x)) (ENNReal.ofReal m) P ≤ ENNReal.ofReal C)
    (hbound : ∀ᵐ A ∂P, vectorRms volume (originBall d 1) (fun x => H A (t,x)) ≤
      D * scalarRms volume (Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4)
        (fun z => u A (z.1+(t-1),z.2))) :
    MemLp (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
      (ENNReal.ofReal m) P ∧
    eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => H A (t,x)))
      (ENNReal.ofReal m) P ≤ ENNReal.ofReal (D*C)  := by
  letI : IsProbabilityMeasure P := hP
  let V := originBall d 1
  let W := Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4
  let us := fun A (z : ℝ × Vec d) => u A (z.1+(t-1),z.2)
  let E := fun A => vectorRms volume V (fun x => H A (t,x))
  let S := fun A => scalarRms volume W (us A)
  have hshiftm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) =>
      (z.1,(z.2.1+(t-1),z.2.2))) :=
    measurable_fst.prodMk ((measurable_snd.fst.add measurable_const).prodMk measurable_snd.snd)
  have husm : Measurable (fun z : Coefficient d K × (ℝ × Vec d) => us z.1 z.2) :=
    hum.comp hshiftm
  have hopen : IsOpen (originBall d 4) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hvol := positiveTimeCylinder_volume_pos_finite (d := d)
    (by norm_num : (1/2 : ℝ) < 5/4) (by norm_num : (0 : ℝ) < 4)
  have hscalar := scalarL2_setAverage_moment_le P volume
    (measurableSet_Ioo.prod hopen.measurableSet) hvol.1 hvol.2 hm hC
    (fun z => us z.1 z.2) husm (fun z hz =>
      hval (z.1+(t-1)) (by linarith only [hz.1.1,ht]) z.2)
  have hrep : Measurable (fun z : Coefficient d K × Vec d => H z.1 (t,z.2)) :=
    hHm.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hgm : Measurable (fun z : Coefficient d K × Vec d => euclideanSq (H z.1 (t,z.2))) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp hrep).mul ((measurable_pi_apply j).comp hrep)
  have hEm : Measurable E := by
    have hi := (hgm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict V)).measurable
    simpa only [E,vectorRms,average_eq,measureReal_restrict_apply_univ,smul_eq_mul] using
      (measurable_const.mul hi).sqrt
  have hdom : ∀ᵐ A ∂P, ‖E A‖ ≤ D*‖S A‖ := by
    simpa only [E,S,V,W,us,vectorRms,scalarRms,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hbound
  refine ⟨hscalar.1.of_le_mul hEm.aestronglyMeasurable hdom,?_⟩
  calc
    eLpNorm E (ENNReal.ofReal m) P ≤ ENNReal.ofReal D * eLpNorm S (ENNReal.ofReal m) P :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom _
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal C := mul_le_mul_right hscalar.2 _
    _ = _ := (ENNReal.ofReal_mul hD).symm
end EinsteinRelation.Correctors
