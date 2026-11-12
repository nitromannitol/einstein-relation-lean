import EinsteinRelation.Correctors.PrescribedGradientCylinderTransfer
import EinsteinRelation.Correctors.VectorRmsEnergy
import EinsteinRelation.Correctors.AKMFlowGoodRadiusCylinder

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Time-slice energy converts double-scale cylinder decay into prescribed-time
local gradient decay for the same scalar semigroup.
Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_prescribed_double_cylinder_le {d : ℕ} {K : ℝ}
    (hK : 0 < K) {χ : Vec d → ℝ}
    (hχ : IsSpatialTest (originBall d 2) χ) (hχb : ∀ x, |χ x| ≤ 1)
    (hχV : ∀ x ∈ originBall d 1, χ x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Coefficient d K) (v : Vec d → Vec d)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsSemigroupSolution A v u G → ∀ r : ℝ, 2 ≤ r →
      ∀ H : Vec d → Vec d, HasWeakGradient Set.univ (fun x => u (3*r^2,x)) H →
      MemLp (fun x => euclideanNorm (H x)) 2 (volume.restrict (originBall d 1)) ∧
      vectorRms volume (originBall d 1) H ≤
        D * vectorRms volume (Set.Ioo 8 12 ×ˢ originBall d 2)
          (fun z => G (z.1+(3*r^2-12),z.2)) := by
  let V := originBall d 1
  let U := originBall d 2
  have hopen (s : ℝ) : IsOpen (originBall d s) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hUcompact := isCompact_closure_originBall d 2
  have hVcompact := isCompact_closure_originBall d 1
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hUcompact.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  letI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hVcompact.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hV0 : 0 < volume.real V := by
    simpa only [V,originBall_eq_gt_ball] using
      paired_ball_volume_pos_finite (d := d) (by norm_num : (0 : ℝ) < 1)
  have hC0 : 0 < volume.real (Set.Ioo (8 : ℝ) 12 ×ˢ U) := by
    simpa only [U] using ENNReal.toReal_pos
      (positiveTimeCylinder_volume_pos_finite (d := d) (by norm_num : (8 : ℝ) < 12)
        (by norm_num : (0 : ℝ) < 2)).1
      (positiveTimeCylinder_volume_pos_finite (d := d) (by norm_num : (8 : ℝ) < 12)
        (by norm_num : (0 : ℝ) < 2)).2
  let D := Real.sqrt d * Real.sqrt (2*K/4+2*K^2*L^2) *
    Real.sqrt (volume.real (Set.Ioo (8 : ℝ) 12 ×ˢ U)) / Real.sqrt (volume.real V)
  refine ⟨max D 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro A v u G hsol r hr H hH
  let c := 3*r^2-12
  let us := fun z : ℝ × Vec d => u (z.1+c,z.2)
  let Gs := fun z : ℝ × Vec d => G (z.1+c,z.2)
  have hc : 0 ≤ c := by dsimp only [c]; nlinarith only [hr]
  have hus : ContinuousOn us (Set.Ioi 0 ×ˢ Set.univ) :=
    hsol.1.comp (by fun_prop) (by
      intro z hz
      exact ⟨add_pos_of_pos_of_nonneg hz.1 hc,Set.mem_univ _⟩)
  have hlocal : IsParabolicSolution A (Set.Ioo (8 : ℝ) 12) U us Gs :=
    by
      have hh := parabolicSolution_time_shift
        (hsol.2.1 (8+c) (12+c) 2 (by dsimp only [c]; nlinarith only [hr])
          (by linarith) (by norm_num)) c
      simpa only [add_sub_cancel_right] using hh
  have hHb : HasWeakGradient Set.univ (fun x => us (12,x)) H := by
    simpa only [us,c,show (12 : ℝ)+(3*r^2-12) = 3*r^2 by ring] using hH
  have hscalar : MemLp (fun x => us (12,x)) 2 (volume.restrict V) := by
    simpa only [us,c,show (12 : ℝ)+(3*r^2-12) = 3*r^2 by ring] using
      semigroupSolution_scalar_memLp_on_precompact hsol hVcompact
        (show 0 < 3*r^2 by nlinarith only [hr])
  obtain ⟨J,hw,hJL,hJb⟩ := parabolicSolution_prescribed_gradient_energy hK
    (by norm_num : (0 : ℝ) < 8) (by norm_num : (8 : ℝ) < 12) (hopen 2)
    (show V ⊆ U from fun x hx =>
      lt_of_lt_of_le (show euclideanNorm x < 1 from hx) (by norm_num))
    (hopen 1).measurableSet hus hlocal hscalar hχ hχb hχV hL hχD
  have heq : J =ᵐ[volume.restrict V] H := by
    filter_upwards [ae_all_iff.mpr fun j => weakPartialDerivative_ae_eq_on_open (hopen 1)
      (hw j) (hasWeakGradient_mono (Set.subset_univ V) hHb j)] with x hx
    exact funext hx
  have hHL := (memLp_congr_ae (heq.mono fun x hx => congrArg euclideanNorm hx)).mp hJL
  have hHbnd : (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict V)).toReal ≤
      Real.sqrt d * Real.sqrt ((2*K/4+2*K^2*L^2) *
        (∫ z in Set.Ioo (8 : ℝ) 12 ×ˢ U, euclideanSq (Gs z))) := by
    simpa only [show (12 : ℝ)-8 = 4 by norm_num,
      eLpNorm_congr_ae (heq.mono fun x hx => congrArg euclideanNorm hx)] using hJb
  rw [eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms volume V H hHL,
    Real.sqrt_mul (by positivity : 0 ≤ 2*K/4+2*K^2*L^2),
    sqrt_energy_eq_volume_mul_vectorRms volume _ hC0,← mul_assoc] at hHbnd
  have hfinal : vectorRms volume V H ≤ D * vectorRms volume
      (Set.Ioo (8 : ℝ) 12 ×ˢ U) Gs := by
    have hh : vectorRms volume V H ≤
        (Real.sqrt d * Real.sqrt (2*K/4+2*K^2*L^2) *
          Real.sqrt (volume.real (Set.Ioo (8 : ℝ) 12 ×ˢ U)) *
          vectorRms volume (Set.Ioo (8 : ℝ) 12 ×ˢ U) Gs) / Real.sqrt (volume.real V) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hV0)).mpr (by
        simpa only [Measure.real, mul_assoc, mul_comm, mul_left_comm] using hHbnd)
    convert hh using 1
    dsimp only [D,Measure.real]
    ring

  exact ⟨hHL,hfinal.trans (mul_le_mul_of_nonneg_right (le_max_left D 1)
    (Real.sqrt_nonneg _))⟩

end EinsteinRelation.Correctors
