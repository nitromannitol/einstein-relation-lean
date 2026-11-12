import EinsteinRelation.Correctors.PrescribedGradientDoubleCylinder
import EinsteinRelation.Correctors.ParabolicCutoffRms

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
/-- A fixed past endpoint estimate from scalar energy in a slightly larger
rectangular cylinder. Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_prescribed_rectangular_scalar_le {d : ℕ} {K : ℝ}
    (hK : 0 < K) (ζ : ℝ × Vec d → ℝ) {M : ℝ} (hM : 0 < M)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζs : tsupport ζ ⊆ Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4)
    (hζ1 : ∀ z ∈ Set.Icc (3/4 : ℝ) 1 ×ˢ originBall d 2, ζ z = 1)
    (hζD : ∀ z, 2*ζ z*fderiv ℝ ζ z (1,0) +
      4*K^2*euclideanSq (fun j => fderiv ℝ ζ z (0,unitVector j)) ≤ M)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 2) χ)
    (hχb : ∀ x, |χ x| ≤ 1) (hχ1 : ∀ x ∈ originBall d 1, χ x = 1)
    {L : ℝ} (hL : 0 ≤ L) (hχD : ∀ x, euclideanNorm (gradient χ x) ≤ L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : Coefficient d K) (v : Vec d → Vec d)
      (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsSemigroupSolution A v u G → ∀ t : ℝ, 1 ≤ t →
      ∀ H : Vec d → Vec d, HasWeakGradient Set.univ (fun x => u (t,x)) H →
      vectorRms volume (originBall d 1) H ≤
        D * scalarRms volume (Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4)
          (fun z => u (z.1+(t-1),z.2))  := by
  let V := originBall d 1
  let U := originBall d 2
  let W := Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4
  let I := Set.Ioo (3/4 : ℝ) 1 ×ˢ U
  have hopen (r : ℝ) : IsOpen (originBall d r) := by
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
  have hIv := positiveTimeCylinder_volume_pos_finite (d := d)
    (by norm_num : (3/4 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
  have hWv := positiveTimeCylinder_volume_pos_finite (d := d)
    (by norm_num : (1/2 : ℝ) < 5/4) (by norm_num : (0 : ℝ) < 4)
  have hI0 : 0 < volume.real I := ENNReal.toReal_pos hIv.1 hIv.2
  let D₁ := Real.sqrt d * Real.sqrt (2*K/(1/4)+2*K^2*L^2) *
    Real.sqrt (volume.real I) / Real.sqrt (volume.real V)
  let D₂ := Real.sqrt (M * volume.real W / volume.real I)
  have hD₁ : 0 ≤ D₁ := by dsimp only [D₁]; positivity
  refine ⟨max (D₁*D₂) 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro A v u G hsol t ht H hH
  let c := t-1
  let us := fun z : ℝ × Vec d => u (z.1+c,z.2)
  let Gs := fun z : ℝ × Vec d => G (z.1+c,z.2)
  have hc : 0 ≤ c := by dsimp only [c]; linarith only [ht]
  have hus : ContinuousOn us (Set.Ioi 0 ×ˢ Set.univ) :=
    hsol.1.comp (by fun_prop) (by
      intro z hz
      exact ⟨add_pos_of_pos_of_nonneg hz.1 hc,Set.mem_univ _⟩)
  have hlocal : IsParabolicSolution A (Set.Ioo (3/4 : ℝ) 1) U us Gs := by
    have hh := parabolicSolution_time_shift
      (hsol.2.1 (3/4+c) (1+c) 2 (by linarith only [hc])
        (by linarith) (by norm_num)) c
    simpa only [add_sub_cancel_right] using hh
  have houter : IsParabolicSolution A (Set.Ioo (1/2 : ℝ) (5/4))
      (originBall d 4) us Gs := by
    have hh := parabolicSolution_time_shift
      (hsol.2.1 (1/2+c) (5/4+c) 4 (by linarith only [hc])
        (by linarith) (by norm_num)) c
    simpa only [add_sub_cancel_right] using hh
  have hHb : HasWeakGradient Set.univ (fun x => us (1,x)) H := by
    simpa only [us,c,show (1 : ℝ)+(t-1) = t by ring] using hH
  have hscalar : MemLp (fun x => us (1,x)) 2 (volume.restrict V) := by
    simpa only [us,c,show (1 : ℝ)+(t-1) = t by ring] using
      semigroupSolution_scalar_memLp_on_precompact hsol hVcompact
        (show 0 < t by linarith only [ht])
  obtain ⟨J,hw,hJL,hJb⟩ := parabolicSolution_prescribed_gradient_energy hK
    (by norm_num : (0 : ℝ) < 3/4) (by norm_num : (3/4 : ℝ) < 1) (hopen 2)
    (show V ⊆ U from fun x hx =>
      lt_of_lt_of_le (show euclideanNorm x < 1 from hx) (by norm_num))
    (hopen 1).measurableSet hus hlocal hscalar hχ hχb hχ1 hL hχD
  have heq : J =ᵐ[volume.restrict V] H := by
    filter_upwards [ae_all_iff.mpr fun j => weakPartialDerivative_ae_eq_on_open (hopen 1)
      (hw j) (hasWeakGradient_mono (Set.subset_univ V) hHb j)] with x hx
    exact funext hx
  have hHL := (memLp_congr_ae (heq.mono fun x hx => congrArg euclideanNorm hx)).mp hJL
  have hHbnd : (eLpNorm (fun x => euclideanNorm (H x)) 2 (volume.restrict V)).toReal ≤
      Real.sqrt d * Real.sqrt ((2*K/(1/4)+2*K^2*L^2) *
        (∫ z in I, euclideanSq (Gs z))) := by
    simpa only [I,show (1 : ℝ)-3/4 = 1/4 by norm_num,
      eLpNorm_congr_ae (heq.mono fun x hx => congrArg euclideanNorm hx)] using hJb
  rw [eLpNorm_euclideanNorm_toReal_eq_volume_mul_rms volume V H hHL,
    Real.sqrt_mul (by positivity : 0 ≤ 2*K/(1/4)+2*K^2*L^2),
    sqrt_energy_eq_volume_mul_vectorRms volume _ hI0,← mul_assoc] at hHbnd
  have hfinal : vectorRms volume V H ≤ D₁ * vectorRms volume I Gs := by
    have hh : vectorRms volume V H ≤
        (Real.sqrt d * Real.sqrt (2*K/(1/4)+2*K^2*L^2) *
          Real.sqrt (volume.real I) * vectorRms volume I Gs) / Real.sqrt (volume.real V) :=
      (le_div_iff₀ (Real.sqrt_pos.mpr hV0)).mpr (by
        simpa only [Measure.real,mul_assoc,mul_comm,mul_left_comm] using hHbnd)
    convert hh using 1
    dsimp only [D₁,Measure.real]
    ring
  have hi : vectorRms volume I Gs ≤ D₂ * scalarRms volume W us := by
    apply parabolicSolution_inner_rms_le hK measurableSet_Ioo (hopen 4) houter
      hζ hζc (by simpa only [interior_Ioo] using hζs)
      (measurableSet_Ioo.prod (hopen 2).measurableSet) ?_ hIv.1 hIv.2 hWv.2
      ?_ hM.le (fun z _ => hζD z)
    · intro z hz
      exact ⟨⟨by linarith only [hz.1.1],by linarith only [hz.1.2]⟩,
        lt_of_lt_of_le (show euclideanNorm z.2 < 2 from hz.2) (by norm_num)⟩
    · intro z hz
      exact hζ1 z ⟨⟨hz.1.1.le,hz.1.2.le⟩,hz.2⟩
  exact (hfinal.trans (mul_le_mul_of_nonneg_left hi hD₁)).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right (le_max_left (D₁*D₂) 1)
      (Real.sqrt_nonneg (⨍ z in W, (us z)^2))))
end EinsteinRelation.Correctors
