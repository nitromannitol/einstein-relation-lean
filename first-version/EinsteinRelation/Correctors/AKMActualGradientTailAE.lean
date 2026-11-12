import EinsteinRelation.Correctors.StochasticGradientTailAE
import EinsteinRelation.Correctors.AKMActualLocalGradientTimeTail
import EinsteinRelation.Correctors.SemigroupGradientTailSlices

/-! # Actual semigroup tails with almost-everywhere time bounds

Source: `paper/main.tex:808–816,851–857`. The semigroup energy class
supplies the spatial slice integrability, and a time-null exceptional
set in the sharp moment estimate leaves the literal tail unchanged.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local spatial RMS moments of the actual gradient imply the sharp
stochastic time-tail bound. Source: `paper/main.tex:808–816,851–857`. -/
theorem actualCoefficientLaw_local_gradient_time_tail_moment_le_ae
    {d : ℕ} (hd : 0 < d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G z.1 z.2))
    (ν : Measure (Vec d)) [SigmaFinite ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hsections : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => G A (t,x)) 2 ν)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => Real.sqrt (∫ x, euclideanSq (G A (t,x)) ∂ν)) p
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-(d : ℝ)/4))) :
    MemLp (fun A => Real.sqrt (∫ x,
      euclideanSq (∫ t in Ioi T, G A (t,x)) ∂ν)) p (actualCoefficientLaw Q) ∧
    eLpNorm (fun A => Real.sqrt (∫ x,
      euclideanSq (∫ t in Ioi T, G A (t,x)) ∂ν)) p (actualCoefficientLaw Q) ≤
        ENNReal.ofReal ((C/((d : ℝ)/4))*T^(-((d : ℝ)/4))) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hα : 0 < (d : ℝ)/4 := div_pos (by exact_mod_cast hd) (by norm_num)
  have hsq (v : Vec d) : ‖J v‖^2 = euclideanSq v := by
    change ‖WithLp.toLp 2 v‖^2 = _
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
    exact Real.sq_sqrt (euclideanSq_nonneg_coords _)
  have hJsections : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => J (G A (t,x))) 2 ν := by
    filter_upwards [hsections] with A hA
    filter_upwards [hA] with t ht
    exact J.toContinuousLinearMap.comp_memLp' ht
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => Real.sqrt (∫ x, ‖J (G A (t,x))‖^2 ∂ν)) p
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-(d : ℝ)/4)) := by
    filter_upwards [hdecay] with t ht
    simpa only [hsq] using ht
  have htail := stochastic_local_gradient_tail_moment_le_ae (actualCoefficientLaw Q) ν
    (fun z => J (G z.1 z.2)) (J.continuous.measurable.comp hG)
    hp hpt hC hα hT hJsections hbound
  have heq (A : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :
      ‖∫ t in Ioi T, J (G A (t,x))‖^2 = euclideanSq (∫ t in Ioi T, G A (t,x)) := by
    rw [J.integral_comp_comm,hsq]
  simpa only [heq] using htail.2


/-- The actual gradient flow has the sharp stochastic tail on every
normalized origin ball. No separate spatial integrability hypothesis is
needed. Source: `paper/main.tex:808–816,851–857`. -/
theorem actualCoefficientLaw_semigroup_gradient_ball_tail_moment_le_ae
    {d : ℕ} (hd : 0 < d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G z.1 z.2))
    (hsol : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C T ρ : ℝ} (hC : 0 < C) (hT : 0 < T) (hρ : 0 < ρ)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => vectorRms volume (originBall d ρ) (fun x => G A (t,x))) p
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-(d : ℝ)/4))) :
    MemLp (fun A => vectorRms volume (originBall d ρ)
      (fun x => ∫ t in Ioi T, G A (t,x))) p (actualCoefficientLaw Q) ∧
    eLpNorm (fun A => vectorRms volume (originBall d ρ)
      (fun x => ∫ t in Ioi T, G A (t,x))) p (actualCoefficientLaw Q) ≤
        ENNReal.ofReal ((C/((d : ℝ)/4))*T^(-((d : ℝ)/4))) := by
  have hnorm (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    unfold euclideanSq dot
    rw [sq]
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ j)
  have hopen : IsOpen (originBall d ρ) := by
    unfold originBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hU0 : volume (originBall d ρ) ≠ 0 :=
    (hopen.measure_pos volume ⟨0,by simpa [originBall,euclideanNorm,euclideanSq,dot] using hρ⟩).ne'
  have hUfin : volume (originBall d ρ) ≠ ∞ := by
    have hmetric : (volume : Measure (Vec d)) (Metric.ball (0 : Vec d) ρ) ≠ ∞ :=
      Metric.isBounded_ball.measure_lt_top.ne
    apply ne_top_of_le_ne_top hmetric
    apply measure_mono
    intro x hx
    exact (show x ∈ Metric.ball (0 : Vec d) ρ from by
      rw [Metric.mem_ball,dist_zero_right]
      exact (hnorm x).trans_lt hx)
  let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hU0 hUfin⟩
  have hsections : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => G A (t,x)) 2 ν := by
    filter_upwards [hsol] with A hA
    have hs := semigroupSolution_gradient_tail_slice_memLp hA
      (hG.comp (measurable_const.prodMk measurable_id)) hT hρ
    filter_upwards [hs] with t ht
    exact ht.smul_measure (ENNReal.inv_ne_top.mpr hU0)
  have hb : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => Real.sqrt (∫ x, euclideanSq (G A (t,x)) ∂ν)) p
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-(d : ℝ)/4)) := by
    filter_upwards [hdecay] with t ht
    simpa only [vectorRms,setAverage_eq'] using ht
  simpa only [vectorRms,setAverage_eq'] using
    actualCoefficientLaw_local_gradient_time_tail_moment_le_ae hd Q G hG ν hp hpt
      hC hT hsections hb


end EinsteinRelation.Correctors
