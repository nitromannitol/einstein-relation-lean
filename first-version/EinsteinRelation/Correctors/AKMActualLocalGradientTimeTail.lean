import EinsteinRelation.Correctors.StochasticLocalGradientTail
import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Actual gradient tails from local spatial moments

Source: `paper/main.tex:800–808,843–849`. The required decay is a local
spatial RMS estimate, as provided by large-scale gradient regularity.
The carrier, coefficient law, and literal Euclidean tail are unchanged.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local spatial RMS moments of the actual gradient imply the sharp
stochastic time-tail bound. Source: `paper/main.tex:800–808,843–849`. -/
theorem actualCoefficientLaw_local_gradient_time_tail_moment_le
    {d : ℕ} (hd : 0 < d) {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G z.1 z.2))
    (ν : Measure (Vec d)) [SigmaFinite ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hsections : ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ t ∂volume.restrict (Ioi T), MemLp (fun x => G A (t,x)) 2 ν)
    (hdecay : ∀ t : ℝ, T < t →
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
  have hbound (t : ℝ) (ht : T < t) :
      eLpNorm (fun A => Real.sqrt (∫ x, ‖J (G A (t,x))‖^2 ∂ν)) p
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-(d : ℝ)/4)) := by
    simpa only [hsq] using hdecay t ht
  have htail := stochastic_local_gradient_tail_moment_le (actualCoefficientLaw Q) ν
    (fun z => J (G z.1 z.2)) (J.continuous.measurable.comp hG)
    hp hpt hC hα hT hJsections hbound
  have heq (A : Coefficient d (AKMUpperEllipticity L)) (x : Vec d) :
      ‖∫ t in Ioi T, J (G A (t,x))‖^2 = euclideanSq (∫ t in Ioi T, G A (t,x)) := by
    rw [J.integral_comp_comm,hsq]
  simpa only [heq] using htail.2

end EinsteinRelation.Correctors
