import EinsteinRelation.Correctors.FiniteIncrementMoment
import EinsteinRelation.Correctors.ReducedRmsIdentity

/-! # Reduced-law gradient increment bounds

Source: `paper/main.tex:800–808`. The actual local energy and RMS estimates
are transported through spatial orbit identities. These are bounds for
the specified finite integrals, without point evaluation of null sets.
-/

open MeasureTheory Set
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A stationary finite-time gradient difference inherits the sharp actual
coefficient-space tail bound. Source: `paper/main.tex:800–808`. -/
theorem reduced_gradient_increment_bound
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → EuclideanSpace ℝ (Fin d))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    {C α T S : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T) (hTS : T ≤ S)
    (hfinite : ∀ᵐ A ∂actualCoefficientLaw Q, MemLp (G A) 2
      ((volume.restrict (Ioo 0 S)).prod ν))
    (hsections : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => G A (t,x)) 2 ν)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun A => Real.sqrt (∫ x, ‖G A (t,x)‖^2 ∂ν)) 2
        (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-α)))
    (YS YT : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      YS (translate (r₀ • x) (reduce ω.1)) - YT (translate (r₀ • x) (reduce ω.1)) =
        (∫ t in Ioo 0 S, G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x)) -
        ∫ t in Ioo 0 T, G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x)) :
    ‖YS-YT‖ ≤ (C/α)*T^(-α) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  let F : Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d) :=
    fun A x => (∫ t in Ioo 0 S, G A (t,x)) - ∫ t in Ioo 0 T, G A (t,x)
  have hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2) := by
    have hm : Measurable (fun p : (Coefficient d (AKMUpperEllipticity L) × Vec d) × ℝ =>
        G p.1.1 (p.2,p.1.2)) :=
      hG.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable.sub
      hm.stronglyMeasurable.integral_prod_right'.measurable
  have hm := initial_gradient_increment_moment (actualCoefficientLaw Q) ν
    (fun p => G p.1 p.2) hG (by norm_num) (by norm_num) hC hα hT hTS
    hfinite hsections hdecay
  have hid := eLpNorm_eq_coefficient_rms_moment Q
    (fun ρ => YS ρ-YT ρ) ((Lp.stronglyMeasurable YS).measurable.sub
      (Lp.stronglyMeasurable YT).measurable) F hF ν hν he hm.1
  have hb : eLpNorm (fun ρ => YS ρ-YT ρ) 2 (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal ((C/α)*T^(-α)) := hid.trans_le hm.2
  have hb' : eLpNorm (YS-YT) 2 (reducedEnvironmentLaw Q) ≤
      ENNReal.ofReal ((C/α)*T^(-α)) :=
    (eLpNorm_congr_ae (Lp.coeFn_sub YS YT)).trans_le hb
  rw [← Lp.enorm_def, ← ofReal_norm_eq_enorm] at hb'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb' 

end EinsteinRelation.Correctors
