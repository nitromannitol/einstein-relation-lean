import EinsteinRelation.Correctors.L2ParameterAverageMap
import EinsteinRelation.Correctors.L2ParameterAverage
import EinsteinRelation.Correctors.L2MultiplierCurve

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The literal weighted parameter integral has its actual differentiable
L² realization. Source: `paper/main.tex:798–806`; temporal regularization. -/
theorem exists_differentiable_L2_parameter_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    {f : Ω × X → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (m m' : ℝ → Ω × X → ℝ)
    (hm : ∀ t, AEStronglyMeasurable (m t) (μ.prod ν))
    (hm' : ∀ t, AEStronglyMeasurable (m' t) (μ.prod ν))
    (hd : ∀ t z, HasDerivAt (fun s => m s z) (m' t z) t)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t z, |m t z| ≤ C) (hb' : ∀ t z, |m' t z| ≤ D) :
    ∃ F F' : ℝ → Lp ℝ 2 ν,
      (∀ t, (F t : X → ℝ) =ᵐ[ν] fun x => ∫ ω, m t (ω,x) * f (ω,x) ∂μ) ∧
      (∀ t, (F' t : X → ℝ) =ᵐ[ν] fun x => ∫ ω, m' t (ω,x) * f (ω,x) ∂μ) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  obtain ⟨T,hT,hTr⟩ := exists_L2_parameter_average_map μ ν
    (fun f => memLp_two_parameter_average μ ν (Lp.memLp f))
  obtain ⟨F,F',hF,hF',hder⟩ := exists_differentiable_L2_multiplier_curve
    (μ.prod ν) hf m m' hm hm' hd hC hD hb hb'
  refine ⟨fun t => T (F t), fun t => T (F' t), ?_, ?_, ?_⟩
  · intro t
    apply (hTr (F t)).trans
    have hsecswap := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq (hF t))
    filter_upwards [hsecswap] with x hx
    exact integral_congr_ae hx
  · intro t
    apply (hTr (F' t)).trans
    have hsecswap := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq (hF' t))
    filter_upwards [hsecswap] with x hx
    exact integral_congr_ae hx
  · intro t
    exact T.hasFDerivAt.comp_hasDerivAt t (hder t)

end EinsteinRelation.Correctors
