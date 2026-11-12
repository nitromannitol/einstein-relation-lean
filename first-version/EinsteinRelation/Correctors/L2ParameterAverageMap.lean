import EinsteinRelation.Correctors.L2ParameterAverage

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Averaging on a finite product gives its actual continuous L² operator.
Source: `paper/main.tex:798–806`; temporal regularization. -/
theorem exists_L2_parameter_average_map {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    (havg : ∀ f : Lp ℝ 2 (μ.prod ν),
      MemLp (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ∧
      eLpNorm (fun x => ∫ ω, f (ω,x) ∂μ) 2 ν ≤ eLpNorm f 2 (μ.prod ν)) :
    ∃ T : Lp ℝ 2 (μ.prod ν) →L[ℝ] Lp ℝ 2 ν,
      ‖T‖ ≤ 1 ∧ ∀ f : Lp ℝ 2 (μ.prod ν),
        (T f : X → ℝ) =ᵐ[ν] fun x => ∫ ω, f (ω,x) ∂μ := by
  let av (f : Lp ℝ 2 (μ.prod ν)) : X → ℝ := fun x => ∫ ω, f (ω,x) ∂μ
  let T0 (f : Lp ℝ 2 (μ.prod ν)) := (havg f).1.toLp (av f)
  have hrep f : (T0 f : X → ℝ) =ᵐ[ν] av f := (havg f).1.coeFn_toLp
  have hsec (f : Lp ℝ 2 (μ.prod ν)) : ∀ᵐ x ∂ν, Integrable (fun ω => f (ω,x)) μ :=
    ((Lp.memLp f).integrable (by norm_num)).prod_left_ae
  let L : Lp ℝ 2 (μ.prod ν) →ₗ[ℝ] Lp ℝ 2 ν :=
    { toFun := T0
      map_add' := by
        intro f g
        have hae := Measure.ae_ae_of_ae_prod
          ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq (Lp.coeFn_add f g))
        apply Lp.ext
        filter_upwards [hrep (f+g),Lp.coeFn_add (T0 f) (T0 g),hrep f,hrep g,
          hsec f,hsec g,hae] with x h1 h2 h3 h4 h5 h6 h7
        rw [h1,h2]
        change (∫ ω, (f+g) (ω,x) ∂μ) = T0 f x + T0 g x
        change (fun ω => (f+g) (ω,x)) =ᵐ[μ] (fun ω => f (ω,x)+g (ω,x)) at h7
        rw [integral_congr_ae h7,integral_add h5 h6,h3,h4]
      map_smul' := by
        intro c f
        have hae := Measure.ae_ae_of_ae_prod
          ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq (Lp.coeFn_smul c f))
        apply Lp.ext
        filter_upwards [hrep (c • f),Lp.coeFn_smul c (T0 f),hrep f,hae]
          with x h1 h2 h3 h4
        change T0 (c • f) x = (c • T0 f) x
        rw [h1,h2]
        change (∫ ω, (c • f) (ω,x) ∂μ) = c * T0 f x
        change (fun ω => (c • f) (ω,x)) =ᵐ[μ] (fun ω => c * f (ω,x)) at h4
        rw [integral_congr_ae h4]
        simp only [integral_const_mul]
        rw [h3] }
  have hb f : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖(havg f).1.toLp (av f)‖ ≤ _
    rw [Lp.norm_toLp,Lp.norm_def,one_mul]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (havg f).2
  refine ⟨L.mkContinuous 1 hb,LinearMap.mkContinuous_norm_le _ (by norm_num) hb,?_⟩
  exact hrep

end EinsteinRelation.Correctors
