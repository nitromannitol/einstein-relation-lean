import EinsteinRelation.Correctors.StationaryKernelConvolution
import Mathlib.MeasureTheory.Integral.Prod

/-! Source: `paper/main.tex:722,756`. Tonelli and stationarity compute
squared local L² norms without pointwise boundedness of the orbit. -/
open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation.Correctors

/-- Squaring a local L² norm gives the integral of the squared enorm,
including when either side is infinite. -/
theorem eLpNorm_two_sq_eq_lintegral_enorm_sq
    {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) :
    (eLpNorm f 2 ν)^2 = ∫⁻ x, ‖f x‖ₑ^2 ∂ν := by
  calc
    (eLpNorm f 2 ν)^2 = (eLpNorm f 2 ν)^((2 : ℕ) : ℝ) :=
      (ENNReal.rpow_natCast _ 2).symm
    _ = ∫⁻ x, ‖f x‖ₑ^((2 : ℕ) : ℝ) ∂ν :=
      eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    _ = ∫⁻ x, ‖f x‖ₑ^(2 : ℕ) ∂ν := by
      simp only [ENNReal.rpow_natCast]

/-- The expected square of a stationary local L² norm is exactly the
spatial mass times the squared environment L² norm. -/
theorem lintegral_stationary_local_L2_square {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [SFinite ν]
    (f : FieldPair d → ℝ) (hf : Measurable f) :
    (∫⁻ ω, (eLpNorm (fun x => f (translate x ω)) 2 ν)^2 ∂Q) =
      ν Set.univ * (eLpNorm f 2 Q)^2 := by
  have hmeas : Measurable (fun q : FieldPair d × Vec d =>
      ‖f (translate q.2 q.1)‖ₑ^2) :=
    (hf.comp (Probability.continuous_translate.measurable.comp measurable_swap)).enorm.pow_const 2
  simp_rw [eLpNorm_two_sq_eq_lintegral_enorm_sq]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have htranslate (x : Vec d) :
      (∫⁻ ω, ‖f (translate x ω)‖ₑ^2 ∂Q) = ∫⁻ ω, ‖f ω‖ₑ^2 ∂Q := by
    rw [← lintegral_map (hf.enorm.pow_const 2) (Probability.measurable_translate x), hQ x]
  simp_rw [htranslate]
  rw [lintegral_const, mul_comm]

end EinsteinRelation.Correctors
