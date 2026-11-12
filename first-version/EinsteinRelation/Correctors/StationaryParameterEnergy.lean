import EinsteinRelation.Correctors.StationaryParameterAverages
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Tonelli identifies actual local stationary energy before any finiteness assumption
(`paper/main.tex:808–816,926–938`). -/
theorem lintegral_stationary_param_energy {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → E) (hF : Measurable F)
    (ν : Measure (Vec d)) [SFinite ν] (p : ℝ) :
    (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂ν ∂Q) =
      ν Set.univ * (∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q) := by
  have hjoint : Measurable (fun q : Vec d × FieldPair d => translate q.1 q.2) :=
    Probability.continuous_translate.measurable
  have ht : Measurable (fun q : FieldPair d × Vec d => translate q.2 q.1) :=
    hjoint.comp measurable_swap
  have hmeas : Measurable (fun q : FieldPair d × Vec d => ‖F (translate q.2 q.1)‖ₑ ^ p) :=
    ((hF.comp ht).enorm).pow_const p
  have hinv : ∀ x : Vec d, ∫⁻ ω, ‖F (translate x ω)‖ₑ ^ p ∂Q = ∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q := by
    intro x
    rw [← lintegral_map (hF.enorm.pow_const p) (Probability.measurable_translate x), hQ x]
  calc
    (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂ν ∂Q) =
        ∫⁻ x, ∫⁻ ω, ‖F (translate x ω)‖ₑ ^ p ∂Q ∂ν :=
      lintegral_lintegral_swap (f := fun ω x => ‖F (translate x ω)‖ₑ ^ p) hmeas.aemeasurable
    _ = ∫⁻ x, ∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q ∂ν := lintegral_congr fun x => hinv x
    _ = ν Set.univ * (∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q) := by
      rw [lintegral_const]
      exact mul_comm _ _

end EinsteinRelation.Correctors
