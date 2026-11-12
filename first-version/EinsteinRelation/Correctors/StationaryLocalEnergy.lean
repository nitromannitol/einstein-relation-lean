import EinsteinRelation.Correctors.StationaryWeightedOrbit
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Recovering global square integrability from stationary local energy

Source: `paper/main.tex:808–816,926–938`. Local energy is expressed as a
nonnegative extended integral, so its finiteness cannot result from a
nonintegrable Bochner integral being assigned zero.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Positive-volume finite expected local energy gives square integrability
of the actual stationary observable. Source: `paper/main.tex:808–816,926–938`. -/
theorem memLp_of_finite_stationary_local_energy' {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → E) (hF : Measurable F)
    {U : Set (Vec d)} (hUpos : 0 < volume U)
    (henergy : (∫⁻ ω, ∫⁻ x in U, ‖F (translate x ω)‖ₑ ^ (2 : ℝ) ∂volume ∂Q) < ⊤) :
    MemLp F 2 Q := by
  have hm : Measurable (fun z : FieldPair d × Vec d =>
      ‖F (translate z.2 z.1)‖ₑ ^ (2 : ℝ)) :=
    (measurable_enorm.comp (hF.comp
      (Probability.continuous_translate.comp continuous_swap).measurable)).pow_const _
  have hinner (x : Vec d) :
      (∫⁻ ω, ‖F (translate x ω)‖ₑ ^ (2 : ℝ) ∂Q) =
        ∫⁻ ω, ‖F ω‖ₑ ^ (2 : ℝ) ∂Q := by
    have hmeas : Measurable (fun ω => ‖F ω‖ₑ ^ (2 : ℝ)) :=
      (measurable_enorm.comp hF).pow_const _
    rw [← lintegral_map hmeas (Probability.measurable_translate x), hQ x]
  rw [lintegral_lintegral_swap hm.aemeasurable] at henergy
  simp_rw [hinner] at henergy
  rw [lintegral_const, Measure.restrict_apply_univ, mul_comm] at henergy
  have hfinite : (∫⁻ ω, ‖F ω‖ₑ ^ (2 : ℝ) ∂Q) < ⊤ := by
    by_contra! htop
    rw [top_unique htop, ENNReal.mul_top hUpos.ne'] at henergy
    exact lt_irrefl _ henergy
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simpa using hfinite

end EinsteinRelation.Correctors
