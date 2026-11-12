import EinsteinRelation.Correctors.StationaryParameterEnergy
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:727-731`. A local annealed gradient bound
on a physical realization gives the origin moment by stationarity. -/
theorem lintegral_origin_rpow_le_of_physical_local_bound
    {d : ℕ} {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (Q : Measure (FieldPair d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {T : Ω → FieldPair d}
    (hT : MeasurePreserving T P Q) (hQ : IsStationary Q)
    (F : FieldPair d → E) (hF : Measurable F)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (hν : ν Set.univ ≠ 0) (p : ℝ) (hp : 0 ≤ p) (B : ℝ≥0∞)
    (hb : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (‖F (translate x (T ω))‖ ^ p) ∂ν ∂P) ≤
      ν Set.univ * B) :
    (∫⁻ ω, ENNReal.ofReal (‖F ω‖ ^ p) ∂Q) ≤ B := by
  -- helper: convert between ENNReal.ofReal (‖v‖ ^ p) and ‖v‖ₑ ^ p
  have h_enorm_eq (v : E) : ENNReal.ofReal (‖v‖ ^ p) = ‖v‖ₑ ^ p := by
    calc
      ENNReal.ofReal (‖v‖ ^ p) = (ENNReal.ofReal ‖v‖) ^ p := by
        rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]
      _ = ‖v‖ₑ ^ p := by rw [ofReal_norm_eq_enorm v]
  have hνfin : ν Set.univ ≠ ∞ := measure_ne_top ν Set.univ
  -- convert the hypothesis to use enorm
  have hb_enorm : (∫⁻ ω, ∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν ∂P) ≤ ν Set.univ * B := by
    have h_inner (ω : Ω) : (∫⁻ x, ENNReal.ofReal (‖F (translate x (T ω))‖ ^ p) ∂ν) =
        (∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν) := by
      apply lintegral_congr
      intro x
      rw [h_enorm_eq (F (translate x (T ω)))]
    calc
      (∫⁻ ω, ∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν ∂P) =
          (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (‖F (translate x (T ω))‖ ^ p) ∂ν ∂P) := by
        refine lintegral_congr fun ω => ?_
        rw [h_inner ω]
      _ ≤ ν Set.univ * B := hb
  -- define f(ω, x) = ‖F (translate x ω)‖ₑ ^ p, which is jointly measurable
  let f : FieldPair d → Vec d → ℝ≥0∞ := fun ω x => ‖F (translate x ω)‖ₑ ^ p
  have h_joint : Measurable (Function.uncurry f) := by
    have h_translate : Measurable (fun (q : FieldPair d × Vec d) => translate q.2 q.1) :=
      Probability.continuous_translate.measurable.comp measurable_swap
    have : (Function.uncurry f) = (fun (q : FieldPair d × Vec d) => ‖F (translate q.2 q.1)‖ₑ ^ p) := rfl
    rw [this]
    exact ((hF.comp h_translate).enorm).pow_const p
  -- g(ω) = ∫⁻ x, f(ω, x) ∂ν is measurable
  have h_meas_g : Measurable (fun (ω : FieldPair d) => ∫⁻ x, f ω x ∂ν) :=
    h_joint.lintegral_prod_right
  -- relate the double integral over P to the double integral over Q via measure-preserving
  have h_double_eq : (∫⁻ ω, ∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν ∂P) =
      (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂ν ∂Q) := by
    calc
      (∫⁻ ω, ∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν ∂P) =
          (∫⁻ ω, (fun (ω' : FieldPair d) => ∫⁻ x, ‖F (translate x ω')‖ₑ ^ p ∂ν) (T ω) ∂P) := rfl
      _ = (∫⁻ ω, (fun (ω' : FieldPair d) => ∫⁻ x, ‖F (translate x ω')‖ₑ ^ p ∂ν) ω ∂Q) := by
        rw [hT.lintegral_comp h_meas_g]
      _ = (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂ν ∂Q) := rfl
  -- combine everything
  have h_main : ν Set.univ * (∫⁻ ω, ENNReal.ofReal (‖F ω‖ ^ p) ∂Q) ≤ ν Set.univ * B := by
    calc
      ν Set.univ * (∫⁻ ω, ENNReal.ofReal (‖F ω‖ ^ p) ∂Q) =
          ν Set.univ * (∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q) := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [h_enorm_eq (F ω)]
      _ = (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂ν ∂Q) := by
        rw [lintegral_stationary_param_energy Q hQ F hF ν p]
      _ = (∫⁻ ω, ∫⁻ x, ‖F (translate x (T ω))‖ₑ ^ p ∂ν ∂P) := by rw [h_double_eq]
      _ ≤ ν Set.univ * B := hb_enorm
  -- cancel ν Set.univ (nonzero and finite)
  rw [ENNReal.mul_le_mul_iff_right hν hνfin] at h_main
  exact h_main
end EinsteinRelation.Correctors
