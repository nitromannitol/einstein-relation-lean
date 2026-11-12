import EinsteinRelation.Correctors.ReducedIntegratedGradientL2

/-! # Exact reduced-law square-norm transport

Source: `paper/main.tex:800–808,842–849`. Stationarity and the actual
physical-law maps identify a stationary observable's square norm with
the expected spatial energy of its specified coefficient-space realization.
All energies are nonnegative extended integrals.
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Exact square-norm transport at the physical finite-range scale.
The spatial probability may be any absolutely continuous observation law.
Source: `paper/main.tex:800–808,842–849`. -/
theorem eLpNorm_sq_eq_coefficient_energy
    {d : ℕ} {L r₀ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : EnvironmentLaw d L r₀) (f : FieldPair d → E) (hf : Measurable f)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → E)
    (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate (r₀ • x) (reduce ω.1)) =
        F (project (r₀ := r₀) Q.ellipticity_parameter ω) x) :
    (eLpNorm f 2 (reducedEnvironmentLaw Q))^2 =
      ∫⁻ A, ∫⁻ x, ‖F A x‖ₑ^2 ∂ν ∂actualCoefficientLaw Q := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  have hm : Measurable (fun p : FieldPair d × Vec d =>
      ‖f (translate (r₀ • p.2) p.1)‖ₑ^2) :=
    (hf.comp (Probability.continuous_translate.measurable.comp
      ((measurable_const.smul measurable_snd).prodMk measurable_fst))).enorm.pow_const 2
  have hinner (x : Vec d) :
      (∫⁻ ρ, ‖f (translate (r₀ • x) ρ)‖ₑ^2 ∂reducedEnvironmentLaw Q) =
        ∫⁻ ρ, ‖f ρ‖ₑ^2 ∂reducedEnvironmentLaw Q := by
    rw [← lintegral_map (hf.enorm.pow_const 2) (Probability.measurable_translate _),
      reducedEnvironmentLaw_stationary Q _]
  have hs : (eLpNorm f 2 (reducedEnvironmentLaw Q))^2 =
      ∫⁻ ρ, ∫⁻ x, ‖f (translate (r₀ • x) ρ)‖ₑ^2 ∂ν ∂reducedEnvironmentLaw Q := by
    rw [lintegral_lintegral_swap hm.aemeasurable]
    simp_rw [hinner]
    rw [lintegral_const,measure_univ,mul_one]
    simpa using
      (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := reducedEnvironmentLaw Q)
        (p := (2 : ℝ≥0)) (by norm_num))
  rw [hs,← (measurePreserving_physicalReduction Q).map_eq,
    lintegral_map hm.lintegral_prod_right' (measurePreserving_physicalReduction Q).measurable]
  have he' : (∫⁻ ω, ∫⁻ x, ‖f (translate (r₀ • x) (reduce ω.1))‖ₑ^2 ∂ν
      ∂physicalReferenceLaw Q) =
      ∫⁻ ω, ∫⁻ x, ‖F (project (r₀ := r₀) Q.ellipticity_parameter ω) x‖ₑ^2 ∂ν
        ∂physicalReferenceLaw Q := by
    apply lintegral_congr_ae
    filter_upwards [he] with ω hω
    exact lintegral_congr_ae ((hω.filter_mono hν.ae_le).mono fun x hx => congrArg (fun v : E => ‖v‖ₑ^2) hx)
  rw [he']
  rw [← (measurePreserving_akmProject Q).map_eq,
    lintegral_map (hF.enorm.pow_const 2).lintegral_prod_right'
      (measurePreserving_akmProject Q).measurable]

/-- Uniform coefficient-space point moments bound a reduced-law realization
without evaluating any spatial exceptional set at the origin.
Source: `paper/main.tex:800–808`. -/
theorem eLpNorm_le_of_coefficient_point_moments
    {d : ℕ} {L r₀ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : EnvironmentLaw d L r₀) (f : FieldPair d → E) (hf : Measurable f)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → E)
    (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate (r₀ • x) (reduce ω.1)) =
        F (project (r₀ := r₀) Q.ellipticity_parameter ω) x)
    {B : ℝ≥0∞} (hb : ∀ x, eLpNorm (fun A => F A x) 2 (actualCoefficientLaw Q) ≤ B) :
    eLpNorm f 2 (reducedEnvironmentLaw Q) ≤ B := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  apply (ENNReal.pow_le_pow_left_iff (n := 2) (by norm_num)).mp
  rw [eLpNorm_sq_eq_coefficient_energy Q f hf F hF ν hν he,
    lintegral_lintegral_swap (hF.enorm.pow_const 2).aemeasurable]
  calc
    (∫⁻ x, ∫⁻ A, ‖F A x‖ₑ^2 ∂actualCoefficientLaw Q ∂ν) ≤ ∫⁻ _x, B^2 ∂ν := by
      apply lintegral_mono
      intro x
      have hh := eLpNorm_nnreal_pow_eq_lintegral
        (f := fun A => F A x) (μ := actualCoefficientLaw Q) (p := (2 : ℝ≥0)) (by norm_num)
      have hb' := ENNReal.pow_le_pow_left (n := 2) (hb x)
      have hs : (eLpNorm (fun A => F A x) 2 (actualCoefficientLaw Q))^2 =
          ∫⁻ A, ‖F A x‖ₑ^2 ∂actualCoefficientLaw Q := by
        simpa using hh
      dsimp only
      rw [← hs]
      exact hb'
    _ = B^2 := by rw [lintegral_const,measure_univ,mul_one]

end EinsteinRelation.Correctors
