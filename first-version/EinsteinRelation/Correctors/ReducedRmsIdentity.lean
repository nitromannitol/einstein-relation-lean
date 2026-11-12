import EinsteinRelation.Correctors.ReducedEnergyIdentity
import EinsteinRelation.Correctors.SpatialGradientTimeMinkowski

/-! # Exact spatial RMS transport for stationary realizations

Source: `paper/main.tex:800–808,842–849`. Local L2 membership justifies the
real RMS integral before the square-norm identity transfers its moment.
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A stationary realization has exactly the stochastic L2 norm of its
coefficient-space spatial RMS. No spatial point evaluation is involved.
Source: `paper/main.tex:800–808,842–849`. -/
theorem eLpNorm_eq_coefficient_rms_moment
    {d : ℕ} {L r₀ : ℝ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : EnvironmentLaw d L r₀) (f : FieldPair d → E) (hf : Measurable f)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → E)
    (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (hν : ν ≪ volume)
    (he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate (r₀ • x) (reduce ω.1)) =
        F (project (r₀ := r₀) Q.ellipticity_parameter ω) x)
    (hlocal : ∀ᵐ A ∂actualCoefficientLaw Q, MemLp (F A) 2 ν) :
    eLpNorm f 2 (reducedEnvironmentLaw Q) =
      eLpNorm (fun A => Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)) 2 (actualCoefficientLaw Q) := by
  have hs (A : Coefficient d (AKMUpperEllipticity L)) (hA : MemLp (F A) 2 ν) :
      ‖Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)‖ₑ^2 = ∫⁻ x, ‖F A x‖ₑ^2 ∂ν := by
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
      ← eLpNorm_two_eq_ofReal_spatial_rms ν hA]
    simpa using (eLpNorm_nnreal_pow_eq_lintegral
      (f := F A) (μ := ν) (p := (2 : ℝ≥0)) (by norm_num))
  have hsq : (eLpNorm f 2 (reducedEnvironmentLaw Q))^2 =
      (eLpNorm (fun A => Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)) 2 (actualCoefficientLaw Q))^2 := by
    rw [eLpNorm_sq_eq_coefficient_energy Q f hf F hF ν hν he]
    have hh := eLpNorm_nnreal_pow_eq_lintegral
      (f := fun A => Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)) (μ := actualCoefficientLaw Q)
      (p := (2 : ℝ≥0)) (by norm_num)
    have hh' : (eLpNorm (fun A => Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)) 2
        (actualCoefficientLaw Q))^2 =
        ∫⁻ A, ‖Real.sqrt (∫ x, ‖F A x‖^2 ∂ν)‖ₑ^2 ∂actualCoefficientLaw Q := by
      simpa using hh
    rw [hh']
    exact (lintegral_congr_ae (hlocal.mono fun A hA => hs A hA)).symm
  apply le_antisymm
  · exact (ENNReal.pow_le_pow_left_iff (n := 2) (by norm_num)).mp hsq.le
  · exact (ENNReal.pow_le_pow_left_iff (n := 2) (by norm_num)).mp hsq.ge

end EinsteinRelation.Correctors
