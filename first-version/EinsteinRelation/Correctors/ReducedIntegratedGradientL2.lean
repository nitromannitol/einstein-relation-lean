import EinsteinRelation.Correctors.ReducedStationaryRealization
import EinsteinRelation.Correctors.UniformInitialEnergy
import EinsteinRelation.Correctors.StationaryLocalEnergy
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Actual finite-time gradients in reduced-law L2

Source: `paper/main.tex:800–808,842–849`. Stationarity converts the actual
local initial-layer energy into square integrability of the reduced-law
observable. Scaling the observation points instead of the environment law
retains the actual finite-range normalization.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Finite local energy of a rescaled stationary orbit gives genuine L2
membership. Source: `paper/main.tex:800–808`. -/
theorem memLp_of_finite_rescaled_stationary_energy {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : FieldPair d → E) (hf : Measurable f) (r : ℝ)
    {U : Set (Vec d)} (hU : 0 < volume U)
    (henergy : (∫⁻ ρ, ∫⁻ x in U, ‖f (translate (r • x) ρ)‖ₑ ^ (2 : ℝ) ∂volume ∂Q) < ⊤) :
    MemLp f 2 Q := by
  have hm : Measurable (fun p : FieldPair d × Vec d =>
      ‖f (translate (r • p.2) p.1)‖ₑ ^ (2 : ℝ)) :=
    (measurable_enorm.comp (hf.comp (Probability.continuous_translate.measurable.comp
      ((measurable_const.smul measurable_snd).prodMk measurable_fst)))).pow_const _
  have hinner (x : Vec d) :
      (∫⁻ ρ, ‖f (translate (r • x) ρ)‖ₑ ^ (2 : ℝ) ∂Q) =
        ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂Q := by
    have hmeas : Measurable (fun ρ => ‖f ρ‖ₑ ^ (2 : ℝ)) :=
      (measurable_enorm.comp hf).pow_const _
    rw [← lintegral_map hmeas (Probability.measurable_translate (r • x)),hQ (r • x)]
  rw [lintegral_lintegral_swap hm.aemeasurable] at henergy
  simp_rw [hinner] at henergy
  rw [lintegral_const,Measure.restrict_apply_univ,mul_comm] at henergy
  have hfinite : (∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂Q) < ⊤ := by
    by_contra! htop
    rw [top_unique htop,ENNReal.mul_top hU.ne'] at henergy
    exact lt_irrefl _ henergy
  refine ⟨hf.aestronglyMeasurable,?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simpa using hfinite

/-- Uniform physical local energy suffices for a specified stationary
realization to lie in reduced-law L2. The energy is an extended integral,
and its bound is justified by local L2 membership first.
Source: `paper/main.tex:800–808,844–849`. -/
theorem memLp_reduced_realization_of_uniform_coefficient_energy
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (f : FieldPair d → ℝ) (hf : Measurable f)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ)
    (he : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate (r₀ • x) (reduce ω.1)) =
        F (project (r₀ := r₀) Q.ellipticity_parameter ω) x)
    {C : ℝ}
    (hbound : ∀ᵐ A ∂actualCoefficientLaw Q,
      MemLp (F A) 2 (volume.restrict (originBall d 1)) ∧
        (∫ x in originBall d 1, (F A x)^2) ≤ C) :
    MemLp f 2 (reducedEnvironmentLaw Q) := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  have hU : 0 < volume (originBall d 1) := by
    have hh : 0 < (volume (originBall d 1)).toReal := by
      simpa only [Measure.real,originBall,ball,sub_zero] using
        ball_volume_pos_finite d 1 zero_lt_one
    exact (ENNReal.toReal_pos_iff.mp hh).1
  apply memLp_of_finite_rescaled_stationary_energy (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) f hf r₀ hU
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  rw [← (measurePreserving_physicalReduction Q).map_eq]
  apply (lintegral_map_le _ _).trans
  have hb : ∀ᵐ ω ∂physicalReferenceLaw Q,
      (∫⁻ x in originBall d 1, ‖f (translate (r₀ • x) (reduce ω.1))‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal C := by
    filter_upwards [he,(measurePreserving_akmProject Q).quasiMeasurePreserving.ae hbound]
      with ω hω hB
    rw [lintegral_congr_ae ((ae_restrict_of_ae hω).mono fun x hx => by rw [hx])]
    have hs (a : ℝ) : ENNReal.ofReal (a^2) = ‖a‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.rpow_two,← ofReal_norm_eq_enorm,← ENNReal.ofReal_pow (norm_nonneg a)]
      simp only [Real.norm_eq_abs,sq_abs]
    simp_rw [← hs]
    rw [← ofReal_integral_eq_lintegral_ofReal hB.1.integrable_sq (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hB.2
  simpa only [lintegral_const,measure_univ,mul_one] using lintegral_mono_ae hb

/-- A uniformly bounded covariant coefficient observable has an actual
reduced-law stationary L2 realization. Source: `paper/main.tex:800–808`. -/
theorem exists_reduced_L2_realization_of_bounded_covariant_field
    {d : ℕ} {L r₀ B : ℝ} (Q : EnvironmentLaw d L r₀)
    (F : Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ)
    (hF : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => F p.1 p.2))
    (hbound : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ x, ‖F A x‖ ≤ B)
    (hcov : ∀ z : Vec d, ∀ᵐ A ∂actualCoefficientLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)), F (translateCoefficient z A) x = F A (x+z)) :
    ∃ f : FieldPair d → ℝ, Measurable f ∧ MemLp f 2 (reducedEnvironmentLaw Q) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f (translate x (reduce ω.1)) =
          F (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) := by
  have hloc : ∀ᵐ A ∂actualCoefficientLaw Q, LocallyIntegrable (F A) volume := by
    filter_upwards [hbound] with A hA
    exact (locallyIntegrable_const B).mono
      ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (ae_of_all _ fun x => (hA x).trans (le_abs_self B))
  obtain ⟨f,hf,he⟩ := exists_reduced_realization_of_covariant_coefficient_field
    Q F hF hloc hcov
  refine ⟨f,hf,?_,he⟩
  refine memLp_reduced_realization_of_uniform_coefficient_energy Q f hf F
    (C := B^2*volume.real (originBall d 1)) ?_ ?_
  · have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
    filter_upwards [he] with ω hω
    filter_upwards [(Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hω]
      with x hx
    simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hx
  · filter_upwards [hbound] with A hA
    letI : IsFiniteMeasure (volume.restrict (originBall d 1)) := isFiniteMeasure_restrict.mpr
      (ne_top_of_le_ne_top ((isCompact_closure_originBall d 1).measure_ne_top (μ := volume))
        (measure_mono subset_closure))
    have hLp : MemLp (F A) 2 (volume.restrict (originBall d 1)) :=
      MemLp.of_bound ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B
        (ae_of_all _ hA)
    refine ⟨hLp,?_⟩
    have hh := integral_mono_ae hLp.integrable_sq (integrable_const (B^2))
      (ae_of_all (volume.restrict (originBall d 1)) fun x => by
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hA x) 2
        simpa only [Real.norm_eq_abs,sq_abs] using hh)
    simpa only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_comm] using hh

/-- Every specified canonical column flow has an actual stationary L2
realization of its zero-based finite-time gradient, without assuming that
gradient energy or stationary integrability. Joint coefficient measurability
is the input to be supplied by the kernel construction.
Source: `paper/main.tex:800–808,842–849`. -/
theorem exists_reduced_L2_integrated_gradient_realization
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    {T : ℝ} (hT : 0 < T) :
    ∃ Y : FieldPair d → Vec d, Measurable Y ∧ MemLp Y 2 (reducedEnvironmentLaw Q) ∧
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        Y (translate x (reduce ω.1)) =
          fun j => ∫ t in Set.Ioo 0 T,
            G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,r₀⁻¹ • x) j := by
  obtain ⟨Y,hY,he⟩ := exists_reduced_integrated_gradient_realization Q i u G hG hflow hT
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  obtain ⟨C,hC⟩ := exists_uniform_integrated_gradient_coordinate_energy_bound
    (B := (d : ℝ)*akmColumnLipschitzConstant d L r₀) hK hT zero_lt_one
  refine ⟨Y,hY,memLp_pi_iff.mpr (fun j => ?_),he⟩
  refine memLp_reduced_realization_of_uniform_coefficient_energy Q
    (fun ρ => Y ρ j) ((measurable_pi_apply j).comp hY)
    (fun A x => ∫ t in Set.Ioo 0 T, G A (t,x) j) (C := C) ?_ ?_
  · have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
    filter_upwards [he] with ω hω
    filter_upwards [(Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hω]
      with x hx
    simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using congrFun hx j
  · filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
      with A hA hb
    exact hC A _ (u A) (G A) hA.1 hb j

end EinsteinRelation.Correctors
