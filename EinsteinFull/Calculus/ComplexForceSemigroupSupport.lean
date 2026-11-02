import EinsteinFull.Calculus.ComplexForceEvolutionGeneratorSupport

/-!
# The actual forced stationary complex L2 semigroup

Undo the proved structural scalar shift of the contraction family. Both
inclusions of the full infinitesimal generator graph are retained. No
analyticity in force, Lp estimate or physical realization is asserted here.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The forced stationary evolution, obtained from the actual shifted Yosida limit. -/
def forcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ) •
    shiftedForcedComplexEvolution Q i ζ t

/-- The actual forced evolution starts at the identity. -/
theorem forcedComplexEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    forcedComplexEvolution Q i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  simp only [forcedComplexEvolution, NNReal.coe_zero, mul_zero, Real.exp_zero,
    Complex.ofReal_one, one_smul, shiftedForcedComplexEvolution_zero]

/-- The actual forced evolution satisfies the semigroup law. -/
theorem forcedComplexEvolution_add {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0) :
    forcedComplexEvolution Q i ζ (s+t) =
      (forcedComplexEvolution Q i ζ s).comp (forcedComplexEvolution Q i ζ t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [forcedComplexEvolution, NNReal.coe_add, mul_add, Real.exp_add,
    Complex.ofReal_mul, ContinuousLinearMap.smul_apply, shiftedForcedComplexEvolution_add,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul, mul_comm]

/-- The actual forced evolution is strongly continuous on all complex L2. -/
theorem continuous_forcedComplexEvolution_apply {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => forcedComplexEvolution Q i ζ t f) :=
  (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe))).smul
    (continuous_shiftedForcedComplexEvolution_apply Q i ζ f)

/-- The actual forced evolution has the proved quadratic-force exponential growth bound. -/
theorem norm_forcedComplexEvolution_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖forcedComplexEvolution Q i ζ t f‖ ≤
      Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ := by
  change ‖(Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ) •
    shiftedForcedComplexEvolution Q i ζ t f‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_shiftedForcedComplexEvolution_apply_le Q i ζ t f)
    (Real.exp_pos _).le

/-- The actual forced evolution has the corresponding operator norm bound. -/
theorem norm_forcedComplexEvolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    ‖forcedComplexEvolution Q i ζ t‖ ≤ Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) := by
  exact (forcedComplexEvolution Q i ζ t).opNorm_le_bound (Real.exp_pos _).le
    (norm_forcedComplexEvolution_apply_le Q i ζ t)

private theorem tendsto_coe_right_zero :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨(NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin⟩

private theorem tendsto_exp_factor (a : ℝ) :
    Tendsto (fun t : ℝ≥0 => (Real.exp (a * (t : ℝ)) : ℂ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 1) := by
  have h := (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const (y := a)).fun_mul NNReal.continuous_coe))).tendsto
      (0 : ℝ≥0)
  simpa only [Function.comp_def, NNReal.coe_zero, mul_zero, Real.exp_zero,
    Complex.ofReal_one] using
    h.mono_left (show (𝓝[>] (0 : ℝ≥0)) ≤ 𝓝 0 from nhdsWithin_le_nhds)

private theorem tendsto_exp_slope (a : ℝ) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ *
      ((Real.exp (a * (t : ℝ)) : ℂ) - 1)) (𝓝[>] (0 : ℝ≥0)) (𝓝 (a : ℂ)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (a*t)) a 0 := by
    simpa only [id_eq, mul_zero, mul_one, Real.exp_zero, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).const_mul a).exp
  have h := hd.tendsto_slope_zero_right.comp tendsto_coe_right_zero
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  simpa only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul, Function.comp_def,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one] using hc

private theorem evolution_slope_identity {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ((t : ℝ) : ℂ)⁻¹ • (forcedComplexEvolution Q i ζ t f-f) =
      (Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ) •
        (((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f-f)) +
      (((t : ℝ) : ℂ)⁻¹ * ((Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ)-1)) • f := by
  change ((t : ℝ) : ℂ)⁻¹ •
    ((Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ) •
      shiftedForcedComplexEvolution Q i ζ t f-f) = _
  module

/-- The complete actual forced generator graph equals the full frozen weak graph. -/
theorem tendsto_forcedComplexEvolution_slope_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (forcedComplexEvolution Q i ζ t f-f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexGeneratorPair Q i ζ f g := by
  have hc := tendsto_exp_factor (complexForceShift d Λ₀ ζ)
  have hb := tendsto_exp_slope (complexForceShift d Λ₀ ζ)
  constructor
  · intro h
    have hz := (hc.inv₀ one_ne_zero).smul (h.sub (hb.smul (tendsto_const_nhds (x := f))))
    simp only [inv_one, one_smul] at hz
    have he (t : ℝ≥0) :
        (Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ)⁻¹ •
          (((t : ℝ) : ℂ)⁻¹ • (forcedComplexEvolution Q i ζ t f-f) -
            (((t : ℝ) : ℂ)⁻¹ * ((Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) : ℂ)-1)) • f) =
        ((t : ℝ) : ℂ)⁻¹ • (shiftedForcedComplexEvolution Q i ζ t f-f) := by
      rw [evolution_slope_identity, add_sub_cancel_right, smul_smul,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), one_smul]
    simp_rw [he] at hz
    have hh := (tendsto_shiftedForcedComplexEvolution_slope_iff Q i ζ f
      (g - (complexForceShift d Λ₀ ζ : ℂ) • f)).mp hz
    simpa only [sub_add_cancel] using hh
  · intro h
    have hz := (hc.smul h.tendsto_shiftedForcedComplexEvolution_slope).add
      (hb.smul (tendsto_const_nhds (x := f)))
    simp only [one_smul, sub_add_cancel] at hz
    simpa only [← evolution_slope_identity] using hz

/-- The constructed forced family satisfies the complete frozen semigroup predicate. -/
theorem isComplexEnvironmentSemigroup_forcedComplexEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    IsComplexEnvironmentSemigroup Q i ζ (forcedComplexEvolution Q i ζ) :=
  ⟨forcedComplexEvolution_zero Q i ζ, forcedComplexEvolution_add Q i ζ,
    continuous_forcedComplexEvolution_apply Q i ζ,
    tendsto_forcedComplexEvolution_slope_iff Q i ζ⟩

end EinsteinFull
