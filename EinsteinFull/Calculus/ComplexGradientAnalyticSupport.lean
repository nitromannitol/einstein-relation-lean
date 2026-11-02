import EinsteinFull.Calculus.ComplexForceAnalyticSupport

/-!
# Entire force dependence of the actual positive-time gradient

Bounded evaluation of the square-root-weighted orbit gives short-time gradient
analyticity. Factorization through that short time and the already entire
semigroup gives operator-norm analyticity at every complex force.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}

/-- At positive time, bounded orbit evaluation recovers the actual gradient operator. -/
theorem IsComplexEnvironmentSemigroup.forcedGradient_eq_weighted_eval
    {ζ : ℂ} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (ht : 0 < t) :
    hP.forcedGradient t ht =
      (((Real.sqrt (t : ℝ))⁻¹ : ℝ) •
        BoundedContinuousFunction.evalCLM ℂ (β := PiLp 2
          (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
          (⟨(t : ℝ), ht, le_rfl⟩ : Ioc (0 : ℝ) (t : ℝ))).comp
        (hP.weightedGradientOrbit (t : ℝ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change hP.forcedGradient t ht f =
    (Real.sqrt (t : ℝ))⁻¹ • hP.weightedGradientOrbit (t : ℝ) f ⟨t, ht, le_rfl⟩
  rw [hP.weightedGradientOrbit_apply]
  change hP.forcedGradient t ht f =
    (Real.sqrt (t : ℝ))⁻¹ • (Real.sqrt (t : ℝ) • hP.gradientOrbit f (t : ℝ))
  have hsqrt : Real.sqrt (t : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < t from ht))
  rw [smul_smul, inv_mul_cancel₀ hsqrt, one_smul]
  apply hP.forcedGradient_eq
  simpa only [Real.toNNReal_coe] using hP.gradientOrbit_spec f (show 0 < (t : ℝ) from ht)

/-- The actual gradient is operator-norm analytic throughout the short-time force disc. -/
theorem analyticAt_forcedGradient_of_small_force
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (t : ℝ≥0) (ht : 0 < t) (z₀ : ℂ)
    (hs : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (t : ℝ)) < 1) :
    AnalyticAt ℂ (fun z => (hF z).forcedGradient t ht) z₀ := by
  let L := (((Real.sqrt (t : ℝ))⁻¹ : ℝ) •
    BoundedContinuousFunction.evalCLM ℂ (β := PiLp 2
      (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)))
      (⟨(t : ℝ), ht, le_rfl⟩ : Ioc (0 : ℝ) (t : ℝ)))
  have ha := (((ContinuousLinearMap.compL ℂ _ _ _) L).analyticAt _).comp
    (analyticAt_weightedGradientOrbit_of_small_force hF (t : ℝ) z₀ hs)
  apply ha.congr
  apply Eventually.of_forall
  intro z
  exact ((hF z).forcedGradient_eq_weighted_eval t ht).symm

/-- Every actual positive-time gradient is entire in complex force in operator norm. -/
theorem analyticAt_forcedGradient
    {F : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hF : ∀ z : ℂ, IsComplexEnvironmentSemigroup Q i z (F z))
    (t : ℝ≥0) (ht : 0 < t) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z => (hF z).forcedGradient t ht) z₀ := by
  obtain ⟨n, hn, hs⟩ := exists_pos_nat_mul_sqrt_div_lt_one
    (‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)))) (t : ℝ)
  let s : ℝ≥0 := t / n
  have hsp : 0 < s := div_pos ht (Nat.cast_pos.mpr hn)
  have hst : s ≤ t := div_le_self t.property (by exact_mod_cast hn)
  have hsmall : ‖z₀‖ * (4 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * Real.sqrt (s : ℝ)) < 1 := by
    simpa only [s, NNReal.coe_div, NNReal.coe_natCast, mul_assoc] using hs
  have ha := ((ContinuousLinearMap.compL ℂ _ _ _).analyticAt_bilinear _).comp₂
    (analyticAt_forcedGradient_of_small_force hF s hsp z₀ hsmall)
    (analyticAt_complexEnvironmentSemigroup hF (t-s) z₀)
  apply ha.congr
  apply Eventually.of_forall
  intro z
  have he := (hF z).forcedGradient_add s hsp (t-s)
  simpa only [add_tsub_cancel_of_le hst] using! he.symm

/-- The internally constructed evolution has an entire actual positive-time gradient. -/
theorem analyticAt_forcedComplexEvolution_gradient (t : ℝ≥0) (ht : 0 < t) (z₀ : ℂ) :
    AnalyticAt ℂ (fun z =>
      (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z).forcedGradient t ht) z₀ :=
  analyticAt_forcedGradient
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z) t ht z₀

end EinsteinFull
