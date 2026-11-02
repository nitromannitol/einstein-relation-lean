import EinsteinFull.Calculus.S2AnnealedDominationSupport
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# `L²` operator domination of an annealed law

A finite measure `μ` whose integrals of nonnegative bounded continuous tests `f` are the `ν`-integrals
of `T f`, for a bounded operator `T` on complex `L²(ν)`, is absolutely continuous with respect to `ν`,
with `μ A ≤ ‖T‖ ν(univ)^{1/2} ν(A)^{1/2}`. This is the abstract form of the time-`t` annealed
domination `μ_t(A) ≤ ‖P_t‖_{2→2} · ν(A)^{1/2}` (the identification of `μ_t` on bounded continuous
tests is the hypothesis `hid`).
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

variable {Ω : Type*} [TopologicalSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

omit [TopologicalSpace.PseudoMetrizableSpace Ω] in
/-- One-test `L²` bound: if `∫ f dμ = ∫ T F dν` for a representative `F` of `f` in `L²(ν)`, then
`∫ f dμ ≤ ‖T‖ ν(univ)^{1/2} (∫ f² dν)^{1/2}`. -/
theorem lintegral_le_of_integral_eq_apply (μ ν : Measure Ω) [IsFiniteMeasure μ]
    (T : MeasureTheory.Lp ℂ 2 ν →L[ℂ] MeasureTheory.Lp ℂ 2 ν) (M : ℝ≥0)
    (hT : ‖T‖ ≤ M) (f : Ω →ᵇ ℝ≥0) (F : MeasureTheory.Lp ℂ 2 ν)
    (hF : F =ᵐ[ν] fun x => (((f x : ℝ≥0) : ℝ) : ℂ))
    (hid : ∫ x, (((f x : ℝ≥0) : ℝ) : ℂ) ∂μ = ∫ x, (T F) x ∂ν) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤
      ((M : ℝ≥0∞) * ν Set.univ ^ (1 / 2 : ℝ)) * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have hfc : Continuous fun x => ((f x : ℝ≥0) : ℝ) := NNReal.continuous_coe.comp f.continuous
  have henorm : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ‖r‖ₑ := fun r => by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  -- Step 1: `∫⁻ f dμ = ‖∫ f dμ‖ₑ`.
  have h1 : ∫⁻ x, (f x : ℝ≥0∞) ∂μ = ‖∫ x, (((f x : ℝ≥0) : ℝ) : ℂ) ∂μ‖ₑ := by
    rw [integral_complex_ofReal, henorm,
      Real.enorm_eq_ofReal (integral_nonneg fun x => NNReal.coe_nonneg _),
      ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f μ,
      ENNReal.ofReal_toReal (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (μ := μ) f).ne]
  -- Step 2: `‖∫ T F dν‖ₑ ≤ eLpNorm (T F) 1 ν ≤ eLpNorm (T F) 2 ν * ν(univ)^{1/2}`.
  have hTF : AEStronglyMeasurable (fun x => (T F) x) ν := (MeasureTheory.Lp.aestronglyMeasurable _)
  have h2 : ‖∫ x, (T F) x ∂ν‖ₑ ≤ ‖T F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm hTF, MeasureTheory.Lp.enorm_def]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hTF).trans
      (le_of_eq ?_)
    norm_num
  -- Step 3: `‖T F‖ₑ ≤ M * ‖F‖ₑ`.
  have h3 : ‖T F‖ₑ ≤ (M : ℝ≥0∞) * ‖F‖ₑ := by
    rw [← ofReal_norm (T F), ← ofReal_norm F]
    calc ENNReal.ofReal ‖T F‖ ≤ ENNReal.ofReal ((M : ℝ) * ‖F‖) :=
          ENNReal.ofReal_le_ofReal
            ((T.le_opNorm F).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _)))
      _ = (M : ℝ≥0∞) * ENNReal.ofReal ‖F‖ := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg M), ENNReal.ofReal_coe_nnreal]
  -- Step 4: `‖F‖ₑ = (∫⁻ f² dν)^{1/2}`.
  have hFm : AEStronglyMeasurable (fun x => (((f x : ℝ≥0) : ℝ) : ℂ)) ν :=
    (Complex.continuous_ofReal.comp hfc).aestronglyMeasurable
  have h4 : ‖F‖ₑ = (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    rw [MeasureTheory.Lp.enorm_def, eLpNorm_congr_ae hF,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hFm]
    have hen : ∀ x, ‖(((f x : ℝ≥0) : ℝ) : ℂ)‖ₑ ^ ((2 : ℝ≥0∞).toReal) = (f x : ℝ≥0∞) ^ 2 := by
      intro x
      rw [henorm, Real.enorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal,
        ENNReal.toReal_ofNat, ENNReal.rpow_two]
    simp_rw [hen]
    norm_num
  rw [h1, hid]
  calc ‖∫ x, (T F) x ∂ν‖ₑ ≤ ‖T F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := h2
    _ ≤ ((M : ℝ≥0∞) * ‖F‖ₑ) * ν Set.univ ^ (1 / 2 : ℝ) := mul_le_mul' h3 le_rfl
    _ = _ := by rw [h4]; ring

end EinsteinFull
