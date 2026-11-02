import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite-moment contraction for conditional localization.

The Markov-kernel argument proves a scalar ingredient of the conditional Jensen
step in `corrector.conditional`, paper/main.tex:876–881, and the nested
conditioning comparisons in `corrector.local`, paper/main.tex:938–950.
It does not assume independence of environment restrictions. Fiberwise averaging
follows the standard product-measure proof pattern.
Only Mathlib is imported; the other repository is not a dependency.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace EinsteinRelation.Correctors

/-- Scalar probability averaging is bounded by the finite-p seminorm. -/
theorem enorm_integral_le_eLpNorm {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : A → ℝ} (hf : AEStronglyMeasurable f μ) :
    ‖∫ a, f a ∂μ‖ₑ ≤ eLpNorm f p μ := by
  calc
    ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm hf).symm
    _ ≤ eLpNorm f p μ := eLpNorm_le_eLpNorm_of_exponent_le hp

/-- A Markov-kernel average contracts finite-p seminorms, without independence. -/
theorem eLpNorm_kernel_integral_le {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] {μ : Measure A} [SFinite μ] (κ : Kernel A B)
    [IsMarkovKernel κ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : A × B → ℝ} (hf : StronglyMeasurable f) :
    eLpNorm (fun a => ∫ b, f (a,b) ∂κ a) p μ ≤ eLpNorm f p (μ ⊗ₘ κ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top
      hf.integral_kernel_prod_right'.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hf.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (le_of_lt (one_div_pos.mpr hpr))
  rw [Measure.lintegral_compProd (hf.enorm.pow_const p.toReal)]
  apply lintegral_mono
  intro a
  calc
    ‖∫ b, f (a,b) ∂κ a‖ₑ ^ p.toReal ≤
        (eLpNorm (fun b => f (a,b)) p (κ a)) ^ p.toReal :=
      ENNReal.rpow_le_rpow (enorm_integral_le_eLpNorm hp
        (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable) hpr.le
    _ = ∫⁻ b, ‖f (a,b)‖ₑ ^ p.toReal ∂κ a := by
      have hfa : AEStronglyMeasurable (fun b => f (a, b)) (κ a) :=
        (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp_top hfa,
        ← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one]

/-- Conditional averaging onto the sigma algebra of an actual measurable
restriction variable contracts finite-p scalar norms. -/
theorem eLpNorm_condExp_comap_le {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] {μ : Measure A} [IsProbabilityMeasure μ]
    (X : A → B) (hX : Measurable X) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : A → ℝ} (hf : Integrable f μ) :
    eLpNorm (μ[f | (inferInstance : MeasurableSpace B).comap X]) p μ ≤
      eLpNorm f p μ := by
  set κ : Kernel B ℝ := condDistrib f X μ with hκ
  letI : IsMarkovKernel κ := inferInstanceAs (IsMarkovKernel (condDistrib f X μ))
  have hce : μ[f | (inferInstance : MeasurableSpace B).comap X] =ᵐ[μ]
      fun a => ∫ y, y ∂κ (X a) := condExp_ae_eq_integral_condDistrib' hX hf
  have hmean : StronglyMeasurable (fun b => ∫ y : ℝ, y ∂κ b) :=
    stronglyMeasurable_id.integral_kernel
  have hid : StronglyMeasurable (fun z : B × ℝ => z.2) :=
    measurable_snd.stronglyMeasurable
  rw [eLpNorm_congr_ae hce]
  have hmap_mean : eLpNorm (fun a => ∫ y : ℝ, y ∂κ (X a)) p μ =
      eLpNorm (fun b => ∫ y : ℝ, y ∂κ b) p (μ.map X) := by
    exact (eLpNorm_map_measure (μ := μ) (f := X)
      (g := fun b => ∫ y : ℝ, y ∂κ b) (p := p)
      hmean.aestronglyMeasurable hX.aemeasurable).symm
  have hbound : eLpNorm (fun b => ∫ y : ℝ, y ∂κ b) p (μ.map X) ≤
      eLpNorm (fun z : B × ℝ => z.2) p ((μ.map X) ⊗ₘ κ) :=
    eLpNorm_kernel_integral_le (μ := μ.map X) (p := p)
      (f := fun z : B × ℝ => z.2) κ hp hp_top hid
  have hmap_rhs : eLpNorm (fun z : B × ℝ => z.2) p ((μ.map X) ⊗ₘ κ) =
      eLpNorm f p μ := by
    rw [hκ, compProd_map_condDistrib hX.aemeasurable hf.aestronglyMeasurable.aemeasurable]
    rw [eLpNorm_map_measure hid.aestronglyMeasurable
      (hX.aemeasurable.prodMk hf.aestronglyMeasurable.aemeasurable)]
    rfl
  exact hmap_mean.le.trans (hbound.trans_eq hmap_rhs)

end EinsteinRelation.Correctors
