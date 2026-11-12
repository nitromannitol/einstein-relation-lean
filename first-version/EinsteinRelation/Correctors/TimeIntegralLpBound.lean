import EinsteinRelation.Correctors.KernelLpContraction
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Integrating moment bounds in time

Source: `paper/main.tex:1030–1041`. A positive integrable bound on the
`L^p` norm of each time section bounds the `L^p` norm of the time integral.
The proof normalizes the bound to a probability density and applies Jensen.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]

/-- A finite integrable moment bound also proves genuine joint
integrability, and hence almost sure time integrability
(`paper/main.tex:1030–1041`). -/
theorem integrable_prod_of_eLpNorm_bound {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ν : Measure T) [SFinite ν] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : Ω × T → ℝ} (hg : Measurable g) {B : T → ℝ}
    (hBi : Integrable B ν) (hB : ∀ t, 0 ≤ B t)
    (hbound : ∀ t, eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (B t)) :
    Integrable g (μ.prod ν) := by
  have hgi (t : T) : Integrable (fun ω => g (ω, t)) μ := by
    have hm : MemLp (fun ω => g (ω, t)) p μ :=
      ⟨(hg.comp measurable_prodMk_right).aestronglyMeasurable,
        (hbound t).trans_lt ENNReal.ofReal_lt_top⟩
    exact hm.integrable hp
  have hnorm (t : T) : (∫ ω, ‖g (ω, t)‖ ∂μ) ≤ B t := by
    apply (ENNReal.ofReal_le_ofReal_iff (hB t)).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm (hgi t),
      ← eLpNorm_one_eq_lintegral_enorm]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hp
      (hg.comp measurable_prodMk_right).aestronglyMeasurable).trans (hbound t)
  rw [integrable_prod_iff' hg.aestronglyMeasurable]
  refine ⟨ae_of_all _ hgi, hBi.mono' ?_ (ae_of_all _ fun t => ?_)⟩
  · exact hg.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hnorm t

/-- A probability average of scalar fields in the unit `L^p` ball stays in
that ball (`paper/main.tex:1030–1041`). -/
theorem eLpNorm_integral_probability_le_one {μ : Measure Ω} [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν] {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {g : Ω × T → ℝ} (hg : Measurable g)
    (hbound : ∀ t, eLpNorm (fun ω => g (ω, t)) p μ ≤ 1) :
    eLpNorm (fun ω => ∫ t, g (ω, t) ∂ν) p μ ≤ 1 := by
  have hJ := eLpNorm_kernel_integral_le (μ := μ) (Kernel.const Ω ν) hp hpt
    hg.stronglyMeasurable
  simp only [Kernel.const_apply, Measure.compProd_const] at hJ
  refine hJ.trans ?_
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpower (t : T) : (∫⁻ ω, ‖g (ω, t)‖ₑ ^ p.toReal ∂μ) ≤ 1 := by
    have h := ENNReal.rpow_le_rpow (hbound t) hpr.le
    rw [eLpNorm_eq_eLpNorm' hp0 hpt,
      ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hpr, ENNReal.one_rpow] at h
    exact h
  rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hpt,
    lintegral_prod_symm _ (hg.enorm.pow_const p.toReal).aemeasurable]
  calc
    _ ≤ (∫⁻ _ : T, (1 : ℝ≥0∞) ∂ν) ^ (1 / p.toReal) :=
      ENNReal.rpow_le_rpow (lintegral_mono hpower) (one_div_nonneg.mpr hpr.le)
    _ = 1 := by simp

/-- The norm of a time integral is bounded by the integral of a positive
sectionwise norm bound (`paper/main.tex:1030–1041`). -/
theorem eLpNorm_integral_le_integral_bound {μ : Measure Ω} [SFinite μ]
    (ν : Measure T) [SFinite ν] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : Ω × T → ℝ} (hg : Measurable g)
    {B : T → ℝ} (hB : Measurable B) (hBi : Integrable B ν)
    (hBpos : ∀ t, 0 < B t) (hmass : 0 < ∫ t, B t ∂ν)
    (hbound : ∀ t, eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (B t)) :
    eLpNorm (fun ω => ∫ t, g (ω, t) ∂ν) p μ ≤ ENNReal.ofReal (∫ t, B t ∂ν) := by
  let A : ℝ := ∫ t, B t ∂ν
  have hA : 0 < A := hmass
  let w : T → ℝ≥0∞ := fun t => ENNReal.ofReal (B t / A)
  have hw : Measurable w := (hB.div_const A).ennreal_ofReal
  let νB : Measure T := ν.withDensity w
  have hνB : IsProbabilityMeasure νB := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hBi.div_const A)
        (ae_of_all _ fun t => div_nonneg (hBpos t).le hA.le), integral_div]
    change ENNReal.ofReal (A / A) = 1
    rw [div_self hA.ne', ENNReal.ofReal_one]
  letI := hνB
  let G : Ω × T → ℝ := fun q => g q / B q.2
  have hG : Measurable G := hg.div (hB.comp measurable_snd)
  have hGbound (t : T) : eLpNorm (fun ω => G (ω, t)) p μ ≤ 1 := by
    have heq : (fun ω => G (ω, t)) = (B t)⁻¹ • (fun ω => g (ω, t)) := by
      funext ω
      simp only [G, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr (hBpos t).le),
      ENNReal.ofReal_inv_of_pos (hBpos t)]
    calc
      _ ≤ (ENNReal.ofReal (B t))⁻¹ * ENNReal.ofReal (B t) :=
        mul_le_mul_right (hbound t) _
      _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (hBpos t))
        ENNReal.ofReal_ne_top
  have hrep : (fun ω => ∫ t, g (ω, t) ∂ν) =
      A • (fun ω => ∫ t, G (ω, t) ∂νB) := by
    funext ω
    change (∫ t, g (ω, t) ∂ν) = A * ∫ t, G (ω, t) ∂νB
    rw [integral_withDensity_eq_integral_toReal_smul hw
      (ae_of_all _ fun t => ENNReal.ofReal_lt_top), ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only [w, G]
    rw [ENNReal.toReal_ofReal (div_nonneg (hBpos t).le hA.le), smul_eq_mul]
    field_simp [hA.ne', (hBpos t).ne']
  rw [hrep, eLpNorm_const_smul, Real.enorm_eq_ofReal hA.le]
  simpa only [mul_one] using
    mul_le_mul_right (eLpNorm_integral_probability_le_one νB hp hpt hG hGbound)
      (ENNReal.ofReal A)

/-- The time-integral estimate restricted to a measurable interval or set
(`paper/main.tex:1030–1041`). The bound is needed only on that set. -/
theorem eLpNorm_setIntegral_le_integral_bound {μ : Measure Ω} [SFinite μ]
    (ν : Measure T) [SFinite ν] {s : Set T} (hs : MeasurableSet s)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {g : Ω × T → ℝ} (hg : Measurable g)
    {B : T → ℝ} (hB : Measurable B) (hBi : IntegrableOn B s ν)
    (hBpos : ∀ t, 0 < B t) (hmass : 0 < ∫ t in s, B t ∂ν)
    (hbound : ∀ t ∈ s, eLpNorm (fun ω => g (ω, t)) p μ ≤ ENNReal.ofReal (B t)) :
    eLpNorm (fun ω => ∫ t in s, g (ω, t) ∂ν) p μ ≤ ENNReal.ofReal (∫ t in s, B t ∂ν) := by
  classical
  let G : Ω × T → ℝ := fun q => if q.2 ∈ s then g q else 0
  have hG : Measurable G := Measurable.ite (hs.preimage measurable_snd) hg measurable_const
  have hGb (t : T) : eLpNorm (fun ω => G (ω, t)) p μ ≤ ENNReal.ofReal (B t) := by
    by_cases ht : t ∈ s
    · simpa only [G, if_pos ht] using hbound t ht
    · simp only [G, if_neg ht]
      change eLpNorm (0 : Ω → ℝ) p μ ≤ _
      rw [eLpNorm_zero]
      exact zero_le _
  have heq : (fun ω => ∫ t in s, g (ω, t) ∂ν) = fun ω => ∫ t in s, G (ω, t) ∂ν := by
    funext ω
    exact integral_congr_ae ((ae_restrict_mem hs).mono fun t ht => by simp only [G, if_pos ht])
  rw [heq]
  exact eLpNorm_integral_le_integral_bound (ν.restrict s) hp hpt hG hB hBi hBpos hmass hGb

end EinsteinRelation.Correctors
