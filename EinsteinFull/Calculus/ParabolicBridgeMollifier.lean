import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Time mollification of space-time functions

`tmoll ε` is a smooth probability density on `ℝ` supported in `[-ε, ε]`, and
`Mol ε F (y, t) = ∫ tmoll ε (t - s) F (y, s) ds`.  We prove the `L²` contraction
`‖Mol ε F‖₂ ≤ ‖F‖₂` by a pointwise Jensen inequality and Tonelli.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

/-- The bump with radii `ε/2`, `ε`. -/
def tbump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- The time mollifier. -/
def tmoll (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ := (tbump ε hε).normed volume

variable {ε : ℝ} {hε : 0 < ε}

theorem tmoll_nonneg (t : ℝ) : 0 ≤ tmoll ε hε t := (tbump ε hε).nonneg_normed t

theorem tmoll_integral : ∫ t, tmoll ε hε t = 1 := (tbump ε hε).integral_normed

theorem tmoll_integrable : Integrable (tmoll ε hε) volume := (tbump ε hε).integrable_normed

theorem tmoll_contDiff : ContDiff ℝ (⊤ : ℕ∞) (tmoll ε hε) := (tbump ε hε).contDiff_normed

theorem tmoll_continuous : Continuous (tmoll ε hε) := (tbump ε hε).continuous_normed

theorem tmoll_hasCompactSupport : HasCompactSupport (tmoll ε hε) :=
  (tbump ε hε).hasCompactSupport_normed

theorem tmoll_eq_zero {t : ℝ} (ht : ε ≤ |t|) : tmoll ε hε t = 0 := by
  by_contra h
  have hmem : t ∈ Function.support ((tbump ε hε).normed volume) := h
  rw [(tbump ε hε).support_normed_eq] at hmem
  have := mem_ball_zero_iff.mp hmem
  have h2 : (tbump ε hε).rOut = ε := rfl
  rw [Real.norm_eq_abs, h2] at this
  linarith

theorem tmoll_neg (t : ℝ) : tmoll ε hε (-t) = tmoll ε hε t := (tbump ε hε).normed_neg (μ := volume) t

/-- Time mollification of a function on `Vec d × ℝ`. -/
def Mol {d : ℕ} (ε : ℝ) (hε : 0 < ε) (F : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  ∫ t, tmoll ε hε (z.2 - t) * F (z.1, t)

/-- Jensen's inequality for a probability weight, in `ℝ≥0∞`. -/
theorem lintegral_sq_le_of_prob {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ G : α → ℝ≥0∞} (hρ : AEMeasurable ρ μ) (hG : AEMeasurable G μ)
    (h1 : ∫⁻ a, ρ a ∂μ = 1) :
    (∫⁻ a, ρ a * G a ∂μ) ^ (2 : ℝ) ≤ ∫⁻ a, ρ a * G a ^ (2 : ℝ) ∂μ := by
  have hhalf : ∀ a, ρ a ^ (1 / 2 : ℝ) * ρ a ^ (1 / 2 : ℝ) = ρ a := fun a => by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hf : AEMeasurable (fun a => ρ a ^ (1 / 2 : ℝ)) μ := hρ.pow_const _
  have hg : AEMeasurable (fun a => ρ a ^ (1 / 2 : ℝ) * G a) μ := hf.mul hG
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : (fun a => ρ a ^ (1 / 2 : ℝ) * (ρ a ^ (1 / 2 : ℝ) * G a)) = fun a => ρ a * G a := by
    funext a
    rw [← mul_assoc, hhalf]
  have e2 : (fun a => (ρ a ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) = ρ := by
    funext a
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : (fun a => (ρ a ^ (1 / 2 : ℝ) * G a) ^ (2 : ℝ)) = fun a => ρ a * G a ^ (2 : ℝ) := by
    funext a
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3, h1] at h
  have h2 : (∫⁻ a, ρ a * G a ∂μ) ^ (2 : ℝ) ≤
      ((1 : ℝ≥0∞) ^ (1 / (2 : ℝ)) * (∫⁻ a, ρ a * G a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.one_rpow, one_mul, ← ENNReal.rpow_mul]
  norm_num

/-- Pointwise `L²` bound for the mollification. -/
theorem enorm_Mol_sq_le {d : ℕ} (F : Vec d × ℝ → ℝ) (hF : Measurable F) (z : Vec d × ℝ) :
    ‖Mol ε hε F z‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ t, ENNReal.ofReal (tmoll ε hε (z.2 - t)) * ‖F (z.1, t)‖ₑ ^ (2 : ℝ) := by
  have hρm : Measurable fun t => ENNReal.ofReal (tmoll ε hε (z.2 - t)) :=
    ENNReal.measurable_ofReal.comp (tmoll_continuous.measurable.comp (measurable_const.sub measurable_id))
  have hGm : Measurable fun t => ‖F (z.1, t)‖ₑ :=
    (hF.comp (measurable_const.prodMk measurable_id)).enorm
  have h1 : ∫⁻ t, ENNReal.ofReal (tmoll ε hε (z.2 - t)) = 1 := by
    have hint : Integrable (tmoll ε hε) volume := tmoll_integrable
    have e : ∫⁻ t, ENNReal.ofReal (tmoll ε hε (z.2 - t)) = ∫⁻ t, ENNReal.ofReal (tmoll ε hε t) :=
      lintegral_sub_left_eq_self (fun t => ENNReal.ofReal (tmoll ε hε t)) z.2
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall tmoll_nonneg),
      tmoll_integral, ENNReal.ofReal_one]
  have hJ := lintegral_sq_le_of_prob hρm.aemeasurable hGm.aemeasurable h1
  refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) hJ
  have : ‖Mol ε hε F z‖ₑ ≤ ∫⁻ t, ‖tmoll ε hε (z.2 - t) * F (z.1, t)‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  refine this.trans (le_of_eq (lintegral_congr fun t => ?_))
  rw [enorm_mul, Real.enorm_eq_ofReal (tmoll_nonneg _)]

/-- The `L²` contraction of the time mollification. -/
theorem lintegral_enorm_Mol_sq_le {d : ℕ} (F : Vec d × ℝ → ℝ) (hF : Measurable F) :
    ∫⁻ z, ‖Mol ε hε F z‖ₑ ^ (2 : ℝ) ≤ ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) := by
  refine (lintegral_mono fun z => enorm_Mol_sq_le F hF z).trans ?_
  have hmeas : Measurable fun p : (Vec d × ℝ) × ℝ =>
      ENNReal.ofReal (tmoll ε hε (p.1.2 - p.2)) * ‖F (p.1.1, p.2)‖ₑ ^ (2 : ℝ) := by
    refine (ENNReal.measurable_ofReal.comp (tmoll_continuous.measurable.comp
      (measurable_snd.comp measurable_fst |>.sub measurable_snd))).mul ?_
    exact ((hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).enorm).pow_const _
  have h1 : ∫⁻ z : Vec d × ℝ, ∫⁻ t, ENNReal.ofReal (tmoll ε hε (z.2 - t)) *
      ‖F (z.1, t)‖ₑ ^ (2 : ℝ) = ∫⁻ y : Vec d, ∫⁻ s : ℝ, ∫⁻ t : ℝ,
        ENNReal.ofReal (tmoll ε hε (s - t)) * ‖F (y, t)‖ₑ ^ (2 : ℝ) := by
    rw [Measure.volume_eq_prod, lintegral_prod]
    exact (hmeas.lintegral_prod_right').aemeasurable
  have h2 : ∀ y : Vec d, ∫⁻ s : ℝ, ∫⁻ t : ℝ,
      ENNReal.ofReal (tmoll ε hε (s - t)) * ‖F (y, t)‖ₑ ^ (2 : ℝ) =
        ∫⁻ t : ℝ, ‖F (y, t)‖ₑ ^ (2 : ℝ) := by
    intro y
    have hm2 : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (tmoll ε hε (p.1 - p.2)) * ‖F (y, p.2)‖ₑ ^ (2 : ℝ) := by
      refine (ENNReal.measurable_ofReal.comp (tmoll_continuous.measurable.comp
        (measurable_fst.sub measurable_snd))).mul ?_
      exact ((hF.comp (measurable_const.prodMk measurable_snd)).enorm).pow_const _
    rw [lintegral_lintegral_swap hm2.aemeasurable]
    refine lintegral_congr fun t => ?_
    rw [lintegral_mul_const' _ _ (by simp)]
    have e : ∫⁻ s : ℝ, ENNReal.ofReal (tmoll ε hε (s - t)) =
        ∫⁻ s : ℝ, ENNReal.ofReal (tmoll ε hε s) :=
      lintegral_sub_right_eq_self (fun s => ENNReal.ofReal (tmoll ε hε s)) t
    rw [e, ← ofReal_integral_eq_lintegral_ofReal tmoll_integrable
      (Filter.Eventually.of_forall tmoll_nonneg), tmoll_integral, ENNReal.ofReal_one, one_mul]
  rw [h1]
  simp only [h2]
  rw [Measure.volume_eq_prod, lintegral_prod]
  exact (hF.enorm.pow_const _).aemeasurable

end EinsteinFull.ParabolicBridge
