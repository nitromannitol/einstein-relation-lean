import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Removing a compact cutoff from the kernel pairing

Source: AKM (9.2), p. 347, (E.4), (E.8), pp. 500–501;
`paper/main.tex:777–782,840`. Absolute integrability controls the gradient
pairing tail, and the integrable kernel controls the cutoff derivative.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- The coordinate norm bounds a contraction, with the explicit dimension factor. -/
theorem akm_abs_dot_le_dimension_mul_norm {d : ℕ} (v w : Vec d) :
    |dot v w| ≤ (d : ℝ) * ‖v‖ * ‖w‖ := by
  calc
    |dot v w| ≤ ∑ j, |v j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- An integrable kernel and its absolutely integrable gradient pairing allow
compact smooth cutoffs to be removed. No pointwise gradient bound is needed. -/
theorem akm_kernel_pairing_of_compact_cutoffs {d : ℕ}
    {g Dp : Vec d → Vec d} {a p : Vec d → ℝ} {χ : ℕ → Vec d → ℝ}
    (hp : Integrable p volume) (hq : Integrable (fun x => dot (g x) (Dp x)) volume)
    (hg : AEStronglyMeasurable g volume) (ha : AEStronglyMeasurable a volume)
    {B C L : ℝ} (hL : 0 ≤ L)
    (hgb : ∀ᵐ x ∂volume, ‖g x‖ ≤ B) (hab : ∀ᵐ x ∂volume, |a x| ≤ C)
    (hχ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n))
    (hχb : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hDχ : ∀ n x, ‖gradient (χ n) x‖ ≤ L / (n+1 : ℕ))
    (hibp : ∀ n,
      (∫ x, χ n x * dot (g x) (Dp x) + p x * dot (g x) (gradient (χ n) x) ∂volume) =
        -(∫ x, χ n x * p x * a x ∂volume)) :
    -(∫ x, dot (g x) (Dp x) ∂volume) = ∫ x, p x * a x ∂volume := by
  have hχm n := (hχ n).continuous.aestronglyMeasurable (μ := volume)
  have hχnorm n : ∀ᵐ x ∂volume, ‖χ n x‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hχb n x).1] using (hχb n x).2
  have hRle n : L / (n+1 : ℕ) ≤ L := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
    have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using mul_le_mul_of_nonneg_left hn hL
  have hR : Tendsto (fun n : ℕ => L / (n+1 : ℕ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_zero, one_div, one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul L
  have hgradm n : AEStronglyMeasurable (gradient (χ n)) volume := by
    apply Continuous.aestronglyMeasurable
    apply continuous_pi
    intro j
    exact ((hχ n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdotm n : AEStronglyMeasurable (fun x => dot (g x) (gradient (χ n) x)) volume := by
    simpa only [dot, Finset.sum_apply, Pi.mul_apply] using
      Finset.aestronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      ((continuous_apply j).comp_aestronglyMeasurable hg).mul
        ((continuous_apply j).comp_aestronglyMeasurable (hgradm n)))
  have hdotb n : ∀ᵐ x ∂volume,
      |dot (g x) (gradient (χ n) x)| ≤ ((d : ℝ) * |B|) * (L / (n+1 : ℕ)) := by
    filter_upwards [hgb] with x hx
    calc
      _ ≤ (d : ℝ) * ‖g x‖ * ‖gradient (χ n) x‖ :=
        akm_abs_dot_le_dimension_mul_norm _ _
      _ ≤ _ := by gcongr; exact hx.trans (le_abs_self B); exact hDχ n x
  have hdotfixed n : ∀ᵐ x ∂volume,
      ‖dot (g x) (gradient (χ n) x)‖ ≤ ((d : ℝ) * |B|) * L := by
    filter_upwards [hdotb n] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left (hRle n) (by positivity))
  have hei n : Integrable (fun x => p x * dot (g x) (gradient (χ n) x)) volume :=
    hp.mul_bdd (hdotm n) (hdotfixed n)
  have he : Tendsto (fun n => ∫ x, p x * dot (g x) (gradient (χ n) x) ∂volume)
      atTop (𝓝 0) := by
    have hb : ∀ n, ∀ᵐ x ∂volume,
        ‖p x * dot (g x) (gradient (χ n) x)‖ ≤ ‖p x‖ * (((d : ℝ) * |B|) * L) := by
      intro n
      filter_upwards [hdotfixed n] with x hx
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hx (norm_nonneg (p x))
    have hl : ∀ᵐ x ∂volume, Tendsto (fun n => p x * dot (g x) (gradient (χ n) x))
        atTop (𝓝 0) := by
      filter_upwards [ae_all_iff.mpr hdotb] with x hx
      apply (tendsto_zero_iff_norm_tendsto_zero).mpr
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
        (Eventually.of_forall (fun n => by
          simpa only [norm_mul, Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left (hx n) (abs_nonneg (p x))))
      simpa using (hR.const_mul ((d : ℝ) * |B|)).const_mul |p x|
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence
        (fun x => ‖p x‖ * (((d : ℝ) * |B|) * L))
        (fun n => (hei n).aestronglyMeasurable) (hp.norm.mul_const _) hb hl
  have hqi n : Integrable (fun x => χ n x * dot (g x) (Dp x)) volume :=
    hq.bdd_mul (hχm n) (hχnorm n)
  have hqconv : Tendsto (fun n => ∫ x, χ n x * dot (g x) (Dp x) ∂volume)
      atTop (𝓝 (∫ x, dot (g x) (Dp x) ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖dot (g x) (Dp x)‖) (fun n => (hqi n).aestronglyMeasurable) hq.norm
    · intro n
      filter_upwards [hχnorm n] with x hx
      simpa only [Pi.mul_apply, norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · filter_upwards with x
      simpa using (hχlim x).mul_const (dot (g x) (Dp x))
  have hai : Integrable (fun x => p x * a x) volume :=
    hp.mul_bdd ha (by simpa only [Real.norm_eq_abs] using hab)
  have haconv : Tendsto (fun n => ∫ x, χ n x * p x * a x ∂volume)
      atTop (𝓝 (∫ x, p x * a x ∂volume)) := by
    simp_rw [mul_assoc]
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖p x * a x‖) (fun n => ((hχm n).mul hai.aestronglyMeasurable)) hai.norm
    · intro n
      filter_upwards [hχnorm n] with x hx
      simpa only [Pi.mul_apply, norm_mul, one_mul] using
        mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (p x)) (norm_nonneg (a x)))
    · filter_upwards with x
      simpa using (hχlim x).mul_const (p x * a x)
  have heq : (fun n => (∫ x, χ n x * dot (g x) (Dp x) ∂volume) +
      ∫ x, p x * dot (g x) (gradient (χ n) x) ∂volume) =
      fun n => -(∫ x, χ n x * p x * a x ∂volume) := by
    funext n
    rw [← integral_add (hqi n) (hei n)]
    exact hibp n
  have hlimit : (∫ x, dot (g x) (Dp x) ∂volume) + 0 =
      -(∫ x, p x * a x ∂volume) :=
    tendsto_nhds_unique (hqconv.add he) (heq ▸ haconv.neg)
  linarith

end EinsteinRelation.Correctors
