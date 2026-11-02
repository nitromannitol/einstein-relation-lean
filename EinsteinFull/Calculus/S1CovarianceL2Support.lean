import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Elementary mean-square calculus used by the covariance chain: the size
`sqrt (∫ ‖f‖²)` is the norm of the `L²` class, hence satisfies the triangle and
Cauchy–Schwarz inequalities for functions with `MemLp f 2`. No hypothesis other
than membership in `L²` is used. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- Mean-square size of a scalar function; it equals `covarianceComplexL2Size`
pointwise by unfolding. -/
noncomputable def l2Size {𝕜 : Type*} [RCLike 𝕜] (μ : Measure α) (f : α → 𝕜) : ℝ :=
  Real.sqrt (∫ ω, ‖f ω‖ ^ 2 ∂μ)

theorem l2Size_nonneg {𝕜 : Type*} [RCLike 𝕜] (f : α → 𝕜) : 0 ≤ l2Size μ f :=
  Real.sqrt_nonneg _

theorem l2Size_eq_norm_toLp {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (hf : MemLp f 2 μ) :
    l2Size μ f = ‖hf.toLp f‖ := by
  have hg := hf.coeFn_toLp
  have h2 : ∫ ω, ‖(hf.toLp f) ω‖ ^ 2 ∂μ = ∫ ω, ‖f ω‖ ^ 2 ∂μ :=
    integral_congr_ae (hg.mono fun ω hω => by dsimp only; rw [hω])
  have h3 : ((‖hf.toLp f‖ ^ 2 : ℝ) : 𝕜) = ((∫ ω, ‖(hf.toLp f) ω‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
    calc ((‖hf.toLp f‖ ^ 2 : ℝ) : 𝕜) = (‖hf.toLp f‖ : 𝕜) ^ 2 := by push_cast; rfl
      _ = inner 𝕜 (hf.toLp f) (hf.toLp f) := (inner_self_eq_norm_sq_to_K _).symm
      _ = ∫ a, inner 𝕜 ((hf.toLp f) a) ((hf.toLp f) a) ∂μ := L2.inner_def _ _
      _ = ∫ a, ((‖(hf.toLp f) a‖ ^ 2 : ℝ) : 𝕜) ∂μ := by
          congr 1
          funext a
          rw [inner_self_eq_norm_sq_to_K]
          push_cast
          rfl
      _ = ((∫ ω, ‖(hf.toLp f) ω‖ ^ 2 ∂μ : ℝ) : 𝕜) := integral_ofReal
  have h4 : ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
    rw [← h2]
    exact_mod_cast h3
  unfold l2Size
  rw [← h4, Real.sqrt_sq (norm_nonneg _)]

theorem l2Size_add_le {𝕜 : Type*} [RCLike 𝕜] {f g : α → 𝕜} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : l2Size μ (f + g) ≤ l2Size μ f + l2Size μ g := by
  rw [l2Size_eq_norm_toLp (hf.add hg), l2Size_eq_norm_toLp hf, l2Size_eq_norm_toLp hg,
    MemLp.toLp_add hf hg]
  exact norm_add_le _ _

theorem l2Size_sub_le {𝕜 : Type*} [RCLike 𝕜] {f g : α → 𝕜} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : l2Size μ (f - g) ≤ l2Size μ f + l2Size μ g := by
  rw [l2Size_eq_norm_toLp (hf.sub hg), l2Size_eq_norm_toLp hf, l2Size_eq_norm_toLp hg,
    MemLp.toLp_sub hf hg]
  exact norm_sub_le _ _

theorem l2Size_norm {𝕜 : Type*} [RCLike 𝕜] (f : α → 𝕜) :
    l2Size μ (fun ω => ‖f ω‖) = l2Size μ f := by
  unfold l2Size
  simp only [norm_norm]

/-- Cauchy–Schwarz for real functions in `L²`. -/
theorem integral_mul_le_l2Size_real {a b : α → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ ω, a ω * b ω ∂μ ≤ l2Size μ a * l2Size μ b := by
  have h1 : inner ℝ (ha.toLp a) (hb.toLp b) = ∫ ω, a ω * b ω ∂μ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with ω h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply, mul_comm]
  rw [← h1, l2Size_eq_norm_toLp ha, l2Size_eq_norm_toLp hb]
  exact real_inner_le_norm _ _

/-- Cauchy–Schwarz for the (bilinear, unconjugated) pairing of two scalar `L²` functions. -/
theorem norm_integral_mul_le_l2Size {𝕜 : Type*} [RCLike 𝕜] {f g : α → 𝕜}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ ω, f ω * g ω ∂μ‖ ≤ l2Size μ f * l2Size μ g := by
  calc ‖∫ ω, f ω * g ω ∂μ‖ ≤ ∫ ω, ‖f ω * g ω‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ ω, ‖f ω‖ * ‖g ω‖ ∂μ := by simp only [norm_mul]
    _ ≤ l2Size μ (fun ω => ‖f ω‖) * l2Size μ (fun ω => ‖g ω‖) :=
        integral_mul_le_l2Size_real hf.norm hg.norm
    _ = l2Size μ f * l2Size μ g := by rw [l2Size_norm, l2Size_norm]

/-- Difference of two bilinear pairings, by Cauchy–Schwarz. -/
theorem norm_integral_mul_sub_le {𝕜 : Type*} [RCLike 𝕜] {u v y w : α → 𝕜}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hy : MemLp y 2 μ) (hw : MemLp w 2 μ) :
    ‖(∫ ω, u ω * v ω ∂μ) - ∫ ω, y ω * w ω ∂μ‖ ≤
      l2Size μ (u - y) * l2Size μ v + l2Size μ y * l2Size μ (v - w) := by
  have i1 : Integrable (fun ω => (u - y) ω * v ω) μ := (hu.sub hy).integrable_mul hv
  have i2 : Integrable (fun ω => y ω * (v - w) ω) μ := hy.integrable_mul (hv.sub hw)
  have e : (∫ ω, u ω * v ω ∂μ) - ∫ ω, y ω * w ω ∂μ =
      (∫ ω, (u - y) ω * v ω ∂μ) + ∫ ω, y ω * (v - w) ω ∂μ := by
    rw [← integral_add i1 i2]
    have i3 : Integrable (fun ω => u ω * v ω) μ := hu.integrable_mul hv
    have i4 : Integrable (fun ω => y ω * w ω) μ := hy.integrable_mul hw
    rw [← integral_sub i3 i4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_integral_mul_le_l2Size (hu.sub hy) hv)
    (norm_integral_mul_le_l2Size hy (hv.sub hw)))

/-- The size of an `Lp` element is its norm. -/
theorem l2Size_lp {𝕜 : Type*} [RCLike 𝕜] (u : Lp 𝕜 2 μ) :
    l2Size μ (⇑u) = ‖u‖ := by
  have h := l2Size_eq_norm_toLp (Lp.memLp u)
  rw [Lp.toLp_coeFn u (Lp.memLp u)] at h
  exact h

end EinsteinFull.Calculus.S1
