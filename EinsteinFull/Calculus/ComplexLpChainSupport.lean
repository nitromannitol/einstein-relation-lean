import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong L2 chain rules for complex nonlinear profiles

Real C1 Lipschitz maps on the complex plane act on actual complex L2 classes.
Dominated convergence differentiates composition along affine L2 paths. This
is a directional derivative assertion; it does not assert Frechet
differentiability of the nonlinear composition map on L2.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section

namespace EinsteinFull

/-- A bounded continuous field of real linear maps sends an L2 vector to L2. -/
theorem memLp_complexDifferential {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D) {K : ℝ}
    (hK : ∀ z, ‖D z‖ ≤ K) (f g : Lp ℂ 2 μ) :
    MemLp (fun a => D (f a) (g a)) 2 μ := by
  refine (Lp.memLp g).of_le_mul (c := K)
    ((ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ)).aestronglyMeasurable_comp₂
      (hD.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable g)) (Eventually.of_forall fun a => ?_)
  exact (D (f a)).le_of_opNorm_le (hK _) _

/-- The literal pointwise differential has the same L2 bound as its coefficient field. -/
theorem norm_complexDifferential_toLp_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D) {K : ℝ}
    (hK : ∀ z, ‖D z‖ ≤ K) (f g : Lp ℂ 2 μ) :
    ‖(memLp_complexDifferential μ hD hK f g).toLp (fun a => D (f a) (g a))‖ ≤
      K * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(memLp_complexDifferential μ hD hK f g).coeFn_toLp] with a ha
  rw [ha]
  exact (D (f a)).le_of_opNorm_le (hK _) _

private theorem norm_sq_complexLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- An integrably dominated pointwise limit converges in the actual complex L2 norm. -/
theorem tendsto_complexLp_of_dominated {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    {u : ι → Lp ℂ 2 μ} {v : Lp ℂ 2 μ} {F : ι → α → ℂ} {f : α → ℂ}
    (hF : ∀ n, u n =ᵐ[μ] F n) (hf : v =ᵐ[μ] f)
    {b : α → ℝ} (hb : Integrable (fun a => b a ^ 2) μ)
    (hbound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ‖F n a - f a‖ ≤ b a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto u l (𝓝 v) := by
  have hmeas (n : ι) : AEStronglyMeasurable (fun a => ‖F n a - f a‖ ^ 2) μ :=
    (((Lp.aestronglyMeasurable (u n)).congr (hF n)).sub
      ((Lp.aestronglyMeasurable v).congr hf)).norm.pow 2
  have hsq := tendsto_integral_filter_of_dominated_convergence
    (l := l) (f := fun _ => (0 : ℝ)) (fun a => b a ^ 2)
    (Eventually.of_forall hmeas) ?_ hb ?_
  · have heq (n : ι) : ‖u n - v‖ ^ 2 = ∫ a, ‖F n a - f a‖ ^ 2 ∂μ := by
      rw [norm_sq_complexLp]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (u n) v, hF n, hf] with a ha hu hv
      rw [ha, Pi.sub_apply, hu, hv]
    simp only [integral_zero] at hsq
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    change Tendsto (fun n => Real.sqrt (∫ a, ‖F n a - f a‖ ^ 2 ∂μ)) l
      (𝓝 (Real.sqrt 0)) at hn
    simp only [← heq, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
  · filter_upwards [hbound] with n hn
    filter_upwards [hn] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ha 2
  · filter_upwards [hlim] with a ha
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (ha.sub (tendsto_const_nhds (x := f a))).norm.pow 2

/-- Lipschitz composition has the pointwise real differential along every affine L2 path. -/
theorem hasDerivAt_complexLp_affine {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℂ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z) (f g : Lp ℂ 2 μ) :
    HasDerivAt (fun t : ℝ => hF.compLp h0 (f + t • g))
      ((memLp_complexDifferential μ hD (fun z => (hFD z).le_of_lipschitz hF) f g).toLp
        (fun a => D (f a) (g a))) 0 := by
  let q (t : ℝ) (a : α) := t⁻¹ • (F (f a + t • g a) - F (f a))
  have hq (t : ℝ) (a : α) : ‖q t a‖ ≤ (K : ℝ) * ‖g a‖ := by
    by_cases ht : t = 0
    · simp only [q, ht, inv_zero, zero_smul, norm_zero]
      exact mul_nonneg K.coe_nonneg (norm_nonneg _)
    · calc
        ‖q t a‖ = |t|⁻¹ * ‖F (f a + t • g a) - F (f a)‖ := by
          dsimp only [q]
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
        _ ≤ |t|⁻¹ * ((K : ℝ) * (|t| * ‖g a‖)) := by
          gcongr
          simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using
            hF.norm_sub_le (f a + t • g a) (f a)
        _ = (K : ℝ) * ‖g a‖ := by
          calc
            _ = (K : ℝ) * (|t|⁻¹ * |t|) * ‖g a‖ := by ring
            _ = _ := by rw [inv_mul_cancel₀ (abs_ne_zero.mpr ht), mul_one]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, zero_smul, add_zero]
  refine tendsto_complexLp_of_dominated
    (F := q) (f := fun a => D (f a) (g a)) ?_ (MemLp.coeFn_toLp _)
    (b := fun a => (2 * (K : ℝ)) * ‖g a‖) ?_ ?_ ?_
  · intro t
    filter_upwards [Lp.coeFn_smul t⁻¹
        (hF.compLp h0 (f + t • g) - hF.compLp h0 f),
      Lp.coeFn_sub (hF.compLp h0 (f + t • g)) (hF.compLp h0 f),
      hF.coeFn_compLp h0 (f + t • g), hF.coeFn_compLp h0 f,
      Lp.coeFn_add f (t • g), Lp.coeFn_smul t g] with a ha hb hc hd he hh
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Function.comp_apply] at *
    rw [ha, hb, hc, hd, he, hh]
  · convert ((Lp.memLp g).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
      ((2 * (K : ℝ)) ^ 2) using 1
    ext a
    ring
  · exact Eventually.of_forall fun t => Eventually.of_forall fun a => calc
      ‖q t a - D (f a) (g a)‖ ≤ ‖q t a‖ + ‖D (f a) (g a)‖ := norm_sub_le _ _
      _ ≤ (K : ℝ) * ‖g a‖ + (K : ℝ) * ‖g a‖ := add_le_add (hq t a)
        ((D (f a)).le_of_opNorm_le ((hFD _).le_of_lipschitz hF) _)
      _ = 2 * (K : ℝ) * ‖g a‖ := by ring
  · exact Eventually.of_forall fun a => by
      have hp := (((hasDerivAt_id (0 : ℝ)).smul_const (g a)).const_add (f a))
      simp only [id_eq, one_smul] at hp
      have hd := HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by
        simpa only [zero_smul, add_zero] using hFD (f a)) hp
      change HasDerivAt (fun t : ℝ => F (f a + t • g a)) (D (f a) (g a)) 0 at hd
      simpa only [zero_add, zero_smul, add_zero] using
        (hasDerivAt_iff_tendsto_slope_zero.mp hd)

/-- Lipschitz composition differentiates every strongly differentiable L2 path. -/
theorem hasDerivAt_complexLp_comp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℂ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z)
    {u : ℝ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} (hu : HasDerivAt u g 0) :
    HasDerivAt (fun t : ℝ => hF.compLp h0 (u t))
      ((memLp_complexDifferential μ hD (fun z => (hFD z).le_of_lipschitz hF)
        (u 0) g).toLp (fun a => D (u 0 a) (g a))) 0 := by
  let N := hF.compLp (p := (2 : ENNReal)) (μ := μ) h0
  let A (t : ℝ) := t⁻¹ • (N (u t) - N (u 0))
  let B (t : ℝ) := t⁻¹ • (N (u 0 + t • g) - N (u 0))
  have hB := hasDerivAt_complexLp_affine μ hF h0 hD hFD (u 0) g
  rw [hasDerivAt_iff_tendsto_slope_zero] at hu hB ⊢
  simp only [zero_add, zero_smul, add_zero] at hu hB ⊢
  change Tendsto B (𝓝[≠] (0 : ℝ)) _ at hB
  have hbound : ∀ t : ℝ, t ≠ 0 →
      ‖A t - B t‖ ≤ (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ := by
    intro t ht
    have he : t⁻¹ • (u t - (u 0 + t • g)) = t⁻¹ • (u t - u 0) - g := by
      rw [sub_add_eq_sub_sub, smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
    calc
      ‖A t - B t‖ = |t|⁻¹ * ‖N (u t) - N (u 0 + t • g)‖ := by
        dsimp only [A, B]
        rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ |t|⁻¹ * ((K : ℝ) * ‖u t - (u 0 + t • g)‖) :=
        mul_le_mul_of_nonneg_left (hF.norm_compLp_sub_le h0 _ _) (inv_nonneg.mpr (abs_nonneg t))
      _ = (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ := by
        rw [← he, norm_smul, Real.norm_eq_abs, abs_inv, mul_left_comm]
  have hzero : Tendsto (fun t => ‖A t - B t‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg (A t - B t))
      (show ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖A t - B t‖ ≤
        (K : ℝ) * ‖t⁻¹ • (u t - u 0) - g‖ from
        by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact hbound t ht)
    simpa only [sub_self, norm_zero, mul_zero] using (hu.sub_const g).norm.const_mul (K : ℝ)
  have hlim := (tendsto_zero_iff_norm_tendsto_zero.mpr hzero).add hB
  simpa only [A, sub_add_cancel, zero_add] using hlim

/-- The strong L2 chain rule applies at any real path parameter. -/
theorem hasDerivAt_complexLp_comp_at {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℂ → ℂ} {K : ℝ≥0} (hF : LipschitzWith K F) (h0 : F 0 = 0)
    {D : ℂ → ℂ →L[ℝ] ℂ} (hD : Continuous D)
    (hFD : ∀ z, HasFDerivAt F (D z) z)
    {u : ℝ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} {s : ℝ} (hu : HasDerivAt u g s) :
    HasDerivAt (fun t : ℝ => hF.compLp h0 (u t))
      ((memLp_complexDifferential μ hD (fun z => (hFD z).le_of_lipschitz hF)
        (u s) g).toLp (fun a => D (u s a) (g a))) s := by
  have hs : HasDerivAt (fun t : ℝ => u (s + t)) g 0 := by
    exact (hu.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add s)
      (by simp only [id_eq, add_zero])).congr_deriv (one_smul ℝ g)
  have hc := hasDerivAt_complexLp_comp μ hF h0 hD hFD hs
  simp only [add_zero] at hc
  have ht : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
  have hr := hc.scomp_of_eq s ht (by rw [sub_self])
  change HasDerivAt (fun t : ℝ => hF.compLp h0 (u (s + (t - s)))) _ s at hr
  simpa only [← add_sub_assoc, add_sub_cancel_left, one_smul] using hr

end EinsteinFull
