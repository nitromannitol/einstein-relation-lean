import EinsteinFull.Calculus.RadialTruncationSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Primitive energy for bounded radial tests

The integrand is extended constantly to negative squared radii. This extension
does not change the energy, whose integration interval is nonnegative, and
makes the fundamental theorem of calculus apply at zero as well.
-/

open MeasureTheory Filter
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull

/-- The scalar energy whose real gradient is the bounded radial power test. -/
def radialTruncationPrimitive (ε R a : ℝ) (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * ∫ s in 0..‖z‖ ^ 2, radialTruncationWeight ε R a (max s 0)

private theorem continuous_radialWeight_extension {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    Continuous (fun s : ℝ => radialTruncationWeight ε R a (max s 0)) :=
  (continuousOn_radialTruncationWeight_slope (a := a) hε hR).1.comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)

/-- On the actual squared-radius interval the primitive uses the original weight. -/
theorem radialTruncationPrimitive_eq_integral (ε R a : ℝ) (z : ℂ) :
    radialTruncationPrimitive ε R a z =
      (1 / 2 : ℝ) * ∫ s in 0..‖z‖ ^ 2, radialTruncationWeight ε R a s := by
  unfold radialTruncationPrimitive
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le (sq_nonneg ‖z‖)] at hs
  simp only [max_eq_left hs.1]

/-- The real differential is exactly pairing with the nonlinear radial test. -/
theorem hasFDerivAt_radialTruncationPrimitive {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (z : ℂ) :
    HasFDerivAt (radialTruncationPrimitive ε R a)
      (innerSL ℝ (radialTruncationWeight ε R a (‖z‖ ^ 2) • z)) z := by
  have hc := continuous_radialWeight_extension (a := a) hε hR
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 (‖z‖ ^ 2)) (hc.stronglyMeasurableAtFilter _ _)
    hc.continuousAt).hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hh := hd.const_mul (1 / 2 : ℝ)
  apply hh.congr_fderiv
  ext w
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, max_eq_left (sq_nonneg ‖z‖), innerSL_apply_apply,
    real_inner_smul_left]
  ring

/-- The primitive vanishes at the zero function value. -/
theorem radialTruncationPrimitive_zero (ε R a : ℝ) :
    radialTruncationPrimitive ε R a 0 = 0 := by
  simp only [radialTruncationPrimitive, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, intervalIntegral.integral_same, mul_zero]

private theorem norm_sub_linearization_le {φ : ℂ → ℝ} {G : ℂ → ℂ} {K : ℝ≥0}
    (hG : LipschitzWith K G) (hd : ∀ z, HasFDerivAt φ (innerSL ℝ (G z)) z)
    (x y : ℂ) :
    ‖φ y - φ x - inner ℝ (G x) (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  let f (z : ℂ) := φ z - φ x - inner ℝ (G x) (z - x)
  have hf (z : ℂ) : HasFDerivAt f (innerSL ℝ (G z) - innerSL ℝ (G x)) z := by
    simpa only [f, ContinuousLinearMap.comp_id] using!
      ((hd z).sub_const (φ x)).sub
        ((innerSL ℝ (G x)).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hb (z : ℂ) (hz : z ∈ segment ℝ x y) :
      ‖innerSL ℝ (G z) - innerSL ℝ (G x)‖ ≤ (K : ℝ) * ‖y - x‖ := by
    calc
      _ = ‖innerSL ℝ (G z - G x)‖ := by rw [map_sub]
      _ = ‖G z - G x‖ := innerSL_apply_norm ℝ _
      _ ≤ (K : ℝ) * ‖z - x‖ := hG.norm_sub_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf z).hasFDerivWithinAt) hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, inner_zero_right, sub_zero, mul_assoc, pow_two] using h

/-- A quadratic remainder estimate uniform over the two complex arguments. -/
theorem radialTruncationPrimitive_remainder_le {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (x y : ℂ) :
    ‖radialTruncationPrimitive ε R a y - radialTruncationPrimitive ε R a x -
      inner ℝ (radialTruncationWeight ε R a (‖x‖ ^ 2) • x) (y - x)‖ ≤
        ((1 + 2 * a) * (ε + R) ^ a) * ‖y - x‖ ^ 2 :=
  norm_sub_linearization_le (lipschitzWith_radialTruncation hε hR ha)
    (hasFDerivAt_radialTruncationPrimitive hε hR) x y

/-- The scalar primitive has at most quadratic growth at every complex value. -/
theorem norm_radialTruncationPrimitive_le {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (z : ℂ) :
    ‖radialTruncationPrimitive ε R a z‖ ≤
      ((1 + 2 * a) * (ε + R) ^ a) * ‖z‖ ^ 2 := by
  simpa only [radialTruncationPrimitive_zero, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, smul_zero, inner_zero_left,
    sub_zero] using radialTruncationPrimitive_remainder_le hε hR ha 0 z

/-- The primitive defines an actual integrable energy on the entire complex L2 space. -/
theorem integrable_radialTruncationPrimitive {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℂ 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    Integrable (fun ω => radialTruncationPrimitive ε R a (f ω)) μ := by
  have hc : Continuous (radialTruncationPrimitive ε R a) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasFDerivAt_radialTruncationPrimitive hε hR z).continuousAt
  apply ((Lp.memLp f).norm.integrable_sq.const_mul
    ((1 + 2 * a) * (ε + R) ^ a)).mono'
      (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall fun ω => norm_radialTruncationPrimitive_le hε hR ha (f ω)

private theorem integral_radial_remainder_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g v : Lp ℂ 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a)
    (hv : v =ᵐ[μ] fun ω => radialTruncationWeight ε R a (‖f ω‖ ^ 2) • f ω) :
    ‖(∫ ω, radialTruncationPrimitive ε R a (g ω) ∂μ) -
        (∫ ω, radialTruncationPrimitive ε R a (f ω) ∂μ) - inner ℝ v (g - f)‖ ≤
      ((1 + 2 * a) * (ε + R) ^ a) * ‖g - f‖ ^ 2 := by
  have hi (u : Lp ℂ 2 μ) := integrable_radialTruncationPrimitive μ u hε hR ha
  have hh : Integrable (fun ω => inner ℝ (v ω) ((g - f) ω)) μ :=
    L2.integrable_inner v (g - f)
  have he : ‖g - f‖ ^ 2 = ∫ ω, ‖(g - f) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hiDiff : Integrable (fun ω => radialTruncationPrimitive ε R a (g ω) -
      radialTruncationPrimitive ε R a (f ω)) μ := (hi g).sub (hi f)
  rw [L2.inner_def, ← integral_sub (hi g) (hi f)]
  rw [← integral_sub hiDiff hh, he, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae ((hi g).sub (hi f) |>.sub hh).norm
    ((Lp.memLp (g - f)).norm.integrable_sq.const_mul _)
  filter_upwards [hv, Lp.coeFn_sub g f] with ω hvω hsub
  simp only [hvω, hsub, Pi.sub_apply]
  exact radialTruncationPrimitive_remainder_le hε hR ha (f ω) (g ω)

/-- The primitive integral is Frechet differentiable on the whole actual L2 space.
Its gradient is the actual L2 class of the bounded radial test. -/
theorem hasFDerivAt_integral_radialTruncationPrimitive {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℂ 2 μ) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasFDerivAt (fun u : Lp ℂ 2 μ => ∫ ω, radialTruncationPrimitive ε R a (u ω) ∂μ)
      (innerSL ℝ (hL.compLp hz f)) f := by
  dsimp only
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound ((1 + 2 * a) * (ε + R) ^ a) ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := Lp ℂ 2 μ) (by decide : 1 < 2))
  apply Eventually.of_forall
  intro h
  have hb := integral_radial_remainder_le μ f (f + h)
    ((lipschitzWith_radialTruncation hε hR ha).compLp (by simp only [smul_zero]) f)
    hε hR ha ((lipschitzWith_radialTruncation hε hR ha).coeFn_compLp
      (by simp only [smul_zero]) f)
  simpa only [add_sub_cancel_left, innerSL_apply_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖h‖)] using hb

/-- The derivative formula applies directly to every strongly differentiable L2 path. -/
theorem HasDerivAt.integral_radialTruncationPrimitive {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u : ℝ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} {t : ℝ}
    (hu : HasDerivAt u g t) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivAt (fun s => ∫ ω, radialTruncationPrimitive ε R a (u s ω) ∂μ)
      (inner ℝ (hL.compLp hz (u t)) g) t :=
  (hasFDerivAt_integral_radialTruncationPrimitive μ (u t) hε hR ha).comp_hasDerivAt t hu

/-- The same energy derivative is valid for one-sided strong L2 paths. -/
theorem HasDerivWithinAt.integral_radialTruncationPrimitive
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℝ → Lp ℂ 2 μ} {g : Lp ℂ 2 μ} {t : ℝ} {S : Set ℝ}
    (hu : HasDerivWithinAt u g S t) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hL := lipschitzWith_radialTruncation hε hR ha
    let hz : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    HasDerivWithinAt (fun s => ∫ ω, radialTruncationPrimitive ε R a (u s ω) ∂μ)
      (inner ℝ (hL.compLp hz (u t)) g) S t :=
  (hasFDerivAt_integral_radialTruncationPrimitive μ (u t) hε hR ha).comp_hasDerivWithinAt t hu

/-- The primitive energy is nonnegative at every actual complex value. -/
theorem radialTruncationPrimitive_nonneg {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (z : ℂ) :
    0 ≤ radialTruncationPrimitive ε R a z := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply intervalIntegral.integral_nonneg_of_forall (sq_nonneg ‖z‖)
  intro s
  exact Real.rpow_nonneg (radialTruncationBase_pos_le hε hR (le_max_right s 0)).1.le _

/-- The weighted mass is controlled by its primitive uniformly in both cutoffs.
This is the comparison needed to apply Gronwall without a cutoff-dependent rate. -/
theorem radialTruncation_mass_le_primitive {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (z : ℂ) :
    radialTruncationWeight ε R a (‖z‖ ^ 2) * ‖z‖ ^ 2 ≤
      (2 * (1 + a)) * radialTruncationPrimitive ε R a z := by
  let F (s : ℝ) := (1 + a) *
    (∫ u in 0..s, radialTruncationWeight ε R a (max u 0)) -
      s * radialTruncationWeight ε R a s
  have hc := continuous_radialWeight_extension (a := a) hε hR
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivAt F
      (a * radialTruncationWeight ε R a s - s * radialTruncationSlope ε R a s) s := by
    have hi := (intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 s) (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt)
    have h := (hi.const_mul (1 + a)).sub
      ((hasDerivAt_id s).mul (hasDerivAt_radialTruncationWeight (a := a) hε hR hs))
    apply h.congr_deriv
    simp only [max_eq_left hs, id_eq]
    ring
  have hm : MonotoneOn F (Set.Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hd s (interior_subset hs)).deriv]
      have hb := (radialTruncationSlope_mul_le hε hR ha (interior_subset hs)).2
      nlinarith only [hb])
  have hb := hm (show (0 : ℝ) ∈ Set.Ici 0 by simp) (sq_nonneg ‖z‖) (sq_nonneg ‖z‖)
  simp only [F, intervalIntegral.integral_same, mul_zero, zero_mul, sub_zero] at hb
  unfold radialTruncationPrimitive
  nlinarith only [hb]

end EinsteinFull
