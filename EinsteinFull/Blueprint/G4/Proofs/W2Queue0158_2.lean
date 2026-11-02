import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_core_u2D_extension
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinFull.Blueprint.Foundation.node_e_u3A_generators_u23_real_u2D_semigroup
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Calculus.ComplexHorizontalChainSupport
import EinsteinFull.Calculus.ComplexRadialGeneratorSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

/-!
# Extension of the actual mean response to bounded local data

The bounded-data maximum argument and resolvent approximation adapt earlier
worker proofs, with only adopted dependencies. All support lives in this
module; no HOLD module is imported.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators
noncomputable section
namespace EinsteinFull.Blueprint.W2CoreExtension
open EinsteinRelation

/-- Smooth quadratic-growth energy of the positive excess. -/
def realExcessEnergy (x : ℝ) : ℝ := if x ≤ 0 then 0 else x ^ 4 / (1 + x ^ 2)
/-- First derivative of the excess energy. -/
def realExcessTest (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else 2 * x ^ 3 * (x ^ 2 + 2) / (1 + x ^ 2) ^ 2
/-- Second derivative of the excess energy. -/
def realExcessSlope (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else 2 * x ^ 2 * (x ^ 4 + 3 * x ^ 2 + 6) / (1 + x ^ 2) ^ 3

private theorem hasDerivAt_cutPositive {f : ℝ → ℝ}
    (h0 : f 0 = 0) (hd : HasDerivAt f 0 0) :
    HasDerivAt (fun x => if x ≤ 0 then 0 else f x) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · apply (hasDerivWithinAt_iff_tendsto_slope' (s := Iio 0) (by simp)).mp
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro y hy
      simp only [mem_Iio] at hy
      simp only [if_pos hy.le]
    · simp only [le_refl, if_true]
  · apply (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi 0) (by simp)).mp
    apply hd.hasDerivWithinAt.congr
    · intro y hy
      simp only [mem_Ioi] at hy
      simp only [if_neg (not_le.mpr hy)]
    · simp only [le_refl, if_true, h0]

private theorem hasDerivAt_excessEnergyRational (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 4 / (1 + y ^ 2))
      (2 * x ^ 3 * (x ^ 2 + 2) / (1 + x ^ 2) ^ 2) x := by
  have hn : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  convert! ((hasDerivAt_id x).pow 4).div
    ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)) hn using 1
  simp only [Pi.add_apply, Pi.pow_apply, id_eq]
  ring

private theorem hasDerivAt_excessTestRational (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 3 * (y ^ 2 + 2) / (1 + y ^ 2) ^ 2)
      (2 * x ^ 2 * (x ^ 4 + 3 * x ^ 2 + 6) / (1 + x ^ 2) ^ 3) x := by
  have hn : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  convert! ((((hasDerivAt_id x).pow 3).const_mul 2).mul
    (((hasDerivAt_id x).pow 2).add_const 2)).div
    (((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2)).pow 2)
    (pow_ne_zero 2 hn) using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, id_eq]
  field_simp
  ring

/-- The excess energy is differentiable even at its contact point. -/
theorem hasDerivAt_realExcessEnergy (x : ℝ) :
    HasDerivAt realExcessEnergy (realExcessTest x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [realExcessTest, if_pos hx.le]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp only [realExcessEnergy, if_pos hy.le]
  · simpa only [realExcessEnergy, realExcessTest, le_refl, if_true] using!
      hasDerivAt_cutPositive (f := fun y : ℝ => y ^ 4 / (1 + y ^ 2))
        (by norm_num) (by simpa using! hasDerivAt_excessEnergyRational 0)
  · have h := hasDerivAt_excessEnergyRational x
    rw [realExcessTest, if_neg (not_le.mpr hx)]
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [realExcessEnergy, if_neg (not_le.mpr hy)]

/-- The admissible test has a continuous bounded derivative at the contact point. -/
theorem hasDerivAt_realExcessTest (x : ℝ) :
    HasDerivAt realExcessTest (realExcessSlope x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [realExcessSlope, if_pos hx.le]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    simp only [realExcessTest, if_pos hy.le]
  · simpa only [realExcessTest, realExcessSlope, le_refl, if_true] using!
      hasDerivAt_cutPositive
        (f := fun y : ℝ => 2 * y ^ 3 * (y ^ 2 + 2) / (1 + y ^ 2) ^ 2)
        (by norm_num) (by simpa using! hasDerivAt_excessTestRational 0)
  · rw [realExcessSlope, if_neg (not_le.mpr hx)]
    apply (hasDerivAt_excessTestRational x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    simp only [realExcessTest, if_neg (not_le.mpr hy)]

/-- The energy detects precisely a positive excess. -/
theorem realExcessEnergy_nonneg_and_eq_zero (x : ℝ) :
    0 ≤ realExcessEnergy x ∧ (realExcessEnergy x = 0 ↔ x ≤ 0) := by
  by_cases hx : x ≤ 0
  · simp [realExcessEnergy, hx]
  · have hp : 0 < x := lt_of_not_ge hx
    have he : 0 < x ^ 4 / (1 + x ^ 2) := by positivity
    simp only [realExcessEnergy, if_neg hx]
    exact ⟨he.le, iff_of_false (ne_of_gt he) hx⟩

/-- The Hessian is nonnegative and bounded uniformly on the real line. -/
theorem realExcessSlope_bounds (x : ℝ) : 0 ≤ realExcessSlope x ∧ realExcessSlope x ≤ 6 := by
  by_cases hx : x ≤ 0
  · simp only [realExcessSlope, if_pos hx]; norm_num
  · rw [realExcessSlope, if_neg hx]
    have hp : 0 < (1 + x ^ 2) ^ 3 := by positivity
    constructor
    · positivity
    · apply (div_le_iff₀ hp).mpr
      nlinarith only [sq_nonneg (x ^ 2), sq_nonneg x,
        mul_nonneg (sq_nonneg (x ^ 2)) (sq_nonneg x)]

/-- The force term vanishes at least as fast as the nonlinear energy.
This exact inequality permits Young absorption without an additive error. -/
theorem realExcessTest_sq_le (x : ℝ) :
    realExcessTest x ^ 2 ≤ 4 * realExcessSlope x * realExcessEnergy x := by
  by_cases hx : x ≤ 0
  · simp only [realExcessTest, realExcessSlope, realExcessEnergy, if_pos hx]
    norm_num
  · simp only [realExcessTest, realExcessSlope, realExcessEnergy, if_neg hx]
    have hn : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    ring_nf
    nlinarith only [sq_nonneg (x ^ 3), sq_nonneg (x ^ 4), sq_nonneg (x ^ 5)]

/-- The test has a global Lipschitz constant independent of the excess threshold. -/
theorem lipschitzWith_realExcessTest : LipschitzWith 6 realExcessTest := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_realExcessTest x).differentiableAt)
  intro x
  change ‖deriv realExcessTest x‖ ≤ (6 : ℝ)
  rw [(hasDerivAt_realExcessTest x).deriv, Real.norm_eq_abs,
    abs_of_nonneg (realExcessSlope_bounds x).1]
  exact (realExcessSlope_bounds x).2

/-- The bounded Hessian of the excess profile is continuous, including at zero. -/
theorem continuous_realExcessSlope : Continuous realExcessSlope := by
  unfold realExcessSlope
  apply Continuous.if_le continuous_const _ continuous_id continuous_const
  · intro x hx
    change x = 0 at hx
    subst x
    norm_num
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x
      exact pow_ne_zero 3 (ne_of_gt (by positivity))

/-- Quadratic energy of the real part above a nonnegative threshold. -/
def complexExcessEnergy (M : ℝ) (z : ℂ) : ℝ := realExcessEnergy (z.re - M)

/-- Its real gradient as a complex number. -/
def complexExcessTest (M : ℝ) (z : ℂ) : ℂ := realExcessTest (z.re - M)

/-- The literal differential differentiates only the real component. -/
def complexExcessDifferential (M : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (realExcessSlope (z.re - M) • Complex.ofRealCLM).comp Complex.reCLM

/-- The excess test has a continuous differential. -/
theorem continuous_complexExcessDifferential (M : ℝ) :
    Continuous (complexExcessDifferential M) := by
  exact ((continuous_realExcessSlope.comp (Complex.continuous_re.sub continuous_const)).smul
    continuous_const).clm_comp continuous_const

/-- Exact real differential of the complex excess test. -/
theorem hasFDerivAt_complexExcessTest (M : ℝ) (z : ℂ) :
    HasFDerivAt (complexExcessTest M) (complexExcessDifferential M z) z := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z
    ((hasDerivAt_realExcessTest (z.re - M)).hasFDerivAt.comp z
      (Complex.reCLM.hasFDerivAt.sub_const M))
  convert! h using 1
  ext w
  simp only [complexExcessDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    Complex.reCLM_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul, mul_comm]

/-- The excess energy has the claimed real gradient on the complex plane. -/
theorem hasFDerivAt_complexExcessEnergy (M : ℝ) (z : ℂ) :
    HasFDerivAt (complexExcessEnergy M) (innerSL ℝ (complexExcessTest M z)) z := by
  have h := (hasDerivAt_realExcessEnergy (z.re - M)).hasFDerivAt.comp z
    (Complex.reCLM.hasFDerivAt.sub_const M)
  convert! h using 1
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, Complex.reCLM_apply, innerSL_apply_apply,
    complexExcessTest, real_inner_eq_re_inner ℂ, RCLike.inner_apply,
    RCLike.re_to_complex, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, smul_eq_mul]

/-- Threshold-independent Lipschitz bound for the admissible complex test. -/
theorem lipschitzWith_complexExcessTest (M : ℝ) :
    LipschitzWith 6 (complexExcessTest M) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  change ‖(realExcessTest (z.re - M) : ℂ) - realExcessTest (w.re - M)‖ ≤
    (6 : ℝ≥0) * ‖z - w‖
  rw [← Complex.ofReal_sub, Complex.norm_real]
  exact (lipschitzWith_realExcessTest.norm_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (by simpa only [sub_sub_sub_cancel_right, Complex.sub_re] using! Complex.abs_re_le_norm (z - w))
      (by norm_num))

/-- The test vanishes at zero for every nonnegative threshold. -/
theorem complexExcessTest_zero {M : ℝ} (hM : 0 ≤ M) : complexExcessTest M 0 = 0 := by
  simp only [complexExcessTest, Complex.zero_re, zero_sub, realExcessTest,
    if_pos (neg_nonpos.mpr hM), Complex.ofReal_zero]

/-- The energy likewise vanishes at zero. -/
theorem complexExcessEnergy_zero {M : ℝ} (hM : 0 ≤ M) : complexExcessEnergy M 0 = 0 := by
  exact (realExcessEnergy_nonneg_and_eq_zero _).2.mpr (by simpa using! neg_nonpos.mpr hM)

private theorem excess_remainder_le (M : ℝ) (x y : ℂ) :
    ‖complexExcessEnergy M y - complexExcessEnergy M x -
      inner ℝ (complexExcessTest M x) (y - x)‖ ≤ 6 * ‖y - x‖ ^ 2 := by
  let f (z : ℂ) := complexExcessEnergy M z - complexExcessEnergy M x -
    inner ℝ (complexExcessTest M x) (z - x)
  have hf (z : ℂ) : HasFDerivAt f
      (innerSL ℝ (complexExcessTest M z) - innerSL ℝ (complexExcessTest M x)) z := by
    simpa only [f, ContinuousLinearMap.comp_id] using!
      ((hasFDerivAt_complexExcessEnergy M z).sub_const (complexExcessEnergy M x)).sub
        ((innerSL ℝ (complexExcessTest M x)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).sub_const x))
  have hb (z : ℂ) (hz : z ∈ segment ℝ x y) :
      ‖innerSL ℝ (complexExcessTest M z) - innerSL ℝ (complexExcessTest M x)‖ ≤
        6 * ‖y - x‖ := by
    calc
      _ = ‖complexExcessTest M z - complexExcessTest M x‖ := by
        rw [← map_sub, innerSL_apply_norm]
      _ ≤ 6 * ‖z - x‖ := (lipschitzWith_complexExcessTest M).norm_sub_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) (by norm_num)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hf z).hasFDerivWithinAt) hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [f, sub_self, inner_zero_right, sub_zero, mul_assoc, pow_two] using! h

private theorem excess_energy_norm_le {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    ‖complexExcessEnergy M z‖ ≤ 6 * ‖z‖ ^ 2 := by
  simpa only [complexExcessEnergy_zero hM, complexExcessTest_zero hM,
    sub_zero, inner_zero_left] using! excess_remainder_le M 0 z

/-- The excess energy is integrable on the full actual L2 space. -/
theorem integrable_complexExcessEnergy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℂ 2 μ) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun ω => complexExcessEnergy M (f ω)) μ := by
  have hc : Continuous (complexExcessEnergy M) :=
    continuous_iff_continuousAt.mpr fun z => (hasFDerivAt_complexExcessEnergy M z).continuousAt
  apply ((Lp.memLp f).norm.integrable_sq.const_mul 6).mono'
    (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall fun ω => excess_energy_norm_le hM (f ω)

private theorem integral_excess_remainder_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g v : Lp ℂ 2 μ) {M : ℝ} (hM : 0 ≤ M)
    (hv : v =ᵐ[μ] fun ω => complexExcessTest M (f ω)) :
    ‖(∫ ω, complexExcessEnergy M (g ω) ∂μ) -
      (∫ ω, complexExcessEnergy M (f ω) ∂μ) - inner ℝ v (g - f)‖ ≤
        6 * ‖g - f‖ ^ 2 := by
  have hi (u : Lp ℂ 2 μ) := integrable_complexExcessEnergy μ u hM
  have hh : Integrable (fun ω => inner ℝ (v ω) ((g - f) ω)) μ :=
    L2.integrable_inner v (g - f)
  have he : ‖g - f‖ ^ 2 = ∫ ω, ‖(g - f) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hiDiff : Integrable (fun ω => complexExcessEnergy M (g ω) -
      complexExcessEnergy M (f ω)) μ := (hi g).sub (hi f)
  rw [L2.inner_def, ← integral_sub (hi g) (hi f)]
  rw [← integral_sub hiDiff hh, he, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (((hi g).sub (hi f)).sub hh).norm
    ((Lp.memLp (g - f)).norm.integrable_sq.const_mul _)
  filter_upwards [hv, Lp.coeFn_sub g f] with ω hvω hsub
  simp only [hvω, hsub, Pi.sub_apply]
  exact excess_remainder_le M (f ω) (g ω)

/-- The excess energy integral is Frechet differentiable on the entire complex L2 space. -/
theorem hasFDerivAt_integral_complexExcessEnergy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℂ 2 μ) {M : ℝ} (hM : 0 ≤ M) :
    HasFDerivAt (fun u : Lp ℂ 2 μ => ∫ ω, complexExcessEnergy M (u ω) ∂μ)
      (innerSL ℝ ((lipschitzWith_complexExcessTest M).compLp (complexExcessTest_zero hM) f)) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply (Asymptotics.IsBigO.of_bound 6 ?_).trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := Lp ℂ 2 μ) (by decide : 1 < 2))
  apply Eventually.of_forall
  intro h
  have hb := integral_excess_remainder_le μ f (f + h)
    ((lipschitzWith_complexExcessTest M).compLp (complexExcessTest_zero hM) f) hM
    ((lipschitzWith_complexExcessTest M).coeFn_compLp (complexExcessTest_zero hM) f)
  simpa only [add_sub_cancel_left, innerSL_apply_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖h‖)] using! hb



private theorem excess_force_young (K b x ψ D θ : ℝ)
    (hK : 0 < K) (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hψ : ψ ^ 2 ≤ 4 * D * θ) :
    b * ψ * x ≤ (K⁻¹ / 2) * D * x ^ 2 + 2 * K * b ^ 2 * θ := by
  rcases hD.eq_or_lt with rfl | hD
  · have hzero : ψ = 0 := by nlinarith only [hψ, sq_nonneg ψ]
    simp only [hzero, mul_zero, zero_mul, zero_add]
    positivity
  · have hp : 0 ≤ (D * x - K * b * ψ) ^ 2 +
        K ^ 2 * b ^ 2 * (4 * D * θ - ψ ^ 2) :=
      add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (sub_nonneg.mpr hψ))
    have he : 2 * K * D * ((K⁻¹ / 2) * D * x ^ 2 + 2 * K * b ^ 2 * θ - b * ψ * x) =
        (D * x - K * b * ψ) ^ 2 + K ^ 2 * b ^ 2 * (4 * D * θ - ψ ^ 2) := by
      field_simp
      ring
    rw [← he] at hp
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (by positivity : 0 < 2 * K * D)).mp hp)

/-- Real force absorption retains the same excess energy with no additive term. -/
theorem realExcess_force_young {d : ℕ} (A : Mat d) (i : Fin d)
    (K lam a : ℝ) (hK : 0 < K) (hA : ∀ j, |A j i| ≤ K) (x : Fin d → ℝ) :
    lam * realExcessTest a * (∑ j, A j i * x j) ≤
      (K⁻¹ / 2) * realExcessSlope a * (∑ j, x j ^ 2) +
        (2 * (d : ℝ) * K * (lam * K) ^ 2) * realExcessEnergy a := by
  have hD := (realExcessSlope_bounds a).1
  have hθ := (realExcessEnergy_nonneg_and_eq_zero a).1
  have hp (j : Fin d) : (lam * A j i) * realExcessTest a * x j ≤
      (K⁻¹ / 2) * realExcessSlope a * x j ^ 2 +
        2 * K * (lam * K) ^ 2 * realExcessEnergy a := by
    have hb : (lam * A j i) ^ 2 ≤ (lam * K) ^ 2 := by
      simpa only [mul_pow, sq_abs] using! mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (abs_nonneg _) hK.le).mpr (hA j)) (sq_nonneg lam)
    exact (excess_force_young K (lam * A j i) (x j) _ _ _ hK hD hθ
      (realExcessTest_sq_le a)).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * K)) hθ))
  calc
    _ = ∑ j, (lam * A j i) * realExcessTest a * x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => hp j
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The excess test preserves the actual strong horizontal gradient domain. -/
theorem HasComplexHorizontalGradient.complexExcess {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G) {M : ℝ} (hM : 0 ≤ M) :
    ∃ H : Fin d → Lp ℂ 2 Q,
      HasComplexHorizontalGradient Q hQ
        ((lipschitzWith_complexExcessTest M).compLp (complexExcessTest_zero hM) f) H ∧
      ∀ j, H j =ᵐ[Q] fun ω =>
        (realExcessSlope ((f ω).re - M) * (G j ω).re : ℂ) := by
  let H := fun j => (memLp_complexDifferential Q (continuous_complexExcessDifferential M)
    (fun z => (hasFDerivAt_complexExcessTest M z).le_of_lipschitz
      (lipschitzWith_complexExcessTest M)) f (G j)).toLp
        (fun ω => complexExcessDifferential M (f ω) (G j ω))
  refine ⟨H, hf.compLp (lipschitzWith_complexExcessTest M) (complexExcessTest_zero hM)
    (continuous_complexExcessDifferential M) (hasFDerivAt_complexExcessTest M), ?_⟩
  intro j
  have he := (memLp_complexDifferential Q (continuous_complexExcessDifferential M)
    (fun z => (hasFDerivAt_complexExcessTest M z).le_of_lipschitz
      (lipschitzWith_complexExcessTest M)) f (G j)).coeFn_toLp
  filter_upwards [he] with ω hω
  change H j ω = complexExcessDifferential M (f ω) (G j ω) at hω
  rw [hω]
  simp only [complexExcessDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.real_smul]

open HasComplexHorizontalGradient

private theorem complexExcess_pointwise_rate {d : ℕ} (A : Mat d) (i : Fin d)
    (K lam M : ℝ) (hK : 0 < K) (hA : ∀ j, |A j i| ≤ K)
    (hcoer : ∀ x : Vec d, K⁻¹ * euclideanSq x ≤ dotProduct x (A.mulVec x))
    (z : ℂ) (G : Fin d → ℂ) :
    -(1 / 2 : ℝ) * (∑ j, ∑ k,
      star (realExcessSlope (z.re - M) * (G j).re : ℂ) * (A j k : ℂ) * G k).re +
      ((lam : ℂ) * star (complexExcessTest M z) * (∑ j, (A j i : ℂ) * G j)).re ≤
        (2 * (d : ℝ) * K * (lam * K) ^ 2) * complexExcessEnergy M z := by
  let x : Vec d := fun j => (G j).re
  let D := realExcessSlope (z.re - M)
  have he : (∑ j, ∑ k, star (D * x j : ℂ) * (A j k : ℂ) * G k).re =
      D * dotProduct x (A.mulVec x) := by
    change Complex.reCLM (∑ j, ∑ k, star (D * x j : ℂ) * (A j k : ℂ) * G k) = _
    simp only [map_sum, Complex.reCLM_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      zero_mul, mul_zero, sub_zero, add_zero, neg_zero,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [x]
    ring
  have hf : ((lam : ℂ) * star (complexExcessTest M z) *
      (∑ j, (A j i : ℂ) * G j)).re =
      lam * realExcessTest (z.re - M) * (∑ j, A j i * x j) := by
    change Complex.reCLM ((lam : ℂ) * star (complexExcessTest M z) *
      (∑ j, (A j i : ℂ) * G j)) = _
    simp only [Complex.reCLM_apply, complexExcessTest, Complex.star_def,
      Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, x]
    rw [Complex.re_sum]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hf]
  change -(1 / 2 : ℝ) * (∑ j, ∑ k,
    star (D * x j : ℂ) * (A j k : ℂ) * G k).re + _ ≤ _
  rw [he]
  have hc := mul_le_mul_of_nonneg_left (hcoer x) (realExcessSlope_bounds (z.re - M)).1
  have hy := realExcess_force_young A i K lam (z.re - M) hK hA x
  have hs : euclideanSq x = ∑ j, x j ^ 2 := by
    simp only [euclideanSq, dot, pow_two]
  rw [hs] at hc
  change _ ≤ _ + _ * complexExcessEnergy M z at hy
  change _ ≤ _
  dsimp only [D] at *
  nlinarith only [hc, hy]

private theorem realL2_inner_eq_re {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : Lp ℂ 2 μ) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

/-- The positive-excess energy has a homogeneous rate bound on the actual full
signed real generator graph. The threshold does not enter the rate constant. -/
theorem IsComplexGeneratorPair.realExcess_energy_rate
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i (lam : ℂ) f g)
    {M : ℝ} (hM : 0 ≤ M) :
    inner ℝ ((lipschitzWith_complexExcessTest M).compLp (complexExcessTest_zero hM) f) g ≤
      (2 * (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (lam * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) *
          (∫ ω, complexExcessEnergy M (f ω) ∂reducedLaw Q) := by
  obtain ⟨G, hG, hw⟩ := hfg
  have hfg : IsComplexGeneratorPair Q i (lam : ℂ) f g := ⟨G, hG, hw⟩
  obtain ⟨H, hv, hH⟩ := HasComplexHorizontalGradient.complexExcess hG hM
  let v := (lipschitzWith_complexExcessTest M).compLp (complexExcessTest_zero hM) f
  let D := complexForceDrift Q i (WithLp.toLp 2 G)
  let E := fun ω => ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hE : Integrable E (reducedLaw Q) := integrable_reduced_complex_energy Q H G
  have hF : Integrable (fun ω => (lam : ℂ) * star (v ω) * D ω) (reducedLaw Q) := by
    simpa only [mul_assoc] using!
      (((Lp.memLp v).star.integrable_mul (Lp.memLp D)).const_mul (lam : ℂ))
  have hEr : Integrable (fun ω => (E ω).re) (reducedLaw Q) := hE.re
  have hFr : Integrable (fun ω => ((lam : ℂ) * star (v ω) * D ω).re) (reducedLaw Q) := hF.re
  have hErw : (∫ ω, (E ω).re ∂reducedLaw Q) = (∫ ω, E ω ∂reducedLaw Q).re :=
    integral_re hE
  have hFrw : (∫ ω, ((lam : ℂ) * star (v ω) * D ω).re ∂reducedLaw Q) =
      (∫ ω, (lam : ℂ) * star (v ω) * D ω ∂reducedLaw Q).re := integral_re hF
  have hleft : inner ℝ v g = ∫ ω,
      -(1 / 2 : ℝ) * (E ω).re + ((lam : ℂ) * star (v ω) * D ω).re ∂reducedLaw Q := by
    rw [integral_add (hEr.const_mul _) hFr, integral_const_mul,
      hErw, hFrw, realL2_inner_eq_re,
      hfg.conjugate_test hG v H hv]
    have hf : (∫ ω, (lam : ℂ) * star (v ω) * D ω ∂reducedLaw Q) =
        (lam : ℂ) * inner ℂ v D := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        simp only [RCLike.inner_apply, Complex.star_def]
        ring
    rw [hf, Complex.add_re]
    congr 1
    simp only [Complex.mul_re]
    norm_num [E]
  rw [hleft, ← integral_const_mul]
  apply integral_mono_ae ((hEr.const_mul _).add hFr)
    ((integrable_complexExcessEnergy (reducedLaw Q) f hM).const_mul _)
  filter_upwards [(lipschitzWith_complexExcessTest M).coeFn_compLp
      (complexExcessTest_zero hM) f, ae_all_iff.mpr hH,
    complexForceDrift_coe Q i (WithLp.toLp 2 G),
    Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hvω hHω hDω hω
  change v ω = complexExcessTest M (f ω) at hvω
  change D ω = ∑ j, (ω.1 0 j i : ℂ) * G j ω at hDω
  change -(1 / 2 : ℝ) * (E ω).re + ((lam : ℂ) * star (v ω) * D ω).re ≤ _
  dsimp only [E]
  simp only [hHω, hvω, hDω]
  have hcol (j : Fin d) : |ω.1 0 j i| ≤ K :=
    abs_entry_le_of_quadratic_bounds hK.le (ω.1 0) (hω 0).1
      (fun ξ => (mul_nonneg (inv_nonneg.mpr hK.le) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1) (fun ξ => ((hω 0).2 ξ).2) j i
  exact complexExcess_pointwise_rate (ω.1 0) i K lam M hK hcol
    (fun ξ => ((hω 0).2 ξ).1) (f ω) (fun j => G j ω)



open IsComplexGeneratorPair

/-- The excess energy along the full generator-domain orbit satisfies Gronwall's bound. -/
theorem IsComplexEnvironmentSemigroup.realExcess_energy_growth
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i (lam : ℂ) f g)
    {M : ℝ} (hM : 0 ≤ M) (t : ℝ≥0) :
    (∫ ω, complexExcessEnergy M (P t f ω) ∂reducedLaw Q) ≤
      (∫ ω, complexExcessEnergy M (f ω) ∂reducedLaw Q) *
        Real.exp ((2 * (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (lam * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)) := by
  let hL := lipschitzWith_complexExcessTest M
  let hz := complexExcessTest_zero hM
  let E (s : ℝ) := ∫ ω, complexExcessEnergy M (P s.toNNReal f ω) ∂reducedLaw Q
  let D (s : ℝ) := inner ℝ (hL.compLp hz (P s.toNNReal f)) (P s.toNNReal g)
  let C := 2 * (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
    (lam * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, complexExcessEnergy M (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_complexExcessEnergy (reducedLaw Q) u hM).continuousAt
  have hE : Continuous E := hF.comp ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have hd (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt E (D s) (Ici s) s := by
    exact (hasFDerivAt_integral_complexExcessEnergy (reducedLaw Q) (P s.toNNReal f) hM).comp_hasDerivWithinAt s (hP.hasDerivWithinAt_orbit hfg s hs)
  have hr (s : ℝ) : D s ≤ C * E s :=
    IsComplexGeneratorPair.realExcess_energy_rate (hP.map_generator hfg s.toNNReal) hM
  have hb := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := D) (δ := E 0) (K := C) (ε := 0) (a := 0) (b := (t : ℝ))
    hE.continuousOn (fun s hs _ hr => (hd s hs.1).liminf_right_slope_le hr)
    le_rfl (fun s _ => by simpa only [add_zero] using! hr s)
    (t : ℝ) ⟨t.property, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hb
  simpa only [E, C, Real.toNNReal_zero, Real.toNNReal_coe, hP.1,
    ContinuousLinearMap.id_apply] using! hb

open IsComplexEnvironmentSemigroup

/-- Actual resolvent approximation removes every datum regularity assumption. -/
theorem IsComplexEnvironmentSemigroup.realExcess_energy_growth_all
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (f : Lp ℂ 2 (reducedLaw Q))
    {M : ℝ} (hM : 0 ≤ M) (t : ℝ≥0) :
    (∫ ω, complexExcessEnergy M (P t f ω) ∂reducedLaw Q) ≤
      (∫ ω, complexExcessEnergy M (f ω) ∂reducedLaw Q) *
        Real.exp ((2 * (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (lam * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)) := by
  have hF : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      ∫ ω, complexExcessEnergy M (u ω) ∂reducedLaw Q) :=
    continuous_iff_continuousAt.mpr fun u =>
      (hasFDerivAt_integral_complexExcessEnergy (reducedLaw Q) u hM).continuousAt
  have hu := tendsto_forcedComplexResolventApproximation Q i (lam : ℂ) f
  exact le_of_tendsto_of_tendsto
    (hF.continuousAt.tendsto.comp ((P t).continuous.tendsto f |>.comp hu))
    ((hF.continuousAt.tendsto.comp hu).mul_const _)
    (Eventually.of_forall fun n => IsComplexEnvironmentSemigroup.realExcess_energy_growth hP
      (forcedComplexYosida_graph Q i (lam : ℂ) n f) hM t)

/-- Every nonnegative upper bound on the real part is preserved, for arbitrary
signed real force and arbitrary actual L2 data. -/
theorem IsComplexEnvironmentSemigroup.ae_re_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (f : Lp ℂ 2 (reducedLaw Q))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ ω ∂reducedLaw Q, (f ω).re ≤ M) (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q, (P t f ω).re ≤ M := by
  have hzero : (∫ ω, complexExcessEnergy M (f ω) ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with ω hω
    exact (realExcessEnergy_nonneg_and_eq_zero _).2.mpr (sub_nonpos.mpr hω)
  have hb := IsComplexEnvironmentSemigroup.realExcess_energy_growth_all hP f hM t
  rw [hzero, zero_mul] at hb
  have hn : ∀ᵐ ω ∂reducedLaw Q, 0 ≤ complexExcessEnergy M (P t f ω) :=
    Eventually.of_forall fun ω => (realExcessEnergy_nonneg_and_eq_zero _).1
  have he : (∫ ω, complexExcessEnergy M (P t f ω) ∂reducedLaw Q) = 0 :=
    le_antisymm hb (integral_nonneg_of_ae hn)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn
    (integrable_complexExcessEnergy (reducedLaw Q) (P t f) hM)).mp he
  filter_upwards [hz] with ω hω
  exact sub_nonpos.mp ((realExcessEnergy_nonneg_and_eq_zero _).2.mp hω)

/-- Bounded complex data remain uniformly bounded for signed real force.
The constant two comes from the four real and imaginary half-plane bounds. -/
theorem IsComplexEnvironmentSemigroup.ae_norm_le_two_mul
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (f : Lp ℂ 2 (reducedLaw Q))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) (t : ℝ≥0) :
    ∀ᵐ ω ∂reducedLaw Q, ‖P t f ω‖ ≤ 2 * M := by
  have hb (c : ℂ) (hc : ‖c‖ ≤ 1) :
      ∀ᵐ ω ∂reducedLaw Q, (c * P t f ω).re ≤ M := by
    have hin : ∀ᵐ ω ∂reducedLaw Q, ((c • f) ω).re ≤ M := by
      filter_upwards [hf, Lp.coeFn_smul c f] with ω hω hrep
      rw [hrep]
      exact (Complex.re_le_norm _).trans (by
        rw [Pi.smul_apply, norm_smul]
        exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa using! hω))
    have hout := IsComplexEnvironmentSemigroup.ae_re_le hP (c • f) hM hin t
    rw [map_smul] at hout
    filter_upwards [hout, Lp.coeFn_smul c (P t f)] with ω hω hrep
    simpa only [hrep, smul_eq_mul] using! hω
  filter_upwards [hb 1 (by simp), hb (-1) (by simp), hb Complex.I (by simp),
    hb (-Complex.I) (by simp)] with ω h₁ h₂ h₃ h₄
  simp only [one_mul, neg_one_mul, Complex.neg_re] at h₁ h₂
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    zero_mul, one_mul, neg_zero, neg_one_mul, zero_sub, neg_neg] at h₃ h₄
  have hr : |(P t f ω).re| ≤ M := abs_le.mpr ⟨by linarith only [h₂], h₁⟩
  have hi : |(P t f ω).im| ≤ M := abs_le.mpr ⟨by linarith only [h₃], h₄⟩
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith only [hr, hi])

/-- A bounded datum has a uniform actual L2 orbit bound at every signed real force. -/
theorem IsComplexEnvironmentSemigroup.norm_le_two_mul_of_ae_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (f : Lp ℂ 2 (reducedLaw Q))
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) (t : ℝ≥0) :
    ‖P t f‖ ≤ 2 * M := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  simpa [measureUnivNNReal] using!
    Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2 * M) (IsComplexEnvironmentSemigroup.ae_norm_le_two_mul hP f hM hf t)


private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private def meanCLM {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2
    (Lp.const 2 (reducedLaw Q) 1)

private theorem meanCLM_apply {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) : meanCLM Q f = ∫ ω, f ω ∂reducedLaw Q := by
  rw [meanCLM, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
  simp only [hω, Function.const_apply, ContinuousLinearMap.mul_apply', one_mul]

private def pairCLM {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (b : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 b

private theorem pairCLM_apply {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (b f : Lp ℂ 2 (reducedLaw Q)) :
    pairCLM Q b f = ∫ ω, b ω * f ω ∂reducedLaw Q := by
  simp only [pairCLM, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply']

/-- Mean balance on the full generator domain, with the literal reduced drift. -/
theorem IsComplexGeneratorPair.integral_eq_drift_pairing
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) :
    (∫ ω, g ω ∂reducedLaw Q) =
      -(2 * ζ) * ∫ ω, β i ω * f ω ∂reducedLaw Q := by
  obtain ⟨G, hG, hm⟩ := hfg.integral_eq
  rw [hβ.integral_mul i f G hG, hm]
  ring

/-- The generator-domain mean orbit has the exact response right derivative. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_mean_response
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ ω, P s.toNNReal f ω ∂reducedLaw Q)
      (-(2 * ζ) * ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q) (Ici t) t := by
  have hd := ((meanCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
    (hP.hasDerivWithinAt_orbit hfg t ht)
  change HasDerivWithinAt (fun s : ℝ => meanCLM Q (P s.toNNReal f))
    (meanCLM Q (P t.toNNReal g)) (Ici t) t at hd
  simpa only [meanCLM_apply, IsComplexGeneratorPair.integral_eq_drift_pairing hβ (hP.map_generator hfg t.toNNReal)]
    using! hd

/-- Exact finite-time mean response for every full generator-domain datum. -/
theorem IsComplexEnvironmentSemigroup.mean_response_of_generator
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (T : ℝ≥0) :
    (∫ ω, P T f ω ∂reducedLaw Q) = (∫ ω, f ω ∂reducedLaw Q) -
      (2 * ζ) * ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q := by
  have hc := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hm := (continuous_complexL2_integral (reducedLaw Q)).comp hc
  have hb := (pairCLM Q (β i)).continuous.comp hc
  change Continuous (fun t : ℝ => pairCLM Q (β i) (P t.toNNReal f)) at hb
  simp only [pairCLM_apply] at hb
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    T.property hm.continuousOn
    (fun t ht => (IsComplexEnvironmentSemigroup.hasDerivWithinAt_mean_response hβ hP hfg t ht.1.le).mono
      Ioi_subset_Ici_self) ((continuous_const.mul hb).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at he
  dsimp only [Function.comp_def] at he
  have ht : (T : ℝ).toNNReal = T := Real.toNNReal_coe
  simp only [Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply] at he
  have hT : (∫ ω, P (T : ℝ).toNNReal f ω ∂reducedLaw Q) =
      ∫ ω, P T f ω ∂reducedLaw Q :=
    congrArg (fun t : ℝ≥0 => ∫ ω, P t f ω ∂reducedLaw Q) ht
  calc
    _ = ∫ ω, P (T : ℝ).toNNReal f ω ∂reducedLaw Q := hT.symm
    _ = -(2 * ζ) * (∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q) +
        ∫ ω, f ω ∂reducedLaw Q := (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by ring

/-- Exact finite-time response on all actual complex L2 data, without a core premise. -/
theorem IsComplexEnvironmentSemigroup.mean_response
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    (∫ ω, P T f ω ∂reducedLaw Q) = (∫ ω, f ω ∂reducedLaw Q) -
      (2 * ζ) * ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q := by
  let u : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n =>
    forcedComplexResolventApproximation Q i ζ n f
  let L := pairCLM Q (β i)
  let C := ‖L‖ * (Real.exp (complexForceShift d D.ellipticity ζ * (T : ℝ)) * ‖f‖)
  have hu : Tendsto u atTop (𝓝 f) := tendsto_forcedComplexResolventApproximation Q i ζ f
  have hc (n : ℕ) : Continuous (fun t : ℝ => L (P t.toNNReal (u n))) :=
    L.continuous.comp ((hP.2.2.1 (u n)).comp continuous_real_toNNReal)
  have hi : Tendsto (fun n => ∫ t in Ioc (0 : ℝ) (T : ℝ), L (P t.toNNReal (u n)))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) (T : ℝ), L (P t.toNNReal f))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hc n).aestronglyMeasurable) (integrable_const C)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      apply (L.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
      apply ((P t.toNNReal).le_opNorm (u n)).trans
      apply mul_le_mul (le_trans (hP.norm_le _) ?_)
        (norm_forcedComplexResolventApproximation_le Q i ζ n f) (norm_nonneg _) (Real.exp_nonneg _)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (complexForceShift_nonneg Q ζ)
      rw [Real.coe_toNNReal t ht.1.le]
      exact ht.2
    · filter_upwards with t
      exact (L.continuous.tendsto _).comp (((P t.toNNReal).continuous.tendsto f).comp hu)
  simp only [L, pairCLM_apply] at hi
  have hei (g : ℝ → ℂ) : (∫ t in (0 : ℝ)..(T : ℝ), g t) =
      ∫ t in Ioc (0 : ℝ) (T : ℝ), g t := intervalIntegral.integral_of_le T.property
  simp only [hei]
  have hl := (continuous_complexL2_integral (reducedLaw Q)).tendsto (P T f)
    |>.comp (((P T).continuous.tendsto f).comp hu)
  have hr := ((continuous_complexL2_integral (reducedLaw Q)).tendsto f |>.comp hu).sub
    (hi.const_mul (2 * ζ))
  apply tendsto_nhds_unique hl
  apply hr.congr
  intro n
  simpa only [u, Function.comp_def, hei] using!
    (IsComplexEnvironmentSemigroup.mean_response_of_generator hβ hP (forcedComplexYosida_graph Q i ζ n f) T).symm


/-- The finite-time response gives the right derivative of the mean for every L2 datum. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_mean_response_all
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => ∫ ω, P s.toNNReal f ω ∂reducedLaw Q)
      (-(2 * ζ) * ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q) (Ici t) t := by
  suffices hh : HasDerivWithinAt (fun s : ℝ => meanCLM Q (P s.toNNReal f))
      (-(2 * ζ) * pairCLM Q (β i) (P t.toNNReal f)) (Ici t) t by
    simpa only [meanCLM_apply, pairCLM_apply] using! hh
  have hc := (pairCLM Q (β i)).continuous.comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (2 * ζ)
  have he := hd.const_sub (meanCLM Q f)
  have he' : HasDerivAt (fun r => meanCLM Q f - (2 * ζ) *
      ∫ x in (0 : ℝ)..r, pairCLM Q (β i) (P x.toNNReal f))
      (-(2 * ζ) * pairCLM Q (β i) (P t.toNNReal f)) t := by
    convert! he using 1
    simp only [Function.comp_def]
    ring
  apply he'.hasDerivWithinAt.congr
  · intro r hr
    simpa only [meanCLM_apply, pairCLM_apply, Real.coe_toNNReal r (ht.trans hr)] using!
      IsComplexEnvironmentSemigroup.mean_response hβ hP f r.toNNReal
  · simpa only [meanCLM_apply, pairCLM_apply, Real.coe_toNNReal t ht] using!
      IsComplexEnvironmentSemigroup.mean_response hβ hP f t.toNNReal

/-- Every positive damping parameter makes the actual orbit of bounded data integrable,
without a force growth-shift restriction. -/
theorem IsComplexEnvironmentSemigroup.integrable_laplace_orbit_of_ae_bound
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-s * t) • P t.toNNReal f) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-s * t) • P t.toNNReal f) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((hP.2.2.1 f).comp continuous_real_toNNReal)
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0).mul_const (2 * M)).mono'
    hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (IsComplexEnvironmentSemigroup.norm_le_two_mul_of_ae_bound hP f hM hf t.toNNReal) (Real.exp_nonneg _)

/-- Absolute convergence of every actual bilinear Laplace pairing of bounded data
at every positive damping parameter. -/
theorem IsComplexEnvironmentSemigroup.integrable_laplace_pairing_of_ae_bound
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (f b : Lp ℂ 2 (reducedLaw Q)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => (Real.exp (-s * t) : ℂ) *
      ∫ ω, b ω * P t.toNNReal f ω ∂reducedLaw Q) (Ioi 0) := by
  have hi := ((pairCLM Q b).restrictScalars ℝ).integrable_comp
    (IsComplexEnvironmentSemigroup.integrable_laplace_orbit_of_ae_bound hP f hM hf s hs)
  simpa only [map_smul, Complex.real_smul, ContinuousLinearMap.coe_restrictScalars', pairCLM_apply] using! hi

/-- The literal Abel response holds for bounded data at every signed real force
and every positive damping parameter. -/
theorem IsComplexEnvironmentSemigroup.abel_response_of_ae_bound
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M) (s : ℝ) (hs : 0 < s) :
    (s : ℂ) * (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, P t.toNNReal f ω ∂reducedLaw Q) =
      (∫ ω, f ω ∂reducedLaw Q) - (2 * lam : ℂ) *
        (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q) := by
  let m (t : ℝ) := meanCLM Q (P t.toNNReal f)
  let b (t : ℝ) := pairCLM Q (β i) (P t.toNNReal f)
  let F (t : ℝ) := -(Real.exp (-s * t) • m t)
  let G (t : ℝ) := (s : ℂ) * ((Real.exp (-s * t) : ℂ) * m t) +
    (2 * lam : ℂ) * ((Real.exp (-s * t) : ℂ) * b t)
  have hm : Continuous m := (meanCLM Q).continuous.comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have hb : Continuous b := (pairCLM Q (β i)).continuous.comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have he : Continuous (fun t : ℝ => Real.exp (-s * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hF : Continuous F := (he.smul hm).neg
  have hG : Continuous G :=
    (continuous_const.mul (Complex.continuous_ofReal.comp he |>.mul hm)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp he |>.mul hb))
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt F (G t) (Ici t) t := by
    have hexp := ((hasDerivAt_id t).const_mul (-s)).exp
    have hmean : HasDerivWithinAt m (-(2 * (lam : ℂ)) * b t) (Ici t) t := by
      simpa only [m, b, meanCLM_apply, pairCLM_apply] using!
        IsComplexEnvironmentSemigroup.hasDerivWithinAt_mean_response_all hβ hP f t ht
    have hh := (hexp.hasDerivWithinAt.smul hmean).neg
    convert! hh using 1
    simp only [F, G, Pi.neg_apply, Pi.smul_apply, id_eq, mul_one, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hfinite (T : ℝ) (hT : 0 ≤ T) : (∫ t in (0 : ℝ)..T, G t) = F T - F 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hF.continuousOn
      (fun t ht => (hd t ht.1.le).mono Ioi_subset_Ici_self) (hG.intervalIntegrable 0 T)
  have hi := IsComplexEnvironmentSemigroup.integrable_laplace_orbit_of_ae_bound hP f hM hf s hs
  have him := ((meanCLM Q).restrictScalars ℝ).integrable_comp hi
  have hib := ((pairCLM Q (β i)).restrictScalars ℝ).integrable_comp hi
  simp only [map_smul, Complex.real_smul, ContinuousLinearMap.coe_restrictScalars'] at him hib
  have hiG : IntegrableOn G (Ioi 0) := (him.const_mul (s : ℂ)).add (hib.const_mul (2 * lam : ℂ))
  have hexp : Tendsto (fun t : ℝ => Real.exp (-s * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hs))
  have hzero : Tendsto F atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [zero_mul] using! hexp.mul_const (‖meanCLM Q‖ * (2 * M)))
    exact Eventually.of_forall fun t => by
      simp only [F, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact ((meanCLM Q).le_opNorm (P t.toNNReal f)).trans
        (mul_le_mul_of_nonneg_left (IsComplexEnvironmentSemigroup.norm_le_two_mul_of_ae_bound hP f hM hf t.toNNReal)
          (norm_nonneg _))
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hiG tendsto_id
  have hlim' := hzero.sub_const (F 0)
  have hid : (∫ t in Ioi (0 : ℝ), G t) = -F 0 := by
    apply tendsto_nhds_unique hlim
    simp only [zero_sub] at hlim'
    apply hlim'.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hfinite T hT).symm
  change (∫ t in Ioi (0 : ℝ),
    (s : ℂ) * ((Real.exp (-s * t) : ℂ) * m t) +
    (2 * lam : ℂ) * ((Real.exp (-s * t) : ℂ) * b t)) = -F 0 at hid
  rw [integral_add (him.const_mul _) (hib.const_mul _), integral_const_mul,
    integral_const_mul] at hid
  simp only [F, m, Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply,
    mul_zero, Real.exp_zero, one_smul, neg_neg, meanCLM_apply, pairCLM_apply] at hid
  linear_combination hid

/-- This is the exact first conjunct of the frozen response proposition, with
arbitrary coordinate and with no locality needed beyond the stated bounded data. -/
theorem IsComplexEnvironmentSemigroup.abel_response_boundedLocal
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : IsBoundedLocalObservation Q f)
    (s : ℝ) (hs : 0 < s) :
    (s : ℂ) * (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
      ∫ ω, P t.toNNReal f ω ∂reducedLaw Q) =
      (∫ ω, f ω ∂reducedLaw Q) - (2 * lam : ℂ) *
        (∫ t in Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) *
          ∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q) := by
  obtain ⟨_, _, g, _, hrep, M, hM⟩ := hf
  apply IsComplexEnvironmentSemigroup.abel_response_of_ae_bound hβ hP f (abs_nonneg M) ?_ s hs
  filter_upwards [hrep] with ω hω
  rw [← hω, Complex.norm_real, Real.norm_eq_abs]
  exact (hM ω).trans (le_abs_self M)


/-- Positive-time differentiation of the mean needs no regularity of the datum. -/
theorem hasDerivAt_mean_response
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => ∫ ω, P u.toNNReal f ω ∂reducedLaw Q)
      (-(2 * ζ) * (∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q)) t := by
  have hc := (pairCLM Q (β i)).continuous.comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hc.continuousAt).const_mul (2 * ζ)
  have he := hd.const_sub (meanCLM Q f)
  have he' : HasDerivAt (fun r => meanCLM Q f - (2 * ζ) *
      ∫ x in (0 : ℝ)..r, pairCLM Q (β i) (P x.toNNReal f))
      (-(2 * ζ) * (∫ ω, β i ω * P t.toNNReal f ω ∂reducedLaw Q)) t := by
    convert! he using 1
    simp only [Function.comp_def, pairCLM_apply]
    ring
  apply he'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  simpa only [meanCLM_apply, pairCLM_apply, Real.coe_toNNReal r hr.le] using!
    IsComplexEnvironmentSemigroup.mean_response hβ hP f r.toNNReal

end EinsteinFull.Blueprint.W2CoreExtension

namespace EinsteinFull.Blueprint
open EinsteinRelation W2CoreExtension W2CoreExtension.IsComplexEnvironmentSemigroup

/-- The exact graph reduction for the bounded local mean response extension. -/
@[nolint unusedArguments]
theorem node_p_u3A_response_u23_core_u2D_extension_of_deps
    (_hstationary : node_stationary_u2D_environmentStmt)
    (_hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2) :
    node_p_u3A_response_u23_core_u2D_extensionStmt := by
  intro d hd D Q hQ β a μ hβ _ha _hμ lam P hP F hF
  constructor
  · intro t ht
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using!
      hasDerivAt_mean_response hβ hP F t ht
  · exact fun s hs => W2CoreExtension.IsComplexEnvironmentSemigroup.abel_response_boundedLocal hβ hP F hF s hs

end EinsteinFull.Blueprint
