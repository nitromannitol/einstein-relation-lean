import EinsteinFull.Work.W4.HomogeneousHorizontalCalculusSupport
import EinsteinFull.Calculus.SchwartzAverageSupport
import EinsteinFull.Frozen.ComplexHorizontalGradient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Horizontal H1 control for the actual homogeneous Gaussian comparison leg

Only adopted Gaussian operators and literal Schwartz convolution are used.
The gradient has the Euclidean PiLp 2 norm; complex force is arbitrary.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal LineDeriv

noncomputable section
namespace EinsteinFull
open EinsteinRelation
variable {d : ℕ} {Λ₀ r₀ : ℝ}

private theorem schwartz_translate_domination (ψ : SchwartzMap (Vec d) ℂ) :
    ∃ b : Vec d → ℝ, Integrable b ∧ ∀ x h : Vec d, ‖h‖ ≤ 1 → ‖ψ (x + h)‖ ≤ b x := by
  let n := (volume : Measure (Vec d)).integrablePower
  let C : ℝ := |(2 : ℝ) ^ n * (Finset.Iic (n, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) ψ| + 1
  have hdec (y : Vec d) : (1 + ‖y‖) ^ n * ‖ψ y‖ ≤ C := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (n, 0)) le_rfl le_rfl ψ y
    simp only [norm_iteratedFDeriv_zero] at h
    exact h.trans ((le_abs_self _).trans (by dsimp only [C]; linarith))
  let b := fun x : Vec d => (2 ^ n * C) * (1 + ‖x‖) ^ (-(n : ℝ))
  refine ⟨b, ((Measure.integrable_pow_neg_integrablePower (volume : Measure (Vec d))).const_mul _), ?_⟩
  intro x h hh
  have hn : 1 + ‖x‖ ≤ 2 * (1 + ‖x + h‖) := by
    have hx := norm_sub_le (x + h) h
    rw [add_sub_cancel_right] at hx
    linarith [norm_nonneg (x + h)]
  have hbound : (1 + ‖x‖) ^ n * ‖ψ (x + h)‖ ≤ 2 ^ n * C := by
    calc
      _ ≤ (2 * (1 + ‖x + h‖)) ^ n * ‖ψ (x + h)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hn n) (norm_nonneg _)
      _ = 2 ^ n * ((1 + ‖x + h‖) ^ n * ‖ψ (x + h)‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
  dsimp only [b]
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast]
  exact (le_div_iff₀ (by positivity : 0 < (1 + ‖x‖) ^ n)).mpr
    (by simpa only [div_eq_mul_inv, mul_comm] using! hbound)

/-- Every stationary Schwartz convolution of arbitrary L² data has the genuine
strong horizontal derivative, with the literal differentiated test kernel. -/
theorem hasComplexHorizontalDerivative_schwartzAverage_main
    (Q : EnvironmentLaw d Λ₀ r₀) (ψ : SchwartzMap (Vec d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ F)
      (stationarySchwartzAverage Q (∂_{unitVector j} ψ) F) := by
  letI := reducedLaw_probability Q
  let T := fun x : Vec d => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
  have hT : Continuous (fun x : Vec d => T x F) :=
    (continuous_complexTranslation _ (reducedLaw_stationary Q)).comp (continuous_id.prodMk continuous_const)
  obtain ⟨b, hb, hbound⟩ := schwartz_translate_domination (∂_{unitVector j} ψ)
  have hc (t : ℝ) : Continuous (fun x : Vec d => ψ (t • unitVector j - x) • T x F) :=
    (ψ.continuous.comp (continuous_const.sub continuous_id)).smul hT
  have hc' : Continuous (fun x : Vec d => (∂_{unitVector j} ψ) (-x) • T x F) :=
    ((∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ).continuous.comp continuous_neg).smul hT
  have hdiff (x : Vec d) (t : ℝ) :
      HasDerivAt (fun u : ℝ => ψ (u • unitVector j - x) • T x F)
        ((∂_{unitVector j} ψ) (t • unitVector j - x) • T x F) t := by
    have ha : HasDerivAt (fun u : ℝ => u • unitVector j - x) (unitVector j) t := by
      simpa only [one_smul] using! ((hasDerivAt_id t).smul_const (unitVector j)).sub_const x
    exact (ψ.differentiableAt.hasFDerivAt.comp_hasDerivAt t ha).smul_const (T x F)
  have hint : Integrable (fun x : Vec d => ψ ((0 : ℝ) • unitVector j - x) • T x F) := by
    simpa only [zero_smul, zero_sub] using! integrable_stationarySchwartzAverage_integrand Q ψ F
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => ψ (t • unitVector j - x) • T x F)
    (F' := fun t x => (∂_{unitVector j} ψ) (t • unitVector j - x) • T x F)
    (x₀ := (0 : ℝ)) (s := Metric.ball 0 1) (bound := fun x => b (-x) * ‖F‖) (Metric.ball_mem_nhds _ zero_lt_one)
    (Eventually.of_forall fun t => (hc t).aestronglyMeasurable) hint
    (by simpa only [zero_smul, zero_sub] using! hc'.aestronglyMeasurable)
    (Eventually.of_forall fun x t ht => by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      rw [norm_smul, LinearIsometry.norm_map]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg F)
      rw [sub_eq_neg_add]
      apply hbound
      rw [norm_smul, Real.norm_eq_abs]
      have he : ‖unitVector j‖ ≤ (1 : ℝ) := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro k
        simp only [unitVector, Pi.single_apply]
        split_ifs <;> norm_num
      exact (mul_le_mul_of_nonneg_left he (abs_nonneg t)).trans (by linarith))
    (hb.comp_neg.mul_const _) (Eventually.of_forall fun x t _ => hdiff x t)).2
  have horbit (t : ℝ) : T (t • unitVector j) (stationarySchwartzAverage Q ψ F) =
      ∫ x : Vec d, ψ (t • unitVector j - x) • T x F := by
    unfold stationarySchwartzAverage
    change (T (t • unitVector j)).toContinuousLinearMap (∫ x : Vec d, ψ (-x) • T x F) = _
    rw [← (T (t • unitVector j)).toContinuousLinearMap.integral_comp_comm
      (integrable_stationarySchwartzAverage_integrand Q ψ F)]
    simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul]
    dsimp only [T]
    simp_rw [← complexTranslation_add]
    have h := integral_add_right_eq_self (μ := volume)
      (fun x : Vec d => ψ (t • unitVector j - x) • T x F) (t • unitVector j)
    simpa only [show ∀ x : Vec d, t • unitVector j - (x + t • unitVector j) = -x
      from fun x => by abel, T, add_comm] using h
  simp_rw [← horbit] at hd
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  unfold HasComplexHorizontalDerivative
  simpa only [T, zero_add, zero_smul, complexTranslation_zero, ← Complex.ofReal_inv,
    Complex.coe_smul, zero_sub, stationarySchwartzAverage] using! hd

/-- The actual Gaussian evolution commutes with every horizontal translation. -/
theorem complexTranslation_homogeneousGaussianEvolution
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (x : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (homogeneousGaussianEvolution Q i ζ t f) =
      homogeneousGaussianEvolution Q i ζ t
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  by_cases ht : 0 < (t : ℝ)
  · simp only [homogeneousGaussianEvolution_pos Q i ζ t ht]
    rw [complexTranslation_homogeneousAverage]
    unfold homogeneousAverage
    simp_rw [← complexTranslation_add, add_comm x]
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.property)
    simp only [ht0, homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply]

/-- The literal differentiated Schwartz convolutions give the entire horizontal
gradient of each evolved datum, including time zero and arbitrary complex force. -/
theorem hasComplexHorizontalGradient_homogeneousGaussian_schwartz
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (homogeneousGaussianEvolution Q i ζ t (stationarySchwartzAverage Q ψ f))
      (fun j => homogeneousGaussianEvolution Q i ζ t
        (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f)) := by
  intro j
  exact (hasComplexHorizontalDerivative_schwartzAverage_main Q ψ f j).homogeneousGaussianEvolution i ζ t

/-- The actual bilinear pairing consumes this constructed H1 datum with the
literal differentiated Schwartz kernel and the horizontal integration sign. -/
theorem homogeneousGaussian_schwartz_integration_by_parts
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    {v v' : Lp ℂ 2 (reducedLaw Q)}
    (hv : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j v v') :
    Integrable (fun ω =>
      homogeneousGaussianEvolution Q i ζ t
        (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f) ω * v ω) (reducedLaw Q) ∧
    Integrable (fun ω =>
      homogeneousGaussianEvolution Q i ζ t (stationarySchwartzAverage Q ψ f) ω * v' ω)
      (reducedLaw Q) ∧
    (∫ ω, homogeneousGaussianEvolution Q i ζ t
      (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f) ω * v ω ∂reducedLaw Q) =
      -(∫ ω, homogeneousGaussianEvolution Q i ζ t
        (stationarySchwartzAverage Q ψ f) ω * v' ω ∂reducedLaw Q) :=
  complexHorizontalDerivatives_integration_by_parts
    (hasComplexHorizontalGradient_homogeneousGaussian_schwartz Q i ζ ψ f t j) hv

/-- The Euclidean horizontal gradient on the homogeneous comparison leg. -/
def homogeneousGaussianSchwartzGradient (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (ζ : ℂ) (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  WithLp.toLp 2 (fun j => homogeneousGaussianEvolution Q i ζ s.toNNReal
    (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f))

/-- The actual gradient curve is continuous, including both split-time endpoints. -/
theorem continuous_homogeneousGaussianSchwartzGradient
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (homogeneousGaussianSchwartzGradient Q i ζ ψ f) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j =>
    (continuous_homogeneousGaussianEvolution Q i ζ
      (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f)).comp continuous_real_toNNReal)

/-- Full finite-window square integrability is derived, rather than assumed. -/
theorem intervalIntegrable_sq_homogeneousGaussianSchwartzGradient
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ) :
    IntervalIntegrable (fun s => ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f s‖ ^ 2)
      volume a b :=
  ((continuous_homogeneousGaussianSchwartzGradient Q i ζ ψ f).norm.pow 2).intervalIntegrable a b

/-- The actual stationary convolution satisfies the scalar-kernel `L¹` bound. -/
theorem norm_schwartzAverage_main_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ψ : SchwartzMap (Vec d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖stationarySchwartzAverage Q ψ F‖ ≤ (∫ x : Vec d, ‖ψ x‖) * ‖F‖ := by
  calc
    _ ≤ ∫ x : Vec d, ‖ψ (-x) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, LinearIsometry.norm_map]
      rw [integral_mul_const]
      exact congrArg (fun a : ℝ => a * ‖F‖)
        (integral_neg_eq_self (fun x : Vec d => ‖ψ x‖) volume)

/-- The finite-window bound retains the literal Schwartz derivative L1 norms.
The growth coefficient is exactly the adopted structural Gaussian coefficient. -/
theorem integral_sq_homogeneousGaussianSchwartzGradient_le
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ s in a..b, ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f s‖ ^ 2) ≤
      (b-a) * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T / 2)) ^ 2 *
        (∑ j : Fin d, (∫ x : Vec d, ‖(∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ) x‖) ^ 2) * ‖f‖ ^ 2 := by
  let E := Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T / 2)
  have hK : 0 ≤ sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_nonneg (Real.exp_pos _).le (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])
  have hp (s : ℝ) (hs : s ∈ Icc a b) :
      ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f s‖ ^ 2 ≤
        E ^ 2 * (∑ j : Fin d, (∫ x : Vec d,
          ‖(∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ) x‖) ^ 2) * ‖f‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hcoord (j : Fin d) :
        ‖homogeneousGaussianEvolution Q i ζ s.toNNReal
          (stationarySchwartzAverage Q (∂_{unitVector j} ψ) f)‖ ≤
        E * ((∫ x : Vec d, ‖(∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ) x‖) * ‖f‖) := by
      apply ((homogeneousGaussianEvolution Q i ζ s.toNNReal).le_opNorm _).trans
      apply mul_le_mul
      · apply (norm_homogeneousGaussianEvolution_le Q i ζ _).trans
        apply Real.exp_le_exp.mpr
        rw [Real.coe_toNNReal s (ha.trans hs.1)]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hs.2.trans hb) (mul_nonneg hK (sq_nonneg _))) (by norm_num)
      · exact norm_schwartzAverage_main_le Q _ f
      · exact norm_nonneg _
      · exact (Real.exp_pos _).le
    calc
      _ ≤ ∑ j : Fin d, (E * ((∫ x : Vec d,
          ‖(∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ) x‖) * ‖f‖)) ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2
      _ = _ := by simp only [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
  have hi := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_sq_homogeneousGaussianSchwartzGradient Q i ζ ψ f a b)
    intervalIntegrable_const hp
  rw [intervalIntegral.integral_const] at hi
  simpa only [smul_eq_mul, mul_assoc, E] using! hi

/-- The gradient itself belongs to genuine time L2 on every compact window. -/
theorem memLp_homogeneousGaussianSchwartzGradient
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    {a b : ℝ} (hab : a ≤ b) :
    MemLp (homogeneousGaussianSchwartzGradient Q i ζ ψ f) 2
      (volume.restrict (Icc a b)) := by
  letI : SecondCountableTopologyEither ℝ
      (PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :=
    secondCountableTopologyEither_of_left _ _
  have hm := (continuous_homogeneousGaussianSchwartzGradient Q i ζ ψ f).stronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (intervalIntegrable_sq_homogeneousGaussianSchwartzGradient Q i ζ ψ f a b)

/-- The backwards Gaussian comparison leg has square-integrable spatial gradient
all the way to the split endpoints. -/
theorem intervalIntegrable_sq_backward_homogeneousGaussianSchwartzGradient
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (a b T : ℝ) :
    IntervalIntegrable (fun s =>
      ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f (T-s)‖ ^ 2) volume a b :=
  ((((continuous_homogeneousGaussianSchwartzGradient Q i ζ ψ f).comp
    (continuous_const.sub continuous_id)).norm).pow 2).intervalIntegrable a b

/-- Time reversal preserves the finite-window bound with the exact interval length.
Substitute the opposite signed force directly for bilinear comparison. -/
theorem integral_sq_backward_homogeneousGaussianSchwartzGradient_le
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    {a b T : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ s in a..b, ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f (T-s)‖ ^ 2) ≤
      (b-a) * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * T / 2)) ^ 2 *
        (∑ j : Fin d, (∫ x : Vec d, ‖(∂_{unitVector j} ψ : SchwartzMap (Vec d) ℂ) x‖) ^ 2) * ‖f‖ ^ 2 := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun u => ‖homogeneousGaussianSchwartzGradient Q i ζ ψ f u‖ ^ 2) T]
  have h := integral_sq_homogeneousGaussianSchwartzGradient_le Q i ζ ψ f
    (sub_nonneg.mpr hb) (sub_le_sub_left hab T) (sub_le_self T ha)
  simpa only [show T-a-(T-b) = b-a from by ring] using! h

end EinsteinFull
