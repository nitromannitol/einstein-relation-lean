import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Frozen.ReducedLawProbability
import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Correctors.ProbabilityAverageL2
import EinsteinRelation.Correctors.EllipticInverseBounds
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Extend
import EinsteinFull.Work.W3.GaussianConvolutionSupport

/-!
# The actual reduced clock and its finite-range covariance

The reference law is the local pushforward `Q.measure.map reduce`. It is not a
change of density. All local sigma-fields below observe both coefficients and
clock; separation is measured by the explicit Euclidean norm.
-/

open MeasureTheory
open scoped ENNReal symmDiff

namespace EinsteinFull

open EinsteinRelation

private instance reduced_probability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- The literal centered clock at a spatial point. -/
noncomputable def centeredClockField (Q : EnvironmentLaw d Λ₀ r₀)
    (x : Vec d) (ω : FieldPair d) : ℝ :=
  ω.2 x - ∫ ω', ω'.2 0 ∂reducedLaw Q

/-- The actual reduction preserves the joint restriction finite-range property. -/
theorem reducedLaw_hasFiniteRange (Q : EnvironmentLaw d Λ₀ r₀) :
    HasFiniteRange r₀ (reducedLaw Q) :=
  Localization.finiteRange_map_reduce Q.measure Q.finiteRange

/-- Point evaluation agrees exactly with translating the centered origin clock. -/
theorem centeredClockField_eq_translate (Q : EnvironmentLaw d Λ₀ r₀)
    (x : Vec d) (ω : FieldPair d) :
    centeredClockField Q x ω = Clock.centredClock Q (translate x ω) := by
  simp only [centeredClockField, Clock.centredClock, translate_scalar, add_zero]
  rfl

/-- Joint continuity supplies product measurability for later Fubini arguments. -/
theorem continuous_centeredClockField (Q : EnvironmentLaw d Λ₀ r₀) :
    Continuous (fun p : Vec d × FieldPair d => centeredClockField Q p.1 p.2) :=
  (continuous_snd.snd.eval continuous_fst).sub continuous_const

/-- The clock at x is measurable from the actual joint restriction at x. -/
theorem measurable_centeredClockField_local (Q : EnvironmentLaw d Λ₀ r₀)
    {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) :
    Measurable[localSigma U] (centeredClockField Q x) := by
  have hp : Measurable[localSigma U] (fun ω : FieldPair d => (ω.1 x, ω.2 x)) :=
    (comap_measurable _).mono (le_iSup (fun y : U =>
      MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance)
      ⟨x, hx⟩) le_rfl
  exact (measurable_snd.comp hp).sub_const _

/-- Uniform structural boundedness holds at each point under the reduced law. -/
theorem ae_abs_centeredClockField_le (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    ∀ᵐ ω ∂reducedLaw Q, |centeredClockField Q x ω| ≤ 2 * sourceReducedBound Λ₀ := by
  have h := Clock.abs_centredClock_le Q
  have hp : MeasurePreserving (translate x) (reducedLaw Q) (reducedLaw Q) :=
    ⟨Probability.measurable_translate x, reducedLaw_stationary Q x⟩
  filter_upwards [hp.quasiMeasurePreserving.ae h] with ω hω
  rw [centeredClockField_eq_translate]
  exact hω

/-- Integrability is constructed from the structural bound. -/
theorem integrable_centeredClockField (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    Integrable (centeredClockField Q x) (reducedLaw Q) := by
  apply Integrable.of_bound
    ((continuous_centeredClockField Q).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (2 * sourceReducedBound Λ₀)
  simpa only [Real.norm_eq_abs] using! ae_abs_centeredClockField_le Q x

/-- Stationarity keeps the actual clock centered at every spatial point. -/
theorem integral_centeredClockField (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    (∫ ω, centeredClockField Q x ω ∂reducedLaw Q) = 0 := by
  simp_rw [centeredClockField_eq_translate]
  rw [Probability.integral_translate (reducedLaw Q) (reducedLaw_stationary Q) x
    (Clock.centredClock Q) (Clock.continuous_clockAtOrigin.sub continuous_const).measurable]
  exact Clock.integral_centredClock Q

/-- The real bilinear covariance kernel of the actual centered clock. -/
noncomputable def clockCovariance (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d) : ℝ :=
  ∫ ω, centeredClockField Q x ω * centeredClockField Q y ω ∂reducedLaw Q

/-- Products have genuine integrability witnesses before invoking covariance. -/
theorem integrable_centeredClockField_mul (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d) :
    Integrable (fun ω => centeredClockField Q x ω * centeredClockField Q y ω)
      (reducedLaw Q) := by
  apply Integrable.of_bound
    (((continuous_centeredClockField Q).comp
      (continuous_const.prodMk continuous_id)).mul
      ((continuous_centeredClockField Q).comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    ((2 * sourceReducedBound Λ₀) ^ 2)
  filter_upwards [ae_abs_centeredClockField_le Q x, ae_abs_centeredClockField_le Q y]
    with ω hx hy
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, pow_two]
  exact mul_le_mul hx hy (abs_nonneg _) (by positivity [Clock.sourceReducedBound_pos Q.ellipticity_parameter])

/-- Translation invariance of the two-point covariance, with both points shifted. -/
theorem clockCovariance_translate (Q : EnvironmentLaw d Λ₀ r₀) (x y z : Vec d) :
    clockCovariance Q (z + x) (z + y) = clockCovariance Q x y := by
  apply Probability.integral_translate (reducedLaw Q) (reducedLaw_stationary Q) z
    (fun ω => centeredClockField Q x ω * centeredClockField Q y ω)
    (((continuous_centeredClockField Q).comp
      (continuous_const.prodMk continuous_id)).mul
      ((continuous_centeredClockField Q).comp
        (continuous_const.prodMk continuous_id))).measurable

/-- Clock values at strictly Euclidean-separated points are independent. -/
theorem indepFun_centeredClockField (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d)
    (hxy : r₀ < euclideanNorm (x - y)) :
    ProbabilityTheory.IndepFun (centeredClockField Q x) (centeredClockField Q y)
      (reducedLaw Q) := by
  have hi := reducedLaw_hasFiniteRange Q {x} {y} (measurableSet_singleton x)
    (measurableSet_singleton y) ⟨euclideanNorm (x - y), hxy, by
      intro a ha b hb
      simp only [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb, le_refl]⟩
  change ProbabilityTheory.Indep _ _ _
  rw [ProbabilityTheory.Indep_iff] at hi ⊢
  intro s t hs ht
  exact hi s t
    ((measurable_centeredClockField_local Q (Set.mem_singleton x)).comap_le s hs)
    ((measurable_centeredClockField_local Q (Set.mem_singleton y)).comap_le t ht)

/-- Finite range kills the covariance of the actual clock beyond r₀. -/
theorem clockCovariance_eq_zero (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d)
    (hxy : r₀ < euclideanNorm (x - y)) : clockCovariance Q x y = 0 := by
  unfold clockCovariance
  rw [(indepFun_centeredClockField Q x y hxy).integral_fun_mul_eq_mul_integral
    (integrable_centeredClockField Q x).aestronglyMeasurable
    (integrable_centeredClockField Q y).aestronglyMeasurable,
    integral_centeredClockField, zero_mul]

/-- Uniform structural covariance bound, with no additional moment assumption. -/
theorem abs_clockCovariance_le (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d) :
    |clockCovariance Q x y| ≤ (2 * sourceReducedBound Λ₀) ^ 2 := by
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      ‖centeredClockField Q x ω * centeredClockField Q y ω‖ ≤
        (2 * sourceReducedBound Λ₀) ^ 2 := by
    filter_upwards [ae_abs_centeredClockField_le Q x, ae_abs_centeredClockField_le Q y]
      with ω hx hy
    rw [Real.norm_eq_abs, abs_mul, pow_two]
    exact mul_le_mul hx hy (abs_nonneg _)
      (by positivity [Clock.sourceReducedBound_pos Q.ellipticity_parameter])
  simpa only [clockCovariance, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hbound

/-- A single full-measure set bounds the clock simultaneously at all points. -/
theorem ae_forall_abs_centeredClockField_le (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ x, |centeredClockField Q x ω| ≤ 2 * sourceReducedBound Λ₀ := by
  have hs : MeasurableSet {ω : FieldPair d | ∀ x,
      |centeredClockField Q x ω| ≤ 2 * sourceReducedBound Λ₀} := by
    apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_le
      (((continuous_centeredClockField Q).comp
        (continuous_const.prodMk continuous_id)).abs) continuous_const
  apply (ae_map_iff Probability.measurable_reduce.aemeasurable hs).mpr
  have hm : (sourceReducedBound Λ₀)⁻¹ ≤ ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q ∧
      (∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) ≤ sourceReducedBound Λ₀ :=
    reducedClockMean_bounds Q
  have hK := Clock.sourceReducedBound_pos Q.ellipticity_parameter
  filter_upwards [Q.regular] with ω hω
  intro x
  have hc := (sourceReducedBound_support Q.ellipticity_parameter hω).2.2.1 x
  have hcpos := clockDensity_pos ω x
  change |clockDensity ω x - ∫ ω', ω'.2 0 ∂reducedLaw Q| ≤ _
  rw [abs_le]
  constructor <;> linarith [inv_pos.mpr hK]

/-- Pairing the clock with an L1 test uses the ordinary Lebesgue integral. -/
noncomputable def clockTest (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Vec d → ℝ) (ω : FieldPair d) : ℝ :=
  ∫ x, f x * centeredClockField Q x ω

/-- Product-integrability for the actual spatial pairing, built from L1 domination. -/
theorem integrable_clockTest_integrand (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (fun p : FieldPair d × Vec d => f p.2 * centeredClockField Q p.2 p.1)
      ((reducedLaw Q).prod volume) := by
  apply Integrable.mono' ((hf.norm.mul_const (2 * sourceReducedBound Λ₀)).comp_snd
    (reducedLaw Q))
    (((hfm.comp measurable_snd).mul ((continuous_centeredClockField Q).measurable.comp
      measurable_swap)).aestronglyMeasurable)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
    (((hfm.comp measurable_snd).mul
      ((continuous_centeredClockField Q).measurable.comp measurable_swap)).norm)
    ((hfm.norm.comp measurable_snd).mul_const _))).mpr
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  exact Filter.Eventually.of_forall fun x => by
    change ‖f x * centeredClockField Q x ω‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs (centeredClockField Q x ω)]
    exact mul_le_mul_of_nonneg_left (hω x) (norm_nonneg _)

/-- The actual spatial clock pairing is centered. -/
theorem integral_clockTest (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    (∫ ω, clockTest Q f ω ∂reducedLaw Q) = 0 := by
  unfold clockTest
  rw [integral_integral_swap (integrable_clockTest_integrand Q hfm hf)]
  simp only [integral_const_mul, integral_centeredClockField, mul_zero, integral_zero]

/-- The full three-variable product is integrable; no Fubini hypothesis is assumed. -/
theorem integrable_clockTest_pair (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : FieldPair d × (Vec d × Vec d) =>
      (f p.2.1 * centeredClockField Q p.2.1 p.1) *
        (g p.2.2 * centeredClockField Q p.2.2 p.1))
      ((reducedLaw Q).prod (volume.prod volume)) := by
  have hm : Measurable (fun p : FieldPair d × (Vec d × Vec d) =>
      (f p.2.1 * centeredClockField Q p.2.1 p.1) *
        (g p.2.2 * centeredClockField Q p.2.2 p.1)) := by
    exact ((hfm.comp measurable_snd.fst).mul
      ((continuous_centeredClockField Q).measurable.comp
        (measurable_snd.fst.prodMk measurable_fst))).mul
      ((hgm.comp measurable_snd.snd).mul
        ((continuous_centeredClockField Q).measurable.comp
          (measurable_snd.snd.prodMk measurable_fst)))
  apply Integrable.mono'
    (((hf.norm.mul_prod hg.norm).mul_const ((2 * sourceReducedBound Λ₀) ^ 2)).comp_snd
      (reducedLaw Q)) hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le hm.norm (((hfm.norm.comp measurable_snd.fst).mul
      (hgm.norm.comp measurable_snd.snd)).mul_const _))).mpr
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs (centeredClockField Q z.1 ω),
      Real.norm_eq_abs (centeredClockField Q z.2 ω)]
    calc
      _ ≤ (‖f z.1‖ * (2 * sourceReducedBound Λ₀)) *
          (‖g z.2‖ * (2 * sourceReducedBound Λ₀)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (hω z.1) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hω z.2) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (abs_nonneg _))
          (mul_nonneg (norm_nonneg _) (by positivity [Clock.sourceReducedBound_pos Q.ellipticity_parameter]))
      _ = _ := by dsimp only [Function.comp_def, Pi.mul_apply]; ring

/-- Fubini gives the literal bilinear covariance formula for two real L1 tests. -/
theorem integral_clockTest_mul (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ω, clockTest Q f ω * clockTest Q g ω ∂reducedLaw Q) =
      ∫ z : Vec d × Vec d, f z.1 * g z.2 * clockCovariance Q z.1 z.2 := by
  calc
    _ = ∫ ω, ∫ z : Vec d × Vec d,
        (f z.1 * centeredClockField Q z.1 ω) *
          (g z.2 * centeredClockField Q z.2 ω) ∂volume ∂reducedLaw Q := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (integral_prod_mul _ _).symm
    _ = ∫ z : Vec d × Vec d, ∫ ω,
        (f z.1 * centeredClockField Q z.1 ω) *
          (g z.2 * centeredClockField Q z.2 ω) ∂reducedLaw Q :=
      integral_integral_swap (integrable_clockTest_pair Q hfm hgm hf hg)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        unfold clockCovariance
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by ring

/-- Measurability of the genuine covariance kernel, from joint clock measurability. -/
theorem measurable_clockCovariance (Q : EnvironmentLaw d Λ₀ r₀) :
    Measurable (fun z : Vec d × Vec d => clockCovariance Q z.1 z.2) := by
  exact (((continuous_centeredClockField Q).comp
    (continuous_fst.fst.prodMk continuous_snd)).mul
    ((continuous_centeredClockField Q).comp
      (continuous_fst.snd.prodMk continuous_snd))).stronglyMeasurable.integral_prod_right'.measurable

private theorem coordinate_abs_le_euclideanNorm (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

/-- A compact majorant for the Euclidean finite-range covariance.
The coordinate box only bounds its support; it changes no separation hypothesis. -/
noncomputable def clockCovarianceMajorant (d : ℕ) (Λ₀ r₀ : ℝ) (x : Vec d) : ℝ :=
  (Set.Icc (fun _ => -r₀) (fun _ => r₀)).indicator
    (fun _ => (2 * sourceReducedBound Λ₀) ^ 2) x

private theorem measurable_majorant :
    Measurable (clockCovarianceMajorant d Λ₀ r₀) :=
  measurable_const.indicator measurableSet_Icc

private theorem majorant_nonneg (x : Vec d) :
    0 ≤ clockCovarianceMajorant d Λ₀ r₀ x :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

private theorem majorant_neg (x : Vec d) :
    clockCovarianceMajorant d Λ₀ r₀ (-x) = clockCovarianceMajorant d Λ₀ r₀ x := by
  have hx : -x ∈ Set.Icc (fun _ : Fin d => -r₀) (fun _ => r₀) ↔
      x ∈ Set.Icc (fun _ : Fin d => -r₀) (fun _ => r₀) := by
    simp only [Set.mem_Icc, Pi.le_def, Pi.neg_apply]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> intro i <;>
      linarith [ha i, hb i]
  unfold clockCovarianceMajorant
  by_cases h : x ∈ Set.Icc (fun _ : Fin d => -r₀) (fun _ => r₀)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hx.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hx.mp h)]

private theorem integrable_majorant :
    Integrable (clockCovarianceMajorant d Λ₀ r₀) :=
  (integrableOn_const (isCompact_Icc.measure_lt_top.ne)).integrable_indicator measurableSet_Icc

/-- The finite-range covariance is dominated by a fixed compact kernel. -/
theorem abs_clockCovariance_le_majorant (Q : EnvironmentLaw d Λ₀ r₀) (x y : Vec d) :
    |clockCovariance Q x y| ≤ clockCovarianceMajorant d Λ₀ r₀ (x - y) := by
  by_cases h : x - y ∈ Set.Icc (fun _ => -r₀) (fun _ => r₀)
  · simpa only [clockCovarianceMajorant, Set.indicator_of_mem h] using
      abs_clockCovariance_le Q x y
  · have he : r₀ < euclideanNorm (x - y) := by
      by_contra hn
      apply h
      have he := le_of_not_gt hn
      constructor <;> intro i
      · exact by
          have hi := coordinate_abs_le_euclideanNorm (x - y) i
          linarith [neg_le_abs ((x - y) i)]
      · exact (le_abs_self _).trans ((coordinate_abs_le_euclideanNorm (x - y) i).trans he)
    rw [clockCovariance_eq_zero Q x y he, abs_zero,
      clockCovarianceMajorant, Set.indicator_of_notMem h]

private theorem integrable_sq_majorant {f : Vec d → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun x => f x ^ 2)) :
    Integrable (fun z : Vec d × Vec d =>
      f z.1 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) := by
  have hm : Measurable (fun z : Vec d × Vec d =>
      f z.1 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) :=
    ((hfm.comp measurable_fst).pow_const 2).mul
    (measurable_majorant.comp (measurable_fst.sub measurable_snd))
  change Integrable _ ((volume : Measure (Vec d)).prod volume)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x =>
      ((integrable_comp_sub_left (clockCovarianceMajorant d Λ₀ r₀) x).mpr
        integrable_majorant).const_mul (f x ^ 2)
  · have he (x : Vec d) :
        (∫ y, ‖f x ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (x - y)‖) =
          f x ^ 2 * ∫ y, clockCovarianceMajorant d Λ₀ r₀ y := by
      simp_rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (majorant_nonneg _))]
      rw [integral_const_mul, integral_sub_left_eq_self]
    simp_rw [he]
    exact hf2.mul_const _

private theorem integral_sq_majorant {f : Vec d → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun x => f x ^ 2)) :
    (∫ z : Vec d × Vec d, f z.1 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) =
      (∫ x, f x ^ 2) * ∫ y, clockCovarianceMajorant d Λ₀ r₀ y := by
  rw [Measure.volume_eq_prod, integral_prod _ (integrable_sq_majorant (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2)]
  simp_rw [integral_const_mul, integral_sub_left_eq_self]
  exact integral_mul_const _ _

private theorem majorant_sub_swap (x y : Vec d) :
    clockCovarianceMajorant d Λ₀ r₀ (y - x) =
      clockCovarianceMajorant d Λ₀ r₀ (x - y) := by
  rw [← neg_sub x y, majorant_neg]

private theorem integrable_sq_majorant_right {f : Vec d → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun x => f x ^ 2)) :
    Integrable (fun z : Vec d × Vec d =>
      f z.2 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) := by
  have h := (integrable_sq_majorant (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2).swap
  change Integrable (fun z : Vec d × Vec d =>
    f z.2 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.2 - z.1)) (volume.prod volume) at h
  simpa only [majorant_sub_swap] using! h

private theorem integrable_test_covariance (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (fun z : Vec d × Vec d => f z.1 * f z.2 * clockCovariance Q z.1 z.2) := by
  apply Integrable.mono' ((hf.norm.mul_prod hf.norm).mul_const ((2 * sourceReducedBound Λ₀) ^ 2))
    (((hfm.comp measurable_fst).mul (hfm.comp measurable_snd)).mul
      (measurable_clockCovariance Q)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Pi.mul_apply, Pi.mul_apply, Function.comp_apply, norm_mul, norm_mul, Real.norm_eq_abs (clockCovariance Q z.1 z.2)]
    exact mul_le_mul_of_nonneg_left (abs_clockCovariance_le Q z.1 z.2)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The real deterministic-test L2 bound, with a structural constant fixed before
Q and f. L1 is used only to realize the spatial integral; L2 controls its variance. -/
theorem integral_clockTest_sq_le (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x ^ 2)) :
    (∫ ω, clockTest Q f ω ^ 2 ∂reducedLaw Q) ≤
      (∫ y, clockCovarianceMajorant d Λ₀ r₀ y) * ∫ x, f x ^ 2 := by
  have hleft := integrable_sq_majorant (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2
  have hright := integrable_sq_majorant_right (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2
  calc
    _ = ∫ z : Vec d × Vec d, f z.1 * f z.2 * clockCovariance Q z.1 z.2 := by
      simp_rw [pow_two]
      exact integral_clockTest_mul Q hfm hfm hf hf
    _ ≤ ∫ z : Vec d × Vec d,
        (f z.1 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2) +
          f z.2 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) / 2 := by
      apply integral_mono (integrable_test_covariance Q hfm hf) ((hleft.add hright).div_const 2)
      intro z
      calc
        _ ≤ |f z.1 * f z.2 * clockCovariance Q z.1 z.2| := le_abs_self _
        _ ≤ |f z.1 * f z.2| * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2) := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_clockCovariance_le_majorant Q z.1 z.2)
            (abs_nonneg _)
        _ ≤ _ := by
          have hab : |f z.1 * f z.2| ≤ (f z.1 ^ 2 + f z.2 ^ 2) / 2 := by
            rw [abs_mul]
            nlinarith [sq_nonneg (|f z.1| - |f z.2|), sq_abs (f z.1), sq_abs (f z.2)]
          have hm := mul_le_mul_of_nonneg_right hab
            (majorant_nonneg (d := d) (Λ₀ := Λ₀) (r₀ := r₀) (z.1 - z.2))
          dsimp only [Pi.add_apply]
          nlinarith only [hm]
    _ = _ := by
      rw [integral_div, integral_add hleft hright, integral_sq_majorant hfm hf2]
      have hr : (∫ z : Vec d × Vec d,
          f z.2 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2)) =
          (∫ x, f x ^ 2) * ∫ y, clockCovarianceMajorant d Λ₀ r₀ y := by
        rw [Measure.volume_eq_prod, ← integral_prod_swap (μ := (volume : Measure (Vec d)))
          (ν := (volume : Measure (Vec d)))]
        change (∫ z : Vec d × Vec d,
          f z.1 ^ 2 * clockCovarianceMajorant d Λ₀ r₀ (z.2 - z.1) ∂volume.prod volume) = _
        simp_rw [majorant_sub_swap]
        exact integral_sq_majorant hfm hf2
      rw [hr]
      ring

/-- An explicit structural variance constant, independent of the law and test. -/
noncomputable def clockVarianceConstant (d : ℕ) (Λ₀ r₀ : ℝ) : ℝ :=
  (2 * sourceReducedBound Λ₀) ^ 2 * (2 * r₀) ^ d

/-- The compact support majorant has exactly the displayed structural mass. -/
theorem integral_clockCovarianceMajorant (hr₀ : 0 ≤ r₀) :
    (∫ y, clockCovarianceMajorant d Λ₀ r₀ y) = clockVarianceConstant d Λ₀ r₀ := by
  simp only [clockCovarianceMajorant]
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp only [Measure.real, Real.volume_Icc_pi_toReal (show (fun _ : Fin d => -r₀) ≤
    (fun _ => r₀) from fun _ => by linarith), smul_eq_mul]
  simp [clockVarianceConstant, show r₀ - -r₀ = 2 * r₀ by ring, mul_comm]

/-- The second moment estimate with the numerical structural constant. -/
theorem clockTest_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x ^ 2)) :
    (∫ ω, clockTest Q f ω ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ₀ r₀ * ∫ x, f x ^ 2 := by
  simpa only [integral_clockCovarianceMajorant (le_trans zero_le_one Q.range_parameter)]
    using integral_clockTest_sq_le Q hfm hf hf2

/-- The literal spatial pairing represents an L2 random variable. -/
theorem memLp_clockTest (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    MemLp (clockTest Q f) 2 (reducedLaw Q) := by
  have hm : AEStronglyMeasurable (clockTest Q f) (reducedLaw Q) :=
    (integrable_clockTest_integrand Q hfm hf).aestronglyMeasurable.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).mpr
  have h := (integrable_clockTest_pair Q hfm hfm hf hf).integral_prod_left
  have he (ω : FieldPair d) :
      (∫ z : Vec d × Vec d, (f z.1 * centeredClockField Q z.1 ω) *
        (f z.2 * centeredClockField Q z.2 ω) ∂volume.prod volume) =
          clockTest Q f ω ^ 2 := by
    rw [pow_two]
    exact integral_prod_mul (fun x => f x * centeredClockField Q x ω)
      (fun x => f x * centeredClockField Q x ω)
  simpa only [he] using h

/-- The test transferred across a truncated spatial averaging kernel.
The probability measure can be any anisotropic normalized Gaussian measure. -/
noncomputable def truncatedClockTestFunction (ν : Measure (Vec d)) (T : Set (Vec d))
    (f : Vec d → ℝ) (y : Vec d) : ℝ :=
  ∫ s, T.indicator (fun s => f (y + s)) s ∂ν

private theorem measurable_truncated_test_integrand {T : Set (Vec d)}
    (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) :
    Measurable (fun p : Vec d × Vec d => T.indicator (fun s => f (p.1 + s)) p.2) := by
  convert (hfm.comp (measurable_fst.add measurable_snd)).indicator
    (measurable_snd hT) using 1
  funext p
  by_cases hp : p.2 ∈ T <;> simp [Set.indicator, hp]

/-- Smoothing a real test remains measurable, without a continuity premise. -/
theorem measurable_truncatedClockTestFunction (ν : Measure (Vec d)) [SFinite ν]
    {T : Set (Vec d)} (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) :
    Measurable (truncatedClockTestFunction ν T f) :=
  (measurable_truncated_test_integrand hT hfm).stronglyMeasurable.integral_prod_right'.measurable

private theorem integrable_truncated_test_integrand (ν : Measure (Vec d))
    [IsProbabilityMeasure ν] {T : Set (Vec d)} (hT : MeasurableSet T)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (fun p : Vec d × Vec d => T.indicator (fun s => f (p.1 + s)) p.2)
      (volume.prod ν) := by
  apply Integrable.mono' (g := fun p : Vec d × Vec d => |f (p.1 + p.2)|)
    ?_ (measurable_truncated_test_integrand hT hfm).aestronglyMeasurable
    (ae_of_all _ fun p => by
      by_cases hp : p.2 ∈ T <;> simp [hp, Real.norm_eq_abs])
  apply (integrable_prod_iff
    ((hfm.comp (measurable_fst.add measurable_snd)).norm.aestronglyMeasurable).prod_swap).mpr
    ?_ |>.swap
  constructor
  · exact ae_of_all _ fun s =>
      (measurePreserving_add_right volume s).integrable_comp_of_integrable hf.norm
  · change Integrable (fun s => ∫ y, ‖|f (y + s)|‖) ν
    simp_rw [Real.norm_eq_abs, abs_abs]
    have he (s : Vec d) := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
      (fun x => |f x|) s
    simp_rw [he]
    exact integrable_const _

/-- L1 realization of the test transferred across a truncated probability kernel. -/
theorem integrable_truncatedClockTestFunction (ν : Measure (Vec d))
    [IsProbabilityMeasure ν] {T : Set (Vec d)} (hT : MeasurableSet T)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    Integrable (truncatedClockTestFunction ν T f) :=
  (integrable_truncated_test_integrand ν hT hfm hf).integral_prod_left

private theorem integral_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, pow_two]

/-- The same deterministic-test estimate expressed as squared real L2 norms. -/
theorem clockTest_L2_norm_sq_le (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x ^ 2)) :
    (eLpNorm (clockTest Q f) 2 (reducedLaw Q)).toReal ^ 2 ≤
      clockVarianceConstant d Λ₀ r₀ * (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [← integral_sq_eq_eLpNorm_sq (memLp_clockTest Q hfm hf),
    ← integral_sq_eq_eLpNorm_sq
      ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf2)]
  exact clockTest_variance_le Q hfm hf hf2

/-- Truncated probability averaging contracts real spatial L2 energy.
No isotropy, evenness, or choice of Gaussian covariance is imposed. -/
theorem truncatedClockTestFunction_L2 (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {T : Set (Vec d)} (hT : MeasurableSet T) {f : Vec d → ℝ}
    (hfm : Measurable f) (hf2 : Integrable (fun x => f x ^ 2)) :
    MemLp (truncatedClockTestFunction ν T f) 2 volume ∧
      (∫ x, truncatedClockTestFunction ν T f x ^ 2) ≤ ∫ x, f x ^ 2 := by
  have hmem := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf2
  have hb : ∀ᵐ s ∂ν,
      eLpNorm (fun y => T.indicator (fun s => f (y + s)) s) 2 volume ≤
        eLpNorm f 2 volume := ae_of_all _ fun s => by
    by_cases hs : s ∈ T
    · simpa only [Set.indicator_of_mem hs] using!
        (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable
          (measurePreserving_add_right volume s)).le
    · simp only [Set.indicator_of_notMem hs]
      change eLpNorm (0 : Vec d → ℝ) 2 volume ≤ _
      rw [eLpNorm_zero]
      exact zero_le
  have he := Correctors.eLpNorm_probability_integral_le
    ((measurable_truncated_test_integrand hT hfm).aestronglyMeasurable
      (μ := volume.prod ν)) hb
  have hg : MemLp (truncatedClockTestFunction ν T f) 2 volume :=
    he.trans_lt hmem
  refine ⟨hg, ?_⟩
  rw [integral_sq_eq_eLpNorm_sq hg, integral_sq_eq_eLpNorm_sq hmem]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hmem.ne he) 2

/-- The actual clock convolved with a truncated probability averaging kernel. -/
noncomputable def truncatedClockAverage (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) (T : Set (Vec d)) (x : Vec d) (ω : FieldPair d) : ℝ :=
  ∫ s, T.indicator (fun s => centeredClockField Q (x - s) ω) s ∂ν

private theorem integral_truncated_average_transfer (ν : Measure (Vec d))
    [IsProbabilityMeasure ν] {T : Set (Vec d)} (hT : MeasurableSet T)
    {f m : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hmm : Measurable m) {C : ℝ} (hm : ∀ x, |m x| ≤ C) :
    (∫ x, f x * ∫ s, T.indicator (fun s => m (x - s)) s ∂ν) =
      ∫ y, truncatedClockTestFunction ν T f y * m y := by
  have hF : Integrable (fun p : Vec d × Vec d =>
      T.indicator (fun s => f p.1 * m (p.1 - s)) p.2) (volume.prod ν) := by
    have hmeas : Measurable (fun p : Vec d × Vec d =>
        T.indicator (fun s => f p.1 * m (p.1 - s)) p.2) := by
      convert ((hfm.comp measurable_fst).mul
        (hmm.comp (measurable_fst.sub measurable_snd))).indicator
        (measurable_snd hT) using 1
      funext p
      by_cases hp : p.2 ∈ T <;> simp [Set.indicator, hp]
    apply Integrable.mono' ((hf.norm.mul_const C).comp_fst ν) hmeas.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      by_cases hp : p.2 ∈ T
      · simp only [Set.indicator_of_mem hp, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hm _) (abs_nonneg _)
      · simp only [Set.indicator_of_notMem hp, norm_zero]
        exact mul_nonneg (norm_nonneg _) ((abs_nonneg (m 0)).trans (hm 0))
  have hG : Integrable (fun p : Vec d × Vec d =>
      T.indicator (fun s => f (p.1 + s) * m p.1) p.2) (volume.prod ν) := by
    have hmeas : Measurable (fun p : Vec d × Vec d =>
        T.indicator (fun s => f (p.1 + s) * m p.1) p.2) := by
      convert ((hfm.comp (measurable_fst.add measurable_snd)).mul
        (hmm.comp measurable_fst)).indicator (measurable_snd hT) using 1
      funext p
      by_cases hp : p.2 ∈ T <;> simp [Set.indicator, hp]
    apply Integrable.mono'
      ((integrable_truncated_test_integrand ν hT hfm hf).norm.mul_const C)
      hmeas.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      by_cases hp : p.2 ∈ T
      · simp only [Set.indicator_of_mem hp, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hm _) (abs_nonneg _)
      · simp only [Set.indicator_of_notMem hp, norm_zero, zero_mul, le_refl]
  calc
    _ = ∫ x, ∫ s, T.indicator (fun s => f x * m (x - s)) s ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun s => by by_cases hs : s ∈ T <;> simp [hs]
    _ = ∫ s, ∫ x, T.indicator (fun s => f x * m (x - s)) s ∂volume ∂ν :=
      integral_integral_swap hF
    _ = ∫ s, ∫ y, T.indicator (fun s => f (y + s) * m y) s ∂volume ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        by_cases hs : s ∈ T
        · simp only [Set.indicator_of_mem hs]
          simpa only [add_sub_cancel_right] using
            (integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
              (fun x => f x * m (x - s)) s).symm
        · simp only [Set.indicator_of_notMem hs, integral_zero]
    _ = ∫ y, ∫ s, T.indicator (fun s => f (y + s) * m y) s ∂ν :=
      (integral_integral_swap hG).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        dsimp only
        unfold truncatedClockTestFunction
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ fun s => by by_cases hs : s ∈ T <;> simp [hs]

/-- Fubini moves the genuine truncated clock average onto the deterministic test. -/
theorem ae_clockTest_truncatedAverage (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T : Set (Vec d)}
    (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    (fun ω => ∫ x, f x * truncatedClockAverage Q ν T x ω) =ᵐ[reducedLaw Q]
      clockTest Q (truncatedClockTestFunction ν T f) := by
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  exact integral_truncated_average_transfer ν hT hfm hf
    (((continuous_centeredClockField Q).comp
      (continuous_id.prodMk continuous_const)).measurable) hω

/-- The literal smoothed-clock pairing is an actual L2 random variable. -/
theorem memLp_clockTest_truncatedAverage (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T : Set (Vec d)}
    (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    MemLp (fun ω => ∫ x, f x * truncatedClockAverage Q ν T x ω) 2 (reducedLaw Q) :=
  MemLp.ae_eq (ae_clockTest_truncatedAverage Q ν hT hfm hf).symm
    (memLp_clockTest Q (measurable_truncatedClockTestFunction ν hT hfm)
      (integrable_truncatedClockTestFunction ν hT hfm hf))

/-- The actual smoothed clock pairing is centered. -/
theorem integral_clockTest_truncatedAverage (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T : Set (Vec d)}
    (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) :
    (∫ ω, ∫ x, f x * truncatedClockAverage Q ν T x ω ∂volume ∂reducedLaw Q) = 0 := by
  rw [integral_congr_ae (ae_clockTest_truncatedAverage Q ν hT hfm hf)]
  exact integral_clockTest Q (measurable_truncatedClockTestFunction ν hT hfm)
    (integrable_truncatedClockTestFunction ν hT hfm hf)

/-- The genuine truncated local clock block obeys the original test energy bound. -/
theorem clockTest_truncatedAverage_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T : Set (Vec d)}
    (hT : MeasurableSet T) {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hf2 : Integrable (fun x => f x ^ 2)) :
    (∫ ω, (∫ x, f x * truncatedClockAverage Q ν T x ω) ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ₀ r₀ * ∫ x, f x ^ 2 := by
  have he : (∫ ω, (∫ x, f x * truncatedClockAverage Q ν T x ω) ^ 2 ∂reducedLaw Q) =
      ∫ ω, clockTest Q (truncatedClockTestFunction ν T f) ω ^ 2 ∂reducedLaw Q :=
    integral_congr_ae ((ae_clockTest_truncatedAverage Q ν hT hfm hf).mono
      fun _ h => congrArg (fun a : ℝ => a ^ 2) h)
  rw [he]
  exact (clockTest_variance_le Q (measurable_truncatedClockTestFunction ν hT hfm)
    (integrable_truncatedClockTestFunction ν hT hfm hf)
    (truncatedClockTestFunction_L2 ν hT hfm hf2).1.integrable_sq).trans
      (mul_le_mul_of_nonneg_left (truncatedClockTestFunction_L2 ν hT hfm hf2).2
        (mul_nonneg (sq_nonneg _) (pow_nonneg
          (mul_nonneg (by norm_num) (le_trans zero_le_one Q.range_parameter)) _)))

private theorem integrable_bounded_block_test {S : Set (Vec d)} (hS : MeasurableSet S)
    (hSf : volume S < ∞) {f : Vec d → ℝ} (hfm : Measurable f)
    {A : ℝ} (hA : 0 ≤ A) (hfA : ∀ x ∈ S, |f x| ≤ A) :
    Integrable (S.indicator f) ∧ Integrable (fun x => (S.indicator f x) ^ 2) := by
  have hbound : ∀ᵐ x ∂(volume.restrict S), ‖f x‖ ≤ A := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact (Real.norm_eq_abs _).trans_le (hfA x hx)
  have hi := (IntegrableOn.of_bound hSf hfm.aestronglyMeasurable.restrict A hbound).integrable_indicator hS
  refine ⟨hi, ?_⟩
  have hisq : IntegrableOn (fun x => f x ^ 2) S volume := by
    apply IntegrableOn.of_bound hSf (hfm.pow_const 2).aestronglyMeasurable.restrict (A ^ 2)
    filter_upwards [ae_restrict_mem hS] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hA).mpr (hfA x hx)
  convert hisq.integrable_indicator hS using 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx]

/-- A bounded block or boundary strip is controlled by its actual Lebesgue volume.
Taking S to be the cube or the strip supplies the clock block consumers. -/
theorem clockBlock_truncatedAverage_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T S : Set (Vec d)}
    (hT : MeasurableSet T) (hS : MeasurableSet S) (hSf : volume S < ∞)
    {f : Vec d → ℝ} (hfm : Measurable f) {A : ℝ} (hA : 0 ≤ A)
    (hfA : ∀ x ∈ S, |f x| ≤ A) :
    (∫ ω, (∫ x in S, f x * truncatedClockAverage Q ν T x ω) ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ₀ r₀ * A ^ 2 * volume.real S := by
  obtain ⟨hi, hi2⟩ := integrable_bounded_block_test hS hSf hfm hA hfA
  have he (ω : FieldPair d) :
      (∫ x in S, f x * truncatedClockAverage Q ν T x ω) =
        ∫ x, S.indicator f x * truncatedClockAverage Q ν T x ω := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [he]
  apply (clockTest_truncatedAverage_variance_le Q ν hT (hfm.indicator hS) hi hi2).trans
  have hmass : (∫ x, (S.indicator f x) ^ 2) ≤ A ^ 2 * volume.real S := by
    calc
      _ ≤ ∫ x, S.indicator (fun _ => A ^ 2) x := by
        apply integral_mono hi2 ((integrableOn_const hSf.ne).integrable_indicator hS)
        intro x
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hfA x hx) 2
        · simp [hx]
      _ = _ := by rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm]
  have hC : 0 ≤ clockVarianceConstant d Λ₀ r₀ :=
    mul_nonneg (sq_nonneg _) (pow_nonneg
      (mul_nonneg (by norm_num) (le_trans zero_le_one Q.range_parameter)) _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass hC

/-- A spatial density kernel, distinct from any change to the environment law. -/
noncomputable def clockAveragingMeasure (k : Vec d → ℝ) : Measure (Vec d) :=
  volume.withDensity (fun s => ENNReal.ofReal (k s))

/-- Any nonnegative normalized integrable kernel gives a probability measure. -/
theorem clockAveragingMeasure_probability {k : Vec d → ℝ} (hk : Integrable k)
    (hk0 : ∀ s, 0 ≤ k s) (hk1 : (∫ s, k s) = 1) :
    IsProbabilityMeasure (clockAveragingMeasure k) := by
  constructor
  rw [clockAveragingMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ hk0), hk1, ENNReal.ofReal_one]

/-- The probability formulation is literally the truncated density convolution. -/
theorem truncatedClockAverage_eq_kernel (Q : EnvironmentLaw d Λ₀ r₀)
    {k : Vec d → ℝ} (hkm : Measurable k) (hk0 : ∀ s, 0 ≤ k s)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) (ω : FieldPair d) :
    truncatedClockAverage Q (clockAveragingMeasure k) T x ω =
      ∫ s in T, k s * centeredClockField Q (x - s) ω := by
  unfold truncatedClockAverage clockAveragingMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hkm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]
  rw [← integral_indicator hT]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by by_cases hs : s ∈ T <;> simp [hs]

/-- The actual density-convolution block estimate, including truncated Gaussian
kernels with arbitrary covariance. Its bound is uniform in the kernel and scale. -/
theorem clockBlock_kernel_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    {k : Vec d → ℝ} (hkm : Measurable k) (hk : Integrable k)
    (hk0 : ∀ s, 0 ≤ k s) (hk1 : (∫ s, k s) = 1)
    {T S : Set (Vec d)} (hT : MeasurableSet T) (hS : MeasurableSet S)
    (hSf : volume S < ∞) {f : Vec d → ℝ} (hfm : Measurable f)
    {A : ℝ} (hA : 0 ≤ A) (hfA : ∀ x ∈ S, |f x| ≤ A) :
    (∫ ω, (∫ x in S, f x * ∫ s in T, k s * centeredClockField Q (x - s) ω) ^ 2
      ∂reducedLaw Q) ≤ clockVarianceConstant d Λ₀ r₀ * A ^ 2 * volume.real S := by
  letI := clockAveragingMeasure_probability hk hk0 hk1
  have h := clockBlock_truncatedAverage_variance_le Q (clockAveragingMeasure k)
    hT hS hSf hfm hA hfA
  simpa only [truncatedClockAverage_eq_kernel Q hkm hk0 hT] using h

private def clockTestDomain (d : ℕ) : Submodule ℝ (Lp ℝ 2 (volume : Measure (Vec d))) where
  carrier := {f | Integrable (f : Vec d → ℝ) (volume : Measure (Vec d))}
  zero_mem' := (integrable_zero (Vec d) ℝ volume).congr (Lp.coeFn_zero ℝ 2 volume).symm
  add_mem' := by
    intro f g hf hg
    exact (hf.add hg).congr (Lp.coeFn_add f g).symm
  smul_mem' := by
    intro c f hf
    exact (hf.smul c).congr (Lp.coeFn_smul c f).symm

private theorem clockTestDomain_dense :
    DenseRange (clockTestDomain d).subtype := by
  apply (Lp.simpleFunc.denseRange (E := ℝ) (μ := (volume : Measure (Vec d)))
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mono
  rintro _ ⟨f, rfl⟩
  refine ⟨⟨f, ?_⟩, rfl⟩
  exact ((SimpleFunc.memLp_iff_integrable (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp (Lp.simpleFunc.memLp f)).congr
      (Lp.simpleFunc.toSimpleFunc_eq_toFun f)

private theorem clockTest_congr (Q : EnvironmentLaw d Λ₀ r₀)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume] g) : clockTest Q f = clockTest Q g := by
  funext ω
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

private noncomputable def clockTestDomainMap (Q : EnvironmentLaw d Λ₀ r₀) :
    clockTestDomain d →ₗ[ℝ] Lp ℝ 2 (reducedLaw Q) where
  toFun f := (memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable f.property).toLp
    (clockTest Q f.val)
  map_add' f g := by
    apply Lp.ext
    have hfg := clockTest_congr Q (Lp.coeFn_add f.val g.val)
    filter_upwards [(memLp_clockTest Q (Lp.stronglyMeasurable (f + g).val).measurable
      (f + g).property).coeFn_toLp,
      (memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable f.property).coeFn_toLp,
      (memLp_clockTest Q (Lp.stronglyMeasurable g.val).measurable g.property).coeFn_toLp,
      Lp.coeFn_add
        ((memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable f.property).toLp _)
        ((memLp_clockTest Q (Lp.stronglyMeasurable g.val).measurable g.property).toLp _),
      (integrable_clockTest_integrand Q (Lp.stronglyMeasurable f.val).measurable
        f.property).prod_right_ae,
      (integrable_clockTest_integrand Q (Lp.stronglyMeasurable g.val).measurable
        g.property).prod_right_ae] with ω hsum hf hg hadd hfi hgi
    rw [hsum, hadd]
    dsimp only [Pi.add_apply]
    rw [hf, hg]
    change clockTest Q (↑(f.val + g.val)) ω = _
    rw [hfg]
    simpa only [clockTest, Pi.add_apply, add_mul] using integral_add hfi hgi
  map_smul' c f := by
    apply Lp.ext
    have hcf := clockTest_congr Q (Lp.coeFn_smul c f.val)
    filter_upwards [(memLp_clockTest Q (Lp.stronglyMeasurable (c • f).val).measurable
      (c • f).property).coeFn_toLp,
      (memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable f.property).coeFn_toLp,
      Lp.coeFn_smul c
        ((memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable f.property).toLp _)]
      with ω hsmul hf hcoe
    simp only [RingHom.id_apply]
    rw [hsmul, hcoe]
    dsimp only [Pi.smul_apply]
    rw [hf]
    change clockTest Q (↑(c • f.val)) ω = _
    rw [hcf]
    simp only [clockTest, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem clockVarianceConstant_nonneg (Q : EnvironmentLaw d Λ₀ r₀) :
    0 ≤ clockVarianceConstant d Λ₀ r₀ := by
  unfold clockVarianceConstant
  positivity [le_trans zero_le_one Q.range_parameter]

private theorem clockTestDomainMap_bound (Q : EnvironmentLaw d Λ₀ r₀)
    (f : clockTestDomain d) :
    ‖clockTestDomainMap Q f‖ ≤ Real.sqrt (clockVarianceConstant d Λ₀ r₀) * ‖f.val‖ := by
  have h := clockTest_L2_norm_sq_le Q (Lp.stronglyMeasurable f.val).measurable f.property
    ((memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable f.val)).mp (Lp.memLp f.val))
  change ‖(memLp_clockTest Q (Lp.stronglyMeasurable f.val).measurable
    f.property).toLp (clockTest Q f.val)‖ ≤ _
  rw [Lp.norm_toLp]
  rw [Lp.norm_def]
  have hs := Real.sq_sqrt (clockVarianceConstant_nonneg Q)
  apply (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg)).mp
  simpa only [mul_pow, hs] using h

/-- The mean-square clock pairing on every real spatial L2 test. This is the
continuous extension of the literal integral on L1 ∩ L2, under the reduced law. -/
noncomputable def clockTestL2 (Q : EnvironmentLaw d Λ₀ r₀) :
    Lp ℝ 2 (volume : Measure (Vec d)) →L[ℝ] Lp ℝ 2 (reducedLaw Q) :=
  (clockTestDomainMap Q).extendOfNorm (clockTestDomain d).subtype

/-- Agreement of the mean-square pairing with the ordinary pairing whenever
both the spatial L1 and L2 integrability conditions hold. -/
theorem clockTestL2_toLp (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : Integrable f) (hf2 : MemLp f 2 volume) :
    clockTestL2 Q (hf2.toLp f) = (memLp_clockTest Q hfm hf).toLp (clockTest Q f) := by
  let g : clockTestDomain d := ⟨hf2.toLp f, hf.congr hf2.coeFn_toLp.symm⟩
  have he := LinearMap.extendOfNorm_eq clockTestDomain_dense
    ⟨_, clockTestDomainMap_bound Q⟩ g
  change clockTestL2 Q (hf2.toLp f) = clockTestDomainMap Q g at he
  rw [he]
  apply Lp.ext
  filter_upwards [(memLp_clockTest Q (Lp.stronglyMeasurable g.val).measurable
    g.property).coeFn_toLp, (memLp_clockTest Q hfm hf).coeFn_toLp] with ω hg hff
  change (memLp_clockTest Q (Lp.stronglyMeasurable g.val).measurable
    g.property).toLp (clockTest Q g.val) ω = _
  rw [hg, hff, clockTest_congr Q hf2.coeFn_toLp]

/-- The structural operator bound is independent of the environment law and test. -/
theorem norm_clockTestL2_le (Q : EnvironmentLaw d Λ₀ r₀) :
    ‖clockTestL2 Q‖ ≤ Real.sqrt (clockVarianceConstant d Λ₀ r₀) :=
  LinearMap.opNorm_extendOfNorm_le clockTestDomain_dense (Real.sqrt_nonneg _)
    (clockTestDomainMap_bound Q)

/-- The finite-range second-moment bound holds for every real L2 test. -/
theorem clockTestL2_norm_sq_le (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    ‖clockTestL2 Q f‖ ^ 2 ≤ clockVarianceConstant d Λ₀ r₀ * ‖f‖ ^ 2 := by
  have h := (clockTestL2 Q).le_of_opNorm_le (norm_clockTestL2_le Q) f
  have hs := Real.sq_sqrt (clockVarianceConstant_nonneg Q)
  calc
    _ ≤ (Real.sqrt (clockVarianceConstant d Λ₀ r₀) * ‖f‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [mul_pow, hs]

/-- Centering is preserved by the mean-square extension to arbitrary L2 tests. -/
theorem integral_clockTestL2 (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    (∫ ω, clockTestL2 Q f ω ∂reducedLaw Q) = 0 := by
  let one : Lp ℝ 2 (reducedLaw Q) := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have he (g : Lp ℝ 2 (reducedLaw Q)) :
      (∫ ω, g ω ∂reducedLaw Q) = inner ℝ one g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (1 : ℝ) (p := (2 : ℝ≥0∞))
      (μ := reducedLaw Q)).coeFn_toLp] with ω hω
    simp only [one] at hω ⊢
    rw [hω]
    simp only [RCLike.inner_apply, conj_trivial, mul_one]
  have hc : Continuous (fun f : Lp ℝ 2 (volume : Measure (Vec d)) =>
      ∫ ω, clockTestL2 Q f ω ∂reducedLaw Q) := by
    simp_rw [he]
    exact continuous_inner.comp (continuous_const.prodMk (clockTestL2 Q).continuous)
  refine (clockTestDomain_dense (d := d)).induction_on
    (p := fun f => (∫ ω, clockTestL2 Q f ω ∂reducedLaw Q) = 0)
    f (isClosed_eq hc continuous_const) ?_
  intro g
  have hg := clockTestL2_toLp Q (Lp.stronglyMeasurable g.val).measurable
    g.property (Lp.memLp g.val)
  rw [Lp.toLp_coeFn] at hg
  change (∫ ω, clockTestL2 Q g.val ω ∂reducedLaw Q) = 0
  rw [hg, integral_congr_ae (memLp_clockTest Q (Lp.stronglyMeasurable g.val).measurable
    g.property).coeFn_toLp]
  exact integral_clockTest Q (Lp.stronglyMeasurable g.val).measurable g.property

/-- Specialization to the literal Gaussian with arbitrary positive-definite
covariance `s A`. The structural constant is independent of A, s, and truncation. -/
theorem clockBlock_anisotropicGaussian_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s)
    {T S : Set (Vec d)} (hT : MeasurableSet T) (hS : MeasurableSet S)
    (hSf : volume S < ∞) {f : Vec d → ℝ} (hfm : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x ∈ S, |f x| ≤ B) :
    (∫ ω, (∫ x in S, f x * ∫ y in T,
      anisotropicGaussian A s y * centeredClockField Q (x - y) ω) ^ 2 ∂reducedLaw Q) ≤
        clockVarianceConstant d Λ₀ r₀ * B ^ 2 * volume.real S := by
  apply clockBlock_kernel_variance_le Q
    (contDiff_anisotropicGaussian A s).continuous.measurable
    (integrable_anisotropicGaussian A hA s hs) _
    (integral_anisotropicGaussian A hA s hs) hT hS hSf hfm hB hfB
  intro y
  unfold anisotropicGaussian
  positivity

/-- Finite range makes the covariance integrable against any real L2 test on
both coordinates, even when the test is not spatially L1. -/
theorem integrable_clockCovariance_test_of_memLp (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    Integrable (fun z : Vec d × Vec d => f z.1 * f z.2 * clockCovariance Q z.1 z.2) := by
  have hf2 := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hf
  apply Integrable.mono'
    (((integrable_sq_majorant (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2).add
      (integrable_sq_majorant_right (Λ₀ := Λ₀) (r₀ := r₀) hfm hf2)).div_const 2)
    (((hfm.comp measurable_fst).mul (hfm.comp measurable_snd)).mul
      (measurable_clockCovariance Q)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖f z.1 * f z.2 * clockCovariance Q z.1 z.2‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |f z.1 * f z.2| * clockCovarianceMajorant d Λ₀ r₀ (z.1 - z.2) :=
        mul_le_mul_of_nonneg_left (abs_clockCovariance_le_majorant Q z.1 z.2) (abs_nonneg _)
      _ ≤ _ := by
        have hab : |f z.1 * f z.2| ≤ (f z.1 ^ 2 + f z.2 ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|f z.1| - |f z.2|), sq_abs (f z.1), sq_abs (f z.2)]
        have hm := mul_le_mul_of_nonneg_right hab
          (majorant_nonneg (d := d) (Λ₀ := Λ₀) (r₀ := r₀) (z.1 - z.2))
        dsimp only [Pi.div_apply, Pi.add_apply]
        nlinarith only [hm]

/-- The full covariance identity for the mean-square pairing on arbitrary real
spatial L2 tests. The double integral is an actual absolutely integrable function. -/
theorem clockTestL2_norm_sq_eq_covariance (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    ‖clockTestL2 Q f‖ ^ 2 =
      ∫ z : Vec d × Vec d, f z.1 * f z.2 * clockCovariance Q z.1 z.2 := by
  let fm := (Lp.stronglyMeasurable f).measurable
  let fn (n : ℕ) : SimpleFunc (Vec d) ℝ :=
    SimpleFunc.approxOn f fm (Set.range f ∪ {0}) 0 (by simp) n
  have hfn2 (n : ℕ) : MemLp (fn n) 2 volume :=
    SimpleFunc.memLp_approxOn_range fm (Lp.memLp f) n
  have hfn1 (n : ℕ) : Integrable (fn n) :=
    (SimpleFunc.memLp_iff_integrable (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp (hfn2 n)
  have ht : Filter.Tendsto (fun n => (hfn2 n).toLp (fn n)) Filter.atTop (nhds f) := by
    simpa only [Lp.toLp_coeFn] using
      SimpleFunc.tendsto_approxOn_range_Lp (by norm_num : (2 : ℝ≥0∞) ≠ ∞) fm (Lp.memLp f)
  have hleft := (((clockTestL2 Q).continuous.tendsto f).comp ht).norm.pow 2
  have hright : Filter.Tendsto
      (fun n => ∫ z : Vec d × Vec d, fn n z.1 * fn n z.2 * clockCovariance Q z.1 z.2)
      Filter.atTop
      (nhds (∫ z : Vec d × Vec d, f z.1 * f z.2 * clockCovariance Q z.1 z.2)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun z : Vec d × Vec d => 4 * ‖f z.1 * f z.2 * clockCovariance Q z.1 z.2‖)
    · intro n
      exact (((fn n).measurable.comp measurable_fst).mul
        ((fn n).measurable.comp measurable_snd)).mul
          (measurable_clockCovariance Q) |>.aestronglyMeasurable
    · exact (integrable_clockCovariance_test_of_memLp Q fm (Lp.memLp f)).norm.const_mul 4
    · intro n
      exact ae_of_all _ fun z => by
        have h1 := SimpleFunc.norm_approxOn_zero_le fm (by simp : (0 : ℝ) ∈ Set.range f ∪ {0})
          z.1 n
        have h2 := SimpleFunc.norm_approxOn_zero_le fm (by simp : (0 : ℝ) ∈ Set.range f ∪ {0})
          z.2 n
        change ‖fn n z.1 * fn n z.2 * clockCovariance Q z.1 z.2‖ ≤ _
        calc
          _ ≤ (‖f z.1‖ + ‖f z.1‖) * (‖f z.2‖ + ‖f z.2‖) *
              ‖clockCovariance Q z.1 z.2‖ := by
            rw [norm_mul, norm_mul]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (norm_nonneg _)
          _ = _ := by rw [norm_mul, norm_mul]; ring
    · exact ae_of_all _ fun z => by
        have ht (x : Vec d) : Filter.Tendsto (fun n => fn n x) Filter.atTop (nhds (f x)) :=
          SimpleFunc.tendsto_approxOn fm (by simp) (subset_closure (by simp))
        exact ((ht z.1).mul (ht z.2)).mul_const _
  have he (n : ℕ) : ‖clockTestL2 Q ((hfn2 n).toLp (fn n))‖ ^ 2 =
      ∫ z : Vec d × Vec d, fn n z.1 * fn n z.2 * clockCovariance Q z.1 z.2 := by
    rw [clockTestL2_toLp Q (fn n).measurable (hfn1 n) (hfn2 n), Lp.norm_toLp,
      ← integral_sq_eq_eLpNorm_sq (memLp_clockTest Q (fn n).measurable (hfn1 n))]
    simp_rw [pow_two]
    exact integral_clockTest_mul Q (fn n).measurable (fn n).measurable (hfn1 n) (hfn1 n)
  exact tendsto_nhds_unique hleft (by simpa only [Function.comp_apply, he] using hright)

/-- The source cube Q_L(x) = x + (-L/2,L/2)^d in the coordinate carrier. -/
def clockBlockCube (x : Vec d) (L : ℝ) : Set (Vec d) :=
  Set.pi Set.univ (fun j => Set.Ioo (x j - L / 2) (x j + L / 2))

/-- The source open cube is Lebesgue measurable. -/
theorem measurableSet_clockBlockCube (x : Vec d) (L : ℝ) :
    MeasurableSet (clockBlockCube x L) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

/-- The source cube has its usual, unnormalized Lebesgue volume. -/
theorem volume_clockBlockCube (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    volume (clockBlockCube x L) = ENNReal.ofReal (L ^ d) := by
  unfold clockBlockCube
  rw [Real.volume_pi_Ioo]
  simp_rw [show ∀ j : Fin d, (x j + L / 2) - (x j - L / 2) = L by intro j; ring]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hL]

/-- The real-valued volume is also exact, including dimension zero. -/
theorem volumeReal_clockBlockCube (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    volume.real (clockBlockCube x L) = L ^ d := by
  rw [Measure.real, volume_clockBlockCube x hL, ENNReal.toReal_ofReal (pow_nonneg hL d)]

private theorem clockBlockCube_mono (x : Vec d) {a b : ℝ} (hab : a ≤ b) :
    clockBlockCube x a ⊆ clockBlockCube x b := by
  intro y hy j hj
  have h := hy j hj
  constructor <;> linarith [h.1, h.2]

/-- The boundary-strip volume gives the source surface-area times width bound. -/
theorem volumeReal_clockBlockCube_strip_le (x : Vec d) {L w : ℝ}
    (hw : 0 ≤ w) (hwL : w ≤ L) :
    volume.real (clockBlockCube x L \ clockBlockCube x (L - w)) ≤
      d * L ^ (d - 1) * w := by
  have hL := hw.trans hwL
  rw [measureReal_diff (clockBlockCube_mono x (sub_le_self L hw))
      (measurableSet_clockBlockCube x (L - w))
      (by rw [volume_clockBlockCube x hL]; exact ENNReal.ofReal_ne_top),
    volumeReal_clockBlockCube x hL, volumeReal_clockBlockCube x (sub_nonneg.mpr hwL)]
  calc
    _ ≤ |L ^ d - (L - w) ^ d| := le_abs_self _
    _ ≤ |L - (L - w)| * d * max |L| |L - w| ^ (d - 1) := abs_pow_sub_pow_le ..
    _ = _ := by
      rw [abs_of_nonneg hL, abs_of_nonneg (sub_nonneg.mpr hwL),
        max_eq_left (sub_le_self L hw), show L - (L - w) = w by ring, abs_of_nonneg hw]
      ring

/-- The actual anisotropic Gaussian clock block has CLT-order variance L^d,
uniformly in the smoothing scale and its measurable truncation. -/
theorem clockCube_anisotropicGaussian_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) {L : ℝ} (hL : 0 ≤ L)
    {f : Vec d → ℝ} (hfm : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ y ∈ clockBlockCube x L, |f y| ≤ B) :
    (∫ ω, (∫ y in clockBlockCube x L, f y * ∫ z in T,
      anisotropicGaussian A s z * centeredClockField Q (y - z) ω) ^ 2 ∂reducedLaw Q) ≤
        clockVarianceConstant d Λ₀ r₀ * B ^ 2 * L ^ d := by
  have h := clockBlock_anisotropicGaussian_variance_le Q A hA s hs hT
    (measurableSet_clockBlockCube x L)
    (by rw [volume_clockBlockCube x hL]; exact ENNReal.ofReal_lt_top) hfm hB hfB
  simpa only [volumeReal_clockBlockCube x hL] using h

/-- The genuine clock block over a source boundary strip has variance bounded
by its surface-area times width, with no restriction on Gaussian anisotropy. -/
theorem clockCube_strip_anisotropicGaussian_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (A : Mat d) (hA : A.PosDef) (s : ℝ) (hs : 0 < s)
    {T : Set (Vec d)} (hT : MeasurableSet T) (x : Vec d) {L w : ℝ}
    (hw : 0 ≤ w) (hwL : w ≤ L) {f : Vec d → ℝ} (hfm : Measurable f)
    {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ y ∈ clockBlockCube x L \ clockBlockCube x (L - w), |f y| ≤ B) :
    (∫ ω, (∫ y in clockBlockCube x L \ clockBlockCube x (L - w), f y * ∫ z in T,
      anisotropicGaussian A s z * centeredClockField Q (y - z) ω) ^ 2 ∂reducedLaw Q) ≤
        clockVarianceConstant d Λ₀ r₀ * B ^ 2 * (d * L ^ (d - 1) * w) := by
  have hL := hw.trans hwL
  have h := clockBlock_anisotropicGaussian_variance_le Q A hA s hs hT
    ((measurableSet_clockBlockCube x L).diff (measurableSet_clockBlockCube x (L - w)))
    (lt_of_le_of_lt (measure_mono Set.diff_subset)
      (by rw [volume_clockBlockCube x hL]; exact ENNReal.ofReal_lt_top)) hfm hB hfB
  exact h.trans (mul_le_mul_of_nonneg_left (volumeReal_clockBlockCube_strip_le x hw hwL)
    (mul_nonneg (clockVarianceConstant_nonneg Q) (sq_nonneg _)))

/-- The source second-moment identity in iterated Lebesgue-integral notation,
with the stochastic integral interpreted by its mean-square extension. -/
theorem integral_clockTestL2_sq_eq_covariance (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    (∫ ω, clockTestL2 Q f ω ^ 2 ∂reducedLaw Q) =
      ∫ x, ∫ y, f x * f y * clockCovariance Q x y := by
  rw [integral_sq_eq_eLpNorm_sq (Lp.memLp (clockTestL2 Q f)),
    ← Lp.norm_def, clockTestL2_norm_sq_eq_covariance Q f, Measure.volume_eq_prod]
  exact integral_prod _ (integrable_clockCovariance_test_of_memLp Q
    (Lp.stronglyMeasurable f).measurable (Lp.memLp f))

/-- The complete real L2 deterministic-test estimate in second-moment notation. -/
theorem integral_clockTestL2_sq_le (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    (∫ ω, clockTestL2 Q f ω ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ₀ r₀ * ∫ x, f x ^ 2 := by
  rw [integral_sq_eq_eLpNorm_sq (Lp.memLp (clockTestL2 Q f)),
    integral_sq_eq_eLpNorm_sq (Lp.memLp f), ← Lp.norm_def, ← Lp.norm_def]
  exact clockTestL2_norm_sq_le Q f

/-- The cube consumer using the actual homogenized coefficient and a positive
spatial scale r, with covariance r² times that full anisotropic matrix. -/
theorem clockCube_homogenizedGaussian_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    {r : ℝ} (hr : 0 < r) {T : Set (Vec d)} (hT : MeasurableSet T)
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) {f : Vec d → ℝ} (hfm : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ y ∈ clockBlockCube x L, |f y| ≤ B) :
    (∫ ω, (∫ y in clockBlockCube x L, f y * ∫ z in T,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        centeredClockField Q (y - z) ω) ^ 2 ∂reducedLaw Q) ≤
        clockVarianceConstant d Λ₀ r₀ * B ^ 2 * L ^ d :=
  clockCube_anisotropicGaussian_variance_le Q (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) (r ^ 2) (sq_pos_of_pos hr) hT x hL hfm hB hfB

/-- Translating a cube changes at most a surface-area times displacement
volume. The coordinate bound is used only for this deterministic geometry. -/
theorem volumeReal_clockBlockCube_symmDiff_le (x z : Vec d) {L a : ℝ}
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hz : ∀ j, |z j| ≤ a) :
    volume.real (clockBlockCube x L ∆ clockBlockCube (x - z) L) ≤
      4 * d * L ^ (d - 1) * a := by
  classical
  have hm := measurableSet_clockBlockCube x L
  have hn := measurableSet_clockBlockCube (x - z) L
  have hf : volume (clockBlockCube x L) ≠ ∞ := by
    rw [volume_clockBlockCube x hL]; exact ENNReal.ofReal_ne_top
  have hg : volume (clockBlockCube (x - z) L) ≠ ∞ := by
    rw [volume_clockBlockCube (x - z) hL]; exact ENNReal.ofReal_ne_top
  have heq : volume.real (clockBlockCube x L \ clockBlockCube (x - z) L) =
      volume.real (clockBlockCube (x - z) L \ clockBlockCube x L) := by
    have h₁ := measureReal_diff_add_inter (μ := volume)
      (s := clockBlockCube x L) hn hf
    have h₂ := measureReal_diff_add_inter (μ := volume)
      (s := clockBlockCube (x - z) L) hm hg
    rw [Set.inter_comm, volumeReal_clockBlockCube (x - z) hL] at h₂
    rw [volumeReal_clockBlockCube x hL] at h₁
    linarith
  rw [measureReal_symmDiff_eq hm hn hf hg, ← heq]
  by_cases hsmall : 2 * a ≤ L
  · have hsub : clockBlockCube x (L - 2 * a) ⊆ clockBlockCube (x - z) L := by
      intro y hy j hj
      have hyj := hy j hj
      have hzj := abs_le.mp (hz j)
      change x j - z j - L / 2 < y j ∧ y j < x j - z j + L / 2
      constructor <;> linarith [hyj.1, hyj.2, hzj.1, hzj.2]
    have hbound : volume.real (clockBlockCube x L \ clockBlockCube (x - z) L) ≤
        d * L ^ (d - 1) * (2 * a) := by
      apply (measureReal_mono (Set.diff_subset_diff_right hsub)
        (measure_ne_top_of_subset Set.diff_subset hf)).trans
      exact volumeReal_clockBlockCube_strip_le x (by positivity) hsmall
    linarith
  · have hbound : volume.real (clockBlockCube x L \ clockBlockCube (x - z) L) ≤ L ^ d := by
      simpa only [volumeReal_clockBlockCube x hL] using measureReal_mono Set.diff_subset hf
    cases d with
    | zero =>
      have hempty : clockBlockCube x L = Set.univ := by
        ext y; simp [clockBlockCube, Set.mem_pi]
      have hempty' : clockBlockCube (x - z) L = Set.univ := by
        ext y; simp [clockBlockCube, Set.mem_pi]
      rw [hempty, hempty']
      simp
    | succ n =>
      have hpow : 0 ≤ L ^ n := pow_nonneg hL _
      have hn : (1 : ℝ) ≤ n + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
      have hLa : L ≤ 2 * a := (lt_of_not_ge hsmall).le
      have hmul := mul_le_mul_of_nonneg_left hLa hpow
      simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ] at *
      nlinarith [mul_nonneg hpow ha]

/-- A translation error of the cube indicator has exactly symmetric-difference
L2 energy, bounded in terms of the sum of coordinate displacements. -/
theorem clockBlockCube_indicator_shift_L2_le (x z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (eLpNorm (fun y => (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) (y + z) -
      (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) 2 volume) ^ 2 ≤
        ENNReal.ofReal (4 * d * L ^ (d - 1) * ∑ j, |z j|) := by
  have hshift (y : Vec d) : y + z ∈ clockBlockCube x L ↔
      y ∈ clockBlockCube (x - z) L := by
    constructor <;> intro hy j hj
    · have h := hy j hj
      change x j - z j - L / 2 < y j ∧ y j < x j - z j + L / 2
      change x j - L / 2 < y j + z j ∧ y j + z j < x j + L / 2 at h
      constructor <;> linarith [h.1, h.2]
    · have h := hy j hj
      change x j - L / 2 < y j + z j ∧ y j + z j < x j + L / 2
      change x j - z j - L / 2 < y j ∧ y j < x j - z j + L / 2 at h
      constructor <;> linarith [h.1, h.2]
  have he (y : Vec d) :
      ‖(clockBlockCube x L).indicator (fun _ => (1 : ℝ)) (y + z) -
        (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y‖ₑ ^ 2 =
      (clockBlockCube x L ∆ clockBlockCube (x - z) L).indicator
        (fun _ => (1 : ℝ≥0∞)) y := by
    by_cases hy : y ∈ clockBlockCube x L <;>
      by_cases hz : y ∈ clockBlockCube (x - z) L <;>
      simp [Set.mem_symmDiff, hy, hz, hshift, ← ofReal_norm_eq_enorm]
  have hfm : Measurable ((clockBlockCube x L).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_clockBlockCube x L)
  rw [Correctors.eLpNorm_two_sq
    (fun y => (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) (y + z) -
      (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) volume
    ((hfm.comp (measurable_id.fun_add (measurable_const (a := z)))).fun_sub hfm).aestronglyMeasurable]
  simp_rw [he]
  rw [lintegral_indicator ((measurableSet_clockBlockCube x L).symmDiff
    (measurableSet_clockBlockCube (x - z) L)), lintegral_one, Measure.restrict_apply_univ]
  have hf : volume (clockBlockCube x L ∆ clockBlockCube (x - z) L) ≠ ∞ :=
    measure_ne_top_of_subset Set.symmDiff_subset_union
      (measure_union_ne_top (by rw [volume_clockBlockCube x hL]; finiteness)
        (by rw [volume_clockBlockCube (x - z) hL]; finiteness))
  rw [← ENNReal.ofReal_toReal hf]
  exact ENNReal.ofReal_le_ofReal (volumeReal_clockBlockCube_symmDiff_le x z hL
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) (fun j =>
      Finset.single_le_sum (fun k _ => abs_nonneg (z k)) (Finset.mem_univ j)))

/-- Jensen and Tonelli turn the actual displacement moment of a probability
kernel into the cube's spatial L2 smoothing error. No symmetry is required. -/
theorem clockBlockCube_average_sub_L2_le (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (eLpNorm (fun y => truncatedClockTestFunction ν Set.univ
      ((clockBlockCube x L).indicator (fun _ => (1 : ℝ))) y -
        (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) 2 volume) ^ 2 ≤
      ∫⁻ z, ENNReal.ofReal (4 * d * L ^ (d - 1) * ∑ j, |z j|) ∂ν := by
  let f := (clockBlockCube x L).indicator (fun _ => (1 : ℝ))
  have hfm : Measurable f := measurable_const.indicator (measurableSet_clockBlockCube x L)
  have hF : Measurable (fun p : Vec d × Vec d => f (p.1 + p.2) - f p.1) :=
    (hfm.comp (measurable_fst.fun_add measurable_snd)).fun_sub (hfm.comp measurable_fst)
  have hfi (y : Vec d) : Integrable (fun z => f (y + z)) ν := by
    apply Integrable.of_bound (hfm.comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      by_cases hz : y + z ∈ clockBlockCube x L <;> simp [f, hz]
  have he (y : Vec d) : truncatedClockTestFunction ν Set.univ f y - f y =
      ∫ z, f (y + z) - f y ∂ν := by
    rw [integral_sub (hfi y) (integrable_const _), integral_const]
    simp [truncatedClockTestFunction]
  change (eLpNorm (fun y => truncatedClockTestFunction ν Set.univ f y - f y) 2 volume) ^ 2 ≤ _
  simp_rw [he]
  rw [Correctors.eLpNorm_two_sq (fun y => ∫ z, f (y + z) - f y ∂ν) volume
    (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable]
  calc
    _ ≤ ∫⁻ y, ∫⁻ z, ‖f (y + z) - f y‖ₑ ^ 2 ∂ν := by
      apply lintegral_mono
      intro y
      have hm : AEStronglyMeasurable (fun z => f (y + z) - f y) ν :=
        ((hfm.comp ((measurable_const (a := y)).fun_add measurable_id)).fun_sub
          (measurable_const (a := f y))).aestronglyMeasurable
      exact (pow_le_pow_left' (Correctors.enorm_integral_le_eLpNorm (p := 2)
        (by norm_num) hm) 2).trans_eq (Correctors.eLpNorm_two_sq _ _ hm)
    _ = ∫⁻ z, (eLpNorm (fun y => f (y + z) - f y) 2 volume) ^ 2 ∂ν := by
      rw [lintegral_lintegral_swap (hF.enorm.pow_const 2).aemeasurable]
      apply lintegral_congr
      intro z
      exact (Correctors.eLpNorm_two_sq (fun y => f (y + z) - f y) volume
        ((hfm.comp (measurable_id.fun_add (measurable_const (a := z)))).fun_sub hfm).aestronglyMeasurable).symm
    _ ≤ _ := lintegral_mono (fun z => clockBlockCube_indicator_shift_L2_le x z hL)

private theorem ofReal_integral_sq_eq_eLpNorm_sq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) = eLpNorm f 2 μ ^ 2 := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (ae_of_all _ fun x => sq_nonneg (f x)), Correctors.eLpNorm_two_sq _ _ hf.aestronglyMeasurable]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- The real spatial smoothing energy is controlled by the kernel's first
absolute displacement moment, with the cube surface factor explicit. -/
theorem clockBlockCube_average_sub_energy_le (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : Vec d => ∑ j, |z j|) ν) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ y, (truncatedClockTestFunction ν Set.univ
      ((clockBlockCube x L).indicator (fun _ => (1 : ℝ))) y -
        (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) ^ 2) ≤
      4 * d * L ^ (d - 1) * ∫ z, ∑ j, |z j| ∂ν := by
  have hfm : Measurable ((clockBlockCube x L).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_clockBlockCube x L)
  obtain ⟨_, hf2⟩ := integrable_bounded_block_test (measurableSet_clockBlockCube x L)
    (f := fun _ : Vec d => (1 : ℝ))
    (by rw [volume_clockBlockCube x hL]; finiteness) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) (by intro y hy; norm_num)
  have hfmem := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf2
  have hmem := (truncatedClockTestFunction_L2 ν MeasurableSet.univ hfm hf2).1.sub hfmem
  change MemLp (fun y => truncatedClockTestFunction ν Set.univ
    ((clockBlockCube x L).indicator (fun _ => (1 : ℝ))) y -
      (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) 2 volume at hmem
  have h := clockBlockCube_average_sub_L2_le ν x hL
  rw [← ofReal_integral_sq_eq_eLpNorm_sq hmem,
    ← ofReal_integral_eq_lintegral_ofReal (hν.const_mul (4 * d * L ^ (d - 1)))
      (ae_of_all _ fun z => by positivity), integral_const_mul] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- The actual clock block smoothing error consumes the displacement estimate,
through Fubini and the proved finite-range clock variance bound. -/
theorem clockCube_average_sub_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : Vec d => ∑ j, |z j|) ν) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ ω, ((∫ y in clockBlockCube x L, truncatedClockAverage Q ν Set.univ y ω) -
      ∫ y in clockBlockCube x L, centeredClockField Q y ω) ^ 2 ∂reducedLaw Q) ≤
      clockVarianceConstant d Λ₀ r₀ *
        (4 * d * L ^ (d - 1) * ∫ z, ∑ j, |z j| ∂ν) := by
  let f := (clockBlockCube x L).indicator (fun _ => (1 : ℝ))
  let g := truncatedClockTestFunction ν Set.univ f
  have hfm : Measurable f := measurable_const.indicator (measurableSet_clockBlockCube x L)
  obtain ⟨hfi, hf2⟩ := integrable_bounded_block_test (measurableSet_clockBlockCube x L)
    (f := fun _ : Vec d => (1 : ℝ))
    (by rw [volume_clockBlockCube x hL]; finiteness) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) (by intro y hy; norm_num)
  have hgm : Measurable g := measurable_truncatedClockTestFunction ν MeasurableSet.univ hfm
  have hgi : Integrable g := integrable_truncatedClockTestFunction ν MeasurableSet.univ hfm hfi
  have hgmem := (truncatedClockTestFunction_L2 ν MeasurableSet.univ hfm hf2).1
  have hfmem := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hf2
  have he : (fun ω => (∫ y in clockBlockCube x L, truncatedClockAverage Q ν Set.univ y ω) -
      ∫ y in clockBlockCube x L, centeredClockField Q y ω) =ᵐ[reducedLaw Q]
        clockTest Q (fun y => g y - f y) := by
    filter_upwards [ae_clockTest_truncatedAverage Q ν MeasurableSet.univ hfm hfi,
      (integrable_clockTest_integrand Q hgm hgi).prod_right_ae,
      (integrable_clockTest_integrand Q hfm hfi).prod_right_ae] with ω hω hgω hfω
    have hblock (m : Vec d → ℝ) : (∫ y, f y * m y) = ∫ y in clockBlockCube x L, m y := by
      rw [← integral_indicator (measurableSet_clockBlockCube x L)]
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        by_cases hy : y ∈ clockBlockCube x L <;> simp [f, hy]
    rw [← hblock (fun y => truncatedClockAverage Q ν Set.univ y ω),
      ← hblock (fun y => centeredClockField Q y ω), hω]
    unfold clockTest
    simp_rw [sub_mul]
    exact (integral_sub hgω hfω).symm
  rw [integral_congr_ae (he.mono fun ω hω => congrArg (fun a : ℝ => a ^ 2) hω)]
  exact (clockTest_variance_le Q (hgm.sub hfm) (hgi.sub hfi)
    (hgmem.sub hfmem).integrable_sq).trans
      (mul_le_mul_of_nonneg_left (clockBlockCube_average_sub_energy_le ν hν x hL)
        (clockVarianceConstant_nonneg Q))

private theorem integral_coordinate_inv_mulVec_gaussian (A : Mat d) (hA : A.PosDef)
    (j k : Fin d) (s : ℝ) (hs : 0 < s) :
    (∫ y : Vec d, y j * (A⁻¹).mulVec y k * anisotropicGaussian A s y) =
      s * unitVector k j := by
  have hsym : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hf : Differentiable ℝ (fun y : Vec d => y j) := by fun_prop
  have hg := (contDiff_anisotropicGaussian A s).differentiable (by simp)
  have hd (y : Vec d) : fderiv ℝ (fun y : Vec d => y j) y (unitVector k) =
      unitVector k j := by
    simp only [(hasFDerivAt_apply (𝕜 := ℝ) j y).fderiv, ContinuousLinearMap.proj_apply]
  have hi : Integrable (fun y : Vec d => y j * (A⁻¹).mulVec y k *
      anisotropicGaussian A s y) := by
    simpa only [Matrix.one_mulVec] using
      integrable_mulVec_mulVec_mul_anisotropicGaussian A hA 1 (A⁻¹) j k s hs
  have hf'g : Integrable (fun y : Vec d => fderiv ℝ (fun y : Vec d => y j) y
      (unitVector k) * anisotropicGaussian A s y) := by
    simp_rw [hd]
    exact (integrable_anisotropicGaussian A hA s hs).const_mul _
  have hfg' : Integrable (fun y : Vec d => y j * fderiv ℝ (anisotropicGaussian A s) y
      (unitVector k)) := by
    simp_rw [fderiv_anisotropicGaussian_coordinate A hsym]
    convert hi.const_mul (-1 / s) using 1
    funext y; ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg'
    (by simpa only [Matrix.one_mulVec] using
      integrable_mulVec_mul_anisotropicGaussian A hA 1 j s hs) (fun x _ => hf x) (fun x _ => hg x)
  simp_rw [hd, fderiv_anisotropicGaussian_coordinate A hsym] at h
  rw [show (fun y : Vec d => y j *
      (-((A⁻¹).mulVec y k) / s * anisotropicGaussian A s y)) =
        (fun y => (-1 / s) * (y j * (A⁻¹).mulVec y k * anisotropicGaussian A s y)) by
      funext y; ring, integral_const_mul, integral_const_mul,
    integral_anisotropicGaussian A hA s hs, mul_one] at h
  field_simp at h
  linarith

/-- The actual Gaussian's coordinate second moment retains the full covariance
entry s A_jj. This is obtained from Lebesgue integration by parts. -/
theorem clockGaussian_coordinate_second_moment (A : Mat d) (hA : A.PosDef)
    (j : Fin d) (s : ℝ) (hs : 0 < s) :
    (∫ y : Vec d, y j ^ 2 * anisotropicGaussian A s y) = s * A j j := by
  have hc (y : Vec d) : A.mulVec ((A⁻¹).mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
      Matrix.one_mulVec]
  have he (y : Vec d) : y j ^ 2 * anisotropicGaussian A s y =
      ∑ k, A j k * (y j * (A⁻¹).mulVec y k * anisotropicGaussian A s y) := by
    calc
      _ = y j * A.mulVec ((A⁻¹).mulVec y) j * anisotropicGaussian A s y := by rw [hc]; ring
      _ = _ := by
        change y j * (∑ k, A j k * (A⁻¹).mulVec y k) * anisotropicGaussian A s y = _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun k _ => by
    simpa only [Matrix.one_mulVec] using
      (integrable_mulVec_mulVec_mul_anisotropicGaussian A hA 1 (A⁻¹) j k s hs).const_mul
        (A j k))]
  simp_rw [integral_const_mul, integral_coordinate_inv_mulVec_gaussian A hA _ _ s hs]
  simp [unitVector, Pi.single_apply, mul_ite, mul_comm]

private theorem integrable_clockAveragingMeasure_iff {k f : Vec d → ℝ}
    (hkm : Measurable k) (hk0 : ∀ y, 0 ≤ k y) :
    Integrable f (clockAveragingMeasure k) ↔ Integrable (fun y => k y * f y) := by
  rw [clockAveragingMeasure, integrable_withDensity_iff_integrable_smul'
    hkm.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]

private theorem integral_clockAveragingMeasure {k : Vec d → ℝ}
    (hkm : Measurable k) (hk0 : ∀ y, 0 ≤ k y) (f : Vec d → ℝ) :
    (∫ y, f y ∂clockAveragingMeasure k) = ∫ y, k y * f y := by
  rw [clockAveragingMeasure, integral_withDensity_eq_integral_toReal_smul
    hkm.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]

private theorem integral_norm_le_sqrt_integral_sq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] {f : X → ℝ} (hf : MemLp f 2 ν) :
    (∫ y, ‖f y‖ ∂ν) ≤ Real.sqrt (∫ y, f y ^ 2 ∂ν) := by
  have h := ENNReal.toReal_mono hf.norm.ne
    (Correctors.enorm_integral_le_eLpNorm (p := 2) (by norm_num) hf.norm.aestronglyMeasurable)
  rw [toReal_enorm, Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _),
    eLpNorm_norm _ hf.aestronglyMeasurable] at h
  apply h.trans
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _), integral_sq_eq_eLpNorm_sq hf]

/-- The first absolute displacement moment of the actual anisotropic Gaussian
is finite and bounded by the square roots of its coordinate variances. -/
theorem clockGaussian_first_absolute_moment (A : Mat d) (hA : A.PosDef)
    (s : ℝ) (hs : 0 < s) :
    Integrable (fun y : Vec d => ∑ j, |y j|)
      (clockAveragingMeasure (anisotropicGaussian A s)) ∧
    (∫ y : Vec d, ∑ j, |y j| ∂clockAveragingMeasure (anisotropicGaussian A s)) ≤
      ∑ j, Real.sqrt (s * A j j) := by
  have hkm := (contDiff_anisotropicGaussian A s).continuous.measurable
  have hk0 (y : Vec d) : 0 ≤ anisotropicGaussian A s y := by unfold anisotropicGaussian; positivity
  letI := clockAveragingMeasure_probability (integrable_anisotropicGaussian A hA s hs)
    hk0 (integral_anisotropicGaussian A hA s hs)
  have hmem (j : Fin d) : MemLp (fun y : Vec d => y j) 2
      (clockAveragingMeasure (anisotropicGaussian A s)) := by
    apply (memLp_two_iff_integrable_sq (measurable_pi_apply j).aestronglyMeasurable).mpr
    apply (integrable_clockAveragingMeasure_iff hkm hk0).mpr
    simpa only [Matrix.one_mulVec, pow_two, mul_comm, mul_left_comm] using
      integrable_mulVec_mulVec_mul_anisotropicGaussian A hA 1 1 j j s hs
  have habsi (j : Fin d) : Integrable (fun y : Vec d => |y j|)
      (clockAveragingMeasure (anisotropicGaussian A s)) := by
    simpa only [Real.norm_eq_abs] using ((hmem j).integrable (by norm_num)).norm
  refine ⟨integrable_finset_sum _ (fun j _ => habsi j), ?_⟩
  rw [integral_finset_sum _ (fun j _ => habsi j)]
  apply Finset.sum_le_sum
  intro j _
  have h := integral_norm_le_sqrt_integral_sq (hmem j)
  rw [integral_clockAveragingMeasure hkm hk0 (fun y : Vec d => y j ^ 2),
    show (fun y : Vec d => anisotropicGaussian A s y * y j ^ 2) =
      (fun y => y j ^ 2 * anisotropicGaussian A s y) by funext y; ring,
    clockGaussian_coordinate_second_moment A hA j s hs] at h
  simpa only [Real.norm_eq_abs] using h

/-- Ellipticity makes the Gaussian displacement bound structural and linear in
its spatial scale r, before the environment law is chosen. -/
theorem clockHomogenizedGaussian_first_absolute_moment (Q : EnvironmentLaw d Λ₀ r₀)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : Vec d, ∑ j, |y j|
      ∂clockAveragingMeasure (anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2))) ≤
      d * Real.sqrt (sourceReducedBound Λ₀) * r := by
  apply (clockGaussian_first_absolute_moment (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) (r ^ 2) (sq_pos_of_pos hr)).2.trans
  have hj (j : Fin d) : homogenizedCoefficient Q j j ≤ sourceReducedBound Λ₀ := by
    have h := homogenizedMatrix_quadratic_upper Q (unitVector j)
    simpa [dot, euclideanSq, unitVector, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, ite_mul] using! h
  calc
    _ ≤ ∑ _ : Fin d, Real.sqrt (r ^ 2 * sourceReducedBound Λ₀) :=
      Finset.sum_le_sum (fun j _ => Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hj j) (sq_nonneg r)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]
      ring

/-- The transferred test is the literal density convolution, including a
measurable truncation set and with the adjoint plus sign in its displacement. -/
theorem truncatedClockTestFunction_eq_kernel {k : Vec d → ℝ}
    (hkm : Measurable k) (hk0 : ∀ y, 0 ≤ k y) {T : Set (Vec d)}
    (hT : MeasurableSet T) (f : Vec d → ℝ) (y : Vec d) :
    truncatedClockTestFunction (clockAveragingMeasure k) T f y =
      ∫ z in T, k z * f (y + z) := by
  unfold truncatedClockTestFunction clockAveragingMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hkm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk0 _), smul_eq_mul]
  rw [← integral_indicator hT]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by by_cases hz : z ∈ T <;> simp [hz]

/-- The source deterministic Gaussian cube smoothing estimate in squared L2
form, with a structural constant and ordinary Lebesgue normalization. -/
theorem clockCube_homogenizedGaussian_smoothing_energy_le (Q : EnvironmentLaw d Λ₀ r₀)
    {r : ℝ} (hr : 0 < r) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ y : Vec d, ((∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
      (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) (y + z)) -
        (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y) ^ 2) ≤
      4 * (d : ℝ) ^ 2 * Real.sqrt (sourceReducedBound Λ₀) * L ^ (d - 1) * r := by
  let A := homogenizedCoefficient Q
  have hA := posDef_homogenizedCoefficient Q
  have hs := sq_pos_of_pos hr
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A (r ^ 2) z := by
    unfold anisotropicGaussian; positivity
  letI := clockAveragingMeasure_probability (integrable_anisotropicGaussian A hA (r ^ 2) hs)
    hk0 (integral_anisotropicGaussian A hA (r ^ 2) hs)
  have h := clockBlockCube_average_sub_energy_le
    (clockAveragingMeasure (anisotropicGaussian A (r ^ 2)))
    (clockGaussian_first_absolute_moment A hA (r ^ 2) hs).1 x hL
  simp_rw [truncatedClockTestFunction_eq_kernel
    (contDiff_anisotropicGaussian A (r ^ 2)).continuous.measurable hk0 MeasurableSet.univ,
    Measure.restrict_univ] at h
  apply h.trans
  convert mul_le_mul_of_nonneg_left (clockHomogenizedGaussian_first_absolute_moment Q hr)
    (show 0 ≤ 4 * d * L ^ (d - 1) by positivity) using 1
  ring

/-- The genuine clock block differs from its unaveraged block by at most a
structural multiple of the surface-area times Gaussian scale in variance. -/
theorem clockCube_homogenizedGaussian_smoothing_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    {r : ℝ} (hr : 0 < r) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ ω, ((∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
        centeredClockField Q (y - z) ω) -
      ∫ y in clockBlockCube x L, centeredClockField Q y ω) ^ 2 ∂reducedLaw Q) ≤
      4 * clockVarianceConstant d Λ₀ r₀ * (d : ℝ) ^ 2 *
        Real.sqrt (sourceReducedBound Λ₀) * L ^ (d - 1) * r := by
  let A := homogenizedCoefficient Q
  have hA := posDef_homogenizedCoefficient Q
  have hs := sq_pos_of_pos hr
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A (r ^ 2) z := by
    unfold anisotropicGaussian; positivity
  letI := clockAveragingMeasure_probability (integrable_anisotropicGaussian A hA (r ^ 2) hs)
    hk0 (integral_anisotropicGaussian A hA (r ^ 2) hs)
  have h := clockCube_average_sub_variance_le Q
    (clockAveragingMeasure (anisotropicGaussian A (r ^ 2)))
    (clockGaussian_first_absolute_moment A hA (r ^ 2) hs).1 x hL
  simp_rw [truncatedClockAverage_eq_kernel Q
    (contDiff_anisotropicGaussian A (r ^ 2)).continuous.measurable hk0 MeasurableSet.univ,
    Measure.restrict_univ] at h
  apply h.trans
  convert mul_le_mul_of_nonneg_left (clockHomogenizedGaussian_first_absolute_moment Q hr)
    (show 0 ≤ clockVarianceConstant d Λ₀ r₀ * (4 * d * L ^ (d - 1)) from
      mul_nonneg (clockVarianceConstant_nonneg Q) (by positivity)) using 1 <;> ring

private theorem clockBlockCube_indicator_integral (x : Vec d) (L : ℝ) (m : Vec d → ℝ) :
    (∫ y, (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y * m y) =
      ∫ y in clockBlockCube x L, m y := by
  rw [← integral_indicator (measurableSet_clockBlockCube x L)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    by_cases hy : y ∈ clockBlockCube x L <;> simp [hy]

private theorem memLp_clockCube_average (Q : EnvironmentLaw d Λ₀ r₀)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] {T : Set (Vec d)}
    (hT : MeasurableSet T) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    MemLp (fun ω => ∫ y in clockBlockCube x L, truncatedClockAverage Q ν T y ω)
      2 (reducedLaw Q) := by
  have hfi := (integrableOn_const (by rw [volume_clockBlockCube x hL]; finiteness)
    (C := (1 : ℝ))).integrable_indicator (measurableSet_clockBlockCube x L)
  have h := memLp_clockTest_truncatedAverage Q ν hT
    (measurable_const.indicator (measurableSet_clockBlockCube x L)) hfi
  simpa only [clockBlockCube_indicator_integral] using h

private theorem memLp_clockCube (Q : EnvironmentLaw d Λ₀ r₀)
    (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    MemLp (fun ω => ∫ y in clockBlockCube x L, centeredClockField Q y ω)
      2 (reducedLaw Q) := by
  have hfi := (integrableOn_const (by rw [volume_clockBlockCube x hL]; finiteness)
    (C := (1 : ℝ))).integrable_indicator (measurableSet_clockBlockCube x L)
  have h := memLp_clockTest Q
    (measurable_const.indicator (measurableSet_clockBlockCube x L)) hfi
  change MemLp (fun ω => ∫ y,
    (clockBlockCube x L).indicator (fun _ => (1 : ℝ)) y * centeredClockField Q y ω)
      2 (reducedLaw Q) at h
  simpa only [clockBlockCube_indicator_integral] using h

private theorem memLp_clockCube_homogenizedGaussian (Q : EnvironmentLaw d Λ₀ r₀)
    {r : ℝ} (hr : 0 < r) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    MemLp (fun ω => ∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z * centeredClockField Q (y - z) ω)
      2 (reducedLaw Q) := by
  have hA := posDef_homogenizedCoefficient Q
  have hs := sq_pos_of_pos hr
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z := by
    unfold anisotropicGaussian; positivity
  letI := clockAveragingMeasure_probability
    (integrable_anisotropicGaussian (homogenizedCoefficient Q) hA (r ^ 2) hs)
    hk0 (integral_anisotropicGaussian (homogenizedCoefficient Q) hA (r ^ 2) hs)
  have h := memLp_clockCube_average Q
    (clockAveragingMeasure (anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)))
    MeasurableSet.univ x hL
  simpa only [truncatedClockAverage_eq_kernel Q
    (contDiff_anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2)).continuous.measurable hk0
      MeasurableSet.univ, Measure.restrict_univ] using h

/-- The genuine clock block comparison between any two positive smoothing
scales. Taking both scales at most R gives the source surface-area times R gain. -/
theorem clockCube_homogenizedGaussian_scaleChange_variance_le (Q : EnvironmentLaw d Λ₀ r₀)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (∫ ω, ((∫ y in clockBlockCube x L, ∫ z : Vec d,
      anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z * centeredClockField Q (y - z) ω) -
      ∫ y in clockBlockCube x L, ∫ z : Vec d,
        anisotropicGaussian (homogenizedCoefficient Q) (t ^ 2) z * centeredClockField Q (y - z) ω) ^ 2
      ∂reducedLaw Q) ≤
      8 * clockVarianceConstant d Λ₀ r₀ * (d : ℝ) ^ 2 *
        Real.sqrt (sourceReducedBound Λ₀) * L ^ (d - 1) * (r + t) := by
  let X := fun a : ℝ => fun ω => ∫ y in clockBlockCube x L, ∫ z : Vec d,
    anisotropicGaussian (homogenizedCoefficient Q) (a ^ 2) z * centeredClockField Q (y - z) ω
  let Y := fun ω => ∫ y in clockBlockCube x L, centeredClockField Q y ω
  have hrmem := memLp_clockCube_homogenizedGaussian Q hr x hL
  have htmem := memLp_clockCube_homogenizedGaussian Q ht x hL
  have hymem := memLp_clockCube Q x hL
  change MemLp (X r) 2 (reducedLaw Q) at hrmem
  change MemLp (X t) 2 (reducedLaw Q) at htmem
  change MemLp Y 2 (reducedLaw Q) at hymem
  have hri := (hrmem.sub hymem).integrable_sq
  have hti := (htmem.sub hymem).integrable_sq
  change Integrable (fun ω => (X r ω - Y ω) ^ 2) (reducedLaw Q) at hri
  change Integrable (fun ω => (X t ω - Y ω) ^ 2) (reducedLaw Q) at hti
  have h : (∫ ω, (X r ω - X t ω) ^ 2 ∂reducedLaw Q) ≤
      2 * (∫ ω, (X r ω - Y ω) ^ 2 ∂reducedLaw Q) +
        2 * (∫ ω, (X t ω - Y ω) ^ 2 ∂reducedLaw Q) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      (hri.const_mul 2) (hti.const_mul 2)]
    apply integral_mono (hrmem.sub htmem).integrable_sq
      ((hri.const_mul 2).add (hti.const_mul 2))
    intro ω
    dsimp only [Pi.add_apply, Pi.sub_apply]
    nlinarith [sq_nonneg (X r ω + X t ω - 2 * Y ω)]
  apply h.trans
  have hrbound := clockCube_homogenizedGaussian_smoothing_variance_le Q hr x hL
  have htbound := clockCube_homogenizedGaussian_smoothing_variance_le Q ht x hL
  change (∫ ω, (X r ω - Y ω) ^ 2 ∂reducedLaw Q) ≤ _ at hrbound
  change (∫ ω, (X t ω - Y ω) ^ 2 ∂reducedLaw Q) ≤ _ at htbound
  nlinarith

private theorem clockGaussian_density_split (A : Mat d) {s : ℝ} (hs : 0 < s) (z : Vec d) :
    anisotropicGaussian A s z =
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        Real.exp (-(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (4 * s)) *
          anisotropicGaussian A (2 * s) z := by
  have hp : (2 * Real.pi * (2 * s)) ^ (-(d : ℝ) / 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 * Real.pi * s) ^ (-(d : ℝ) / 2) := by
    rw [show 2 * Real.pi * (2 * s) = 2 * (2 * Real.pi * s) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have ht : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num),
      show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  unfold anisotropicGaussian
  rw [hp, show -(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (2 * s) =
      -(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (4 * s) +
        -(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (2 * (2 * s)) by ring, Real.exp_add]
  calc
    _ = ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2)) *
        ((2 * Real.pi * s) ^ (-(d : ℝ) / 2) / Real.sqrt A.det *
          (Real.exp (-(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (4 * s)) *
            Real.exp (-(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (2 * (2 * s))))) := by rw [ht]; ring
    _ = _ := by ring

/-- The actual anisotropic homogenized Gaussian has a structural exponential
tail outside a Euclidean ball, without replacing its covariance by an isotropic one. -/
theorem clockHomogenizedGaussian_tail_le (Q : EnvironmentLaw d Λ₀ r₀)
    {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) :
    (∫ z : Vec d in {z | R ≤ euclideanNorm z},
      anisotropicGaussian (homogenizedCoefficient Q) s z) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(R ^ 2 / (4 * s * sourceReducedBound Λ₀))) := by
  let A := homogenizedCoefficient Q
  let K := sourceReducedBound Λ₀
  have hK : 0 < K := by
    unfold K sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀]
  have hA := posDef_homogenizedCoefficient Q
  have htail : MeasurableSet {z : Vec d | R ≤ euclideanNorm z} := by
    apply measurableSet_le measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  let C := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(R ^ 2 / (4 * s * K)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := (integrable_anisotropicGaussian A hA (2 * s) (by positivity)).const_mul C
  calc
    _ ≤ ∫ z in {z : Vec d | R ≤ euclideanNorm z}, C * anisotropicGaussian A (2 * s) z := by
      apply setIntegral_mono_on (integrable_anisotropicGaussian A hA s hs).integrableOn
        hi.integrableOn htail
      intro z hz
      have hsq : 0 ≤ euclideanSq z := by
        change 0 ≤ ∑ j, z j * z j
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg (z j)
      have hRz : R ^ 2 ≤ euclideanSq z := by
        have h := pow_le_pow_left₀ hR hz 2
        simpa only [euclideanNorm, Real.sq_sqrt hsq] using h
      have hinv := ((Correctors.isElliptic_inverse hK
        (homogenizedMatrix_isElliptic Q) 0).2 z).1
      have hq : K⁻¹ * euclideanSq z ≤ ∑ j, ∑ k, z j * (A⁻¹) j k * z k := by
        simpa only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using! hinv
      have hscaled := mul_le_mul_of_nonneg_left hRz (inv_nonneg.mpr hK.le)
      have hexp : -(∑ j, ∑ k, z j * (A⁻¹) j k * z k) / (4 * s) ≤
          -(R ^ 2 / (4 * s * K)) := by
        apply (div_le_iff₀ (show 0 < 4 * s by positivity)).mpr
        have hc : R ^ 2 / (4 * s * K) * (4 * s) = K⁻¹ * R ^ 2 := by
          field_simp
        rw [neg_mul, hc]
        linarith
      rw [clockGaussian_density_split A hs z]
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)) (by
          unfold anisotropicGaussian; positivity)
    _ ≤ ∫ z : Vec d, C * anisotropicGaussian A (2 * s) z :=
      setIntegral_le_integral hi (ae_of_all _ fun z => by unfold anisotropicGaussian; positivity)
    _ = C := by rw [integral_const_mul, integral_anisotropicGaussian A hA (2 * s) (by positivity), mul_one]

private theorem clockGaussian_exp_inversePower_le {K δ : ℝ} (hK : 0 < K)
    (hδ : 0 < δ) (p : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
      Real.exp (-(r ^ (2 * δ) / (4 * K))) ≤ C * r ^ (-p) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (p / (2 * δ))
  have hnp : p ≤ 2 * δ * n := by
    have h := (div_le_iff₀ (show 0 < 2 * δ by positivity)).mp hn
    nlinarith
  refine ⟨(n.factorial : ℝ) * (4 * K) ^ n, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hx : 0 < r ^ (2 * δ) / (4 * K) := by positivity
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have h := one_div_le_one_div_of_le (div_pos (pow_pos hx n) hfact)
    (Real.pow_div_factorial_le_exp _ hx.le n)
  have he : (1 : ℝ) / Real.exp (r ^ (2 * δ) / (4 * K)) =
      Real.exp (-(r ^ (2 * δ) / (4 * K))) := by rw [one_div, Real.exp_neg]
  rw [he] at h
  have hratio : (1 : ℝ) / ((r ^ (2 * δ) / (4 * K)) ^ n / n.factorial) =
      (n.factorial : ℝ) * (4 * K) ^ n * r ^ (-(2 * δ * n)) := by
    rw [one_div_div, div_pow, div_div_eq_mul_div,
      ← Real.rpow_natCast (r ^ (2 * δ)) n, ← Real.rpow_mul hr0.le,
      Real.rpow_neg hr0.le]
    ring
  rw [hratio] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hr (by linarith : -(2 * δ * n) ≤ -p)) (by positivity))

private theorem clockGaussian_radius_ratio {r δ K : ℝ} (hr : 0 < r) :
    (r ^ (1 + δ)) ^ 2 / (4 * r ^ 2 * K) = r ^ (2 * δ) / (4 * K) := by
  rw [← Real.rpow_natCast (r ^ (1 + δ)) 2, ← Real.rpow_mul hr.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (1 + δ) * (2 : ℝ) = 2 + 2 * δ by ring, Real.rpow_add hr,
    Real.rpow_two]
  field_simp

/-- At the source Euclidean radius r^(1+δ), Gaussian truncation is smaller
than every inverse power. Its constant is chosen before the law and scale. -/
theorem clockHomogenizedGaussian_tail_inversePower_le (d : ℕ) {Λ₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) {δ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (r : ℝ), 1 ≤ r →
      (∫ z : Vec d in {z | r ^ (1 + δ) ≤ euclideanNorm z},
        anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z) ≤ C * r ^ (-p) := by
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg Λ₀]
  obtain ⟨C, hC, hbound⟩ := clockGaussian_exp_inversePower_le hK hδ p
  refine ⟨(2 : ℝ) ^ ((d : ℝ) / 2) * C, by positivity, ?_⟩
  intro r₀ Q r hr
  have hr0 := zero_lt_one.trans_le hr
  have h := clockHomogenizedGaussian_tail_le Q (sq_pos_of_pos hr0)
    (Real.rpow_nonneg hr0.le (1 + δ))
  rw [clockGaussian_radius_ratio hr0] at h
  apply h.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbound r hr)
    (show 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) by positivity)

/-- Removing any measurable part of the actual Gaussian clock convolution has
an almost-sure error, uniform in space, bounded by the removed Gaussian mass. -/
theorem ae_abs_clockGaussian_truncation_error_le (Q : EnvironmentLaw d Λ₀ r₀)
    (A : Mat d) (hA : A.PosDef) {s : ℝ} (hs : 0 < s)
    {T : Set (Vec d)} (hT : MeasurableSet T) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
      |(∫ z : Vec d, anisotropicGaussian A s z * centeredClockField Q (x - z) ω) -
        ∫ z in T, anisotropicGaussian A s z * centeredClockField Q (x - z) ω| ≤
          2 * sourceReducedBound Λ₀ * ∫ z in Tᶜ, anisotropicGaussian A s z := by
  have hk := integrable_anisotropicGaussian A hA s hs
  have hkm := (contDiff_anisotropicGaussian A s).continuous.measurable
  have hk0 (z : Vec d) : 0 ≤ anisotropicGaussian A s z := by unfold anisotropicGaussian; positivity
  filter_upwards [ae_forall_abs_centeredClockField_le Q] with ω hω
  intro x
  have hm : Measurable (fun z : Vec d => centeredClockField Q (x - z) ω) :=
    ((continuous_centeredClockField Q).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)).measurable
  have hi : Integrable (fun z : Vec d => anisotropicGaussian A s z *
      centeredClockField Q (x - z) ω) := by
    apply (hk.mul_const (2 * sourceReducedBound Λ₀)).mono' (hkm.fun_mul hm).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [norm_mul, Real.norm_eq_abs (anisotropicGaussian A s z), abs_of_nonneg (hk0 z),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hω (x - z)) (hk0 z)
  have he : (∫ z : Vec d, anisotropicGaussian A s z * centeredClockField Q (x - z) ω) -
      (∫ z in T, anisotropicGaussian A s z * centeredClockField Q (x - z) ω) =
        ∫ z in Tᶜ, anisotropicGaussian A s z * centeredClockField Q (x - z) ω := by
    linarith [integral_add_compl hT hi]
  rw [he]
  calc
    _ ≤ ∫ z in Tᶜ, ‖anisotropicGaussian A s z * centeredClockField Q (x - z) ω‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun z : Vec d => anisotropicGaussian A s z * centeredClockField Q (x - z) ω)
        (μ := volume.restrict Tᶜ)
    _ ≤ ∫ z in Tᶜ, (2 * sourceReducedBound Λ₀) * anisotropicGaussian A s z := by
      apply setIntegral_mono_on hi.norm.integrableOn
        (hk.const_mul (2 * sourceReducedBound Λ₀)).integrableOn hT.compl
      intro z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 z)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hω (x - z)) (hk0 z)
    _ = _ := integral_const_mul _ _

/-- The source localization of the actual clock at Euclidean radius r^(1+δ)
has an almost-sure spatially uniform error smaller than every inverse power.
The constant precedes the environment law and smoothing scale. -/
theorem clockHomogenizedGaussian_truncation_inversePower_le (d : ℕ) {Λ₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) {δ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (r : ℝ), 1 ≤ r →
      ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
        |(∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
          centeredClockField Q (x - z) ω) -
          ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
            anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
              centeredClockField Q (x - z) ω| ≤ C * r ^ (-p) := by
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    nlinarith [sq_nonneg Λ₀]
  obtain ⟨C, hC, hbound⟩ := clockHomogenizedGaussian_tail_inversePower_le d hΛ₀ hδ p
  refine ⟨2 * sourceReducedBound Λ₀ * C, by positivity, ?_⟩
  intro r₀ Q r hr
  have hT : MeasurableSet {z : Vec d | euclideanNorm z < r ^ (1 + δ)} := by
    apply measurableSet_lt _ measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have he : {z : Vec d | euclideanNorm z < r ^ (1 + δ)}ᶜ =
      {z : Vec d | r ^ (1 + δ) ≤ euclideanNorm z} := by ext z; simp
  filter_upwards [ae_abs_clockGaussian_truncation_error_le Q (homogenizedCoefficient Q)
    (posDef_homogenizedCoefficient Q) (sq_pos_of_pos (zero_lt_one.trans_le hr)) hT] with ω hω
  intro x
  have h := hω x
  rw [he] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound Q r hr) (show 0 ≤ 2 * sourceReducedBound Λ₀ by positivity))

private theorem measurable_clockGaussian_average (Q : EnvironmentLaw d Λ₀ r₀)
    (A : Mat d) (s : ℝ) {T : Set (Vec d)} (hT : MeasurableSet T) :
    Measurable (fun p : Vec d × FieldPair d => ∫ z in T,
      anisotropicGaussian A s z * centeredClockField Q (p.1 - z) p.2) := by
  have hF : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      T.indicator (fun z => anisotropicGaussian A s z *
        centeredClockField Q (p.1.1 - z) p.1.2) p.2) := by
    convert (((contDiff_anisotropicGaussian A s).continuous.measurable.comp measurable_snd).mul
      ((continuous_centeredClockField Q).measurable.comp
        ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))).indicator
          (measurable_snd hT) using 1
    funext p
    by_cases hp : p.2 ∈ T <;> simp [Set.indicator, hp]
  convert (hF.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Vec d)))).measurable using 1
  funext p
  rw [← integral_indicator hT]

/-- The quantitative localization error is a genuine clock block L2 estimate.
Product measurability and spatial integrability are constructed, and the
constant is uniform in the law, block location, block size and Gaussian scale. -/
theorem clockCube_homogenizedGaussian_truncation_variance_inversePower_le
    (d : ℕ) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) {δ : ℝ} (hδ : 0 < δ) (p : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (r : ℝ), 1 ≤ r →
      ∀ (x : Vec d) (L : ℝ), 0 ≤ L →
      (∫ ω, (∫ y in clockBlockCube x L,
        ((∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
          centeredClockField Q (y - z) ω) -
          ∫ z in {z : Vec d | euclideanNorm z < r ^ (1 + δ)},
            anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
              centeredClockField Q (y - z) ω)) ^ 2 ∂reducedLaw Q) ≤
        (C * L ^ d * r ^ (-p)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := clockHomogenizedGaussian_truncation_inversePower_le d hΛ₀ hδ p
  refine ⟨C, hC, ?_⟩
  intro r₀ Q r hr x L hL
  let T := {z : Vec d | euclideanNorm z < r ^ (1 + δ)}
  have hT : MeasurableSet T := by
    apply measurableSet_lt _ measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  let F := fun q : Vec d × FieldPair d =>
    (∫ z : Vec d, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
      centeredClockField Q (q.1 - z) q.2) -
    ∫ z in T, anisotropicGaussian (homogenizedCoefficient Q) (r ^ 2) z *
      centeredClockField Q (q.1 - z) q.2
  have hFm : Measurable F := by
    have hu := measurable_clockGaussian_average Q (homogenizedCoefficient Q) (r ^ 2) MeasurableSet.univ
    simpa only [Measure.restrict_univ] using! hu.sub
      (measurable_clockGaussian_average Q (homogenizedCoefficient Q) (r ^ 2) hT)
  have hbm : Measurable (fun ω => ∫ y in clockBlockCube x L, F (y, ω)) := by
    have hI : Measurable (fun q : FieldPair d × Vec d =>
        (clockBlockCube x L).indicator (fun y => F (y, q.1)) q.2) := by
      convert (hFm.comp measurable_swap).indicator
        (measurable_snd (measurableSet_clockBlockCube x L)) using 1
      funext p
      by_cases hp : p.2 ∈ clockBlockCube x L <;> simp [Set.indicator, hp, Prod.swap]
    convert (hI.stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure (Vec d)))).measurable using 1
    funext ω
    rw [← integral_indicator (measurableSet_clockBlockCube x L)]
  have hLf : volume (clockBlockCube x L) < ∞ := by rw [volume_clockBlockCube x hL]; finiteness
  have hb : ∀ᵐ ω ∂reducedLaw Q, ‖∫ y in clockBlockCube x L, F (y, ω)‖ ≤
      C * L ^ d * r ^ (-p) := by
    filter_upwards [hbound Q r hr] with ω hω
    have hFi : IntegrableOn (fun y => F (y, ω)) (clockBlockCube x L) volume := by
      apply IntegrableOn.of_bound hLf
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable.restrict
        (C * r ^ (-p))
      exact ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using! hω y
    calc
      _ ≤ ∫ y in clockBlockCube x L, ‖F (y, ω)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ in clockBlockCube x L, C * r ^ (-p) := by
        apply integral_mono hFi.norm (integrableOn_const hLf.ne)
        intro y
        simpa only [Real.norm_eq_abs] using! hω y
      _ = _ := by rw [setIntegral_const, smul_eq_mul, volumeReal_clockBlockCube x hL]; ring
  have hmem := MemLp.of_bound (p := 2) hbm.aestronglyMeasurable (C * L ^ d * r ^ (-p)) hb
  change (∫ ω, (∫ y in clockBlockCube x L, F (y, ω)) ^ 2 ∂reducedLaw Q) ≤ _
  apply (integral_mono_ae hmem.integrable_sq (integrable_const ((C * L ^ d * r ^ (-p)) ^ 2))
    (hb.mono fun ω hω => by
      rw [Real.norm_eq_abs] at hω
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2)).trans_eq
  simp only [integral_const, probReal_univ, one_smul]

end EinsteinFull
