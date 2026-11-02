import EinsteinRelation.Entropy.DensityZeroSetGradient
import EinsteinRelation.Correctors.HorizontalMollifierBounds
import EinsteinRelation.Correctors.HorizontalMollifierRepresentative
import EinsteinRelation.Correctors.HorizontalMollifierApproximation
import EinsteinRelation.Correctors.HorizontalScaledMollifierCore
import EinsteinRelation.Calculus.HorizontalTranslationLpGen
import EinsteinRelation.Calculus.HorizontalWeakL1UniquenessSupport
import EinsteinRelation.Calculus.EnvironmentWeakCalculusCore
import EinsteinRelation.Calculus.HorizontalMollification
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! # The weak horizontal chain rule for `C¹` profiles with bounded derivative

Source `paper/main.tex:241–249` (weak horizontal gradients) and `paper/main.tex:545–566`
(the horizontal smoothing `S_ε f = ∫ κ_ε(x) f(T_x ω) dx`).

For a stationary probability law `Q` on coefficient pairs and a scalar field `f` with weak
horizontal gradient `Df`, composition with a profile `g` of class `C¹` with bounded derivative
gives the weak gradient `g'(f) Df`. The proof mollifies `f` along the translation group. The
mollified field has `C^∞` orbits, its orbit derivative is the mollified `Df` almost everywhere, and
the chain rule holds along each orbit. The mollifications converge in `L¹(Q)`, and the identity
passes to the limit against bounded horizontal cores; the cores approximate every horizontally
smooth test in `L²(Q)`.
-/

open MeasureTheory Filter
open scoped Topology Convolution ENNReal

namespace EinsteinRelation.Calculus

variable {d : ℕ}

/-! ### The unit-mass kernel and its supports -/

/-- The Euclidean norm dominates the sup norm on `Vec d`. -/
private theorem norm_le_euclideanNorm_vec' (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have hsq : x i ^ 2 ≤ euclideanSq x := by
    unfold euclideanSq dot
    rw [sq]
    exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
      (Finset.mem_univ i)
  exact Real.abs_le_sqrt hsq

/-- The unit-mass kernel `κ_ε` at scale `ε ∈ (0, 1]` is supported in the open sup-norm unit
ball. -/
private theorem norm_lt_one_of_kernel_ne_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : Vec d}
    (hx : unitMassScaledMollifier d ε x ≠ 0) : ‖x‖ < 1 := by
  have hx' : (ε ^ d)⁻¹ * mollifier d (ε⁻¹ • x) ≠ 0 := hx
  have hm : mollifier d (ε⁻¹ • x) ≠ 0 := right_ne_zero_of_mul hx'
  have hts : ε⁻¹ • x ∈ tsupport (mollifier d) :=
    subset_tsupport _ (Function.mem_support.mpr hm)
  have h1 : euclideanNorm (ε⁻¹ • x) < 1 := tsupport_mollifier_subset d hts
  have h2 : ‖ε⁻¹ • x‖ ≤ euclideanNorm (ε⁻¹ • x) := norm_le_euclideanNorm_vec' _
  have h3 : ε * ‖ε⁻¹ • x‖ = ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε), ← mul_assoc,
      mul_inv_cancel₀ hε.ne', one_mul]
  have h4 : 0 ≤ ‖ε⁻¹ • x‖ := norm_nonneg _
  have h5 : ε * ‖ε⁻¹ • x‖ ≤ ‖ε⁻¹ • x‖ := mul_le_of_le_one_left h4 hε1
  linarith

private theorem contDiff_unitMassScaled (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (unitMassScaledMollifier d ε) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ε⁻¹ • x) := contDiff_id.const_smul (ε⁻¹ : ℝ)
  unfold unitMassScaledMollifier
  exact contDiff_const.mul ((contDiff_mollifier d).comp hs)

private theorem hasCompactSupport_unitMassScaled {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    HasCompactSupport (unitMassScaledMollifier d ε) := by
  have hsub : tsupport (unitMassScaledMollifier d ε) ⊆ Metric.closedBall (0 : Vec d) 1 := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_lt_one_of_kernel_ne_zero hε hε1 (Function.mem_support.mp hx)).le
  exact (isCompact_closedBall (0 : Vec d) 1).of_isClosed_subset (isClosed_tsupport _) hsub

private theorem unitMassScaled_nonneg {ε : ℝ} (hε : 0 < ε) (z : Vec d) :
    0 ≤ unitMassScaledMollifier d ε z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le d)) (mollifier_nonneg d _)

private theorem integral_unitMassScaled_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ z : Vec d, unitMassScaledMollifier d ε z = 1 := by
  unfold unitMassScaledMollifier
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (μ := volume) (mollifier d) hε.le,
    Module.finrank_fin_fun, integral_mollifier, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_ne_zero d hε.ne')]

private theorem contDiff_coordinateDerivative_vec {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i f) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

/-- The coordinate derivative of the unit-mass kernel is bounded, uniformly in the point. -/
private theorem exists_bound_coordinateDerivative_kernel (i : Fin d) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Vec d, |coordinateDerivative i (unitMassScaledMollifier d ε) t| ≤ C := by
  have hcont := (contDiff_coordinateDerivative_vec (contDiff_unitMassScaled ε) i).continuous
  have hcs : HasCompactSupport (coordinateDerivative i (unitMassScaledMollifier d ε)) :=
    (hasCompactSupport_unitMassScaled hε hε1).fderiv_apply ℝ (unitVector i)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC t).trans (le_max_left _ _)

/-- The coordinate derivative of the unit-mass kernel vanishes outside the closed unit ball. -/
private theorem coordinateDerivative_kernel_eq_zero (i : Fin d) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {t : Vec d} (ht : 1 < ‖t‖) :
    coordinateDerivative i (unitMassScaledMollifier d ε) t = 0 := by
  have hsub : tsupport (unitMassScaledMollifier d ε) ⊆ Metric.closedBall (0 : Vec d) 1 := by
    refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_lt_one_of_kernel_ne_zero hε hε1 (Function.mem_support.mp hx)).le
  have hnot : t ∉ tsupport (unitMassScaledMollifier d ε) := fun h => by
    have h' := hsub h
    rw [Metric.mem_closedBall, dist_zero_right] at h'
    linarith
  show fderiv ℝ (unitMassScaledMollifier d ε) t (unitVector i) = 0
  simp [fderiv_of_notMem_tsupport ℝ hnot]

/-! ### Stationarity and measurability of translations -/

private theorem integrable_comp_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hu : Integrable u Q) (y : Vec d) :
    Integrable (fun ω => u (translate y ω)) Q := by
  have h : Integrable u (Measure.map (translate y) Q) := by
    rw [hQ y]
    exact hu
  exact h.comp_measurable (Probability.measurable_translate y)

private theorem measurable_translate_pair :
    Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
  Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)

private theorem measurable_translate_neg_pair :
    Measurable (fun p : FieldPair d × Vec d => translate (-p.2) p.1) :=
  Probability.continuous_translate.measurable.comp ((measurable_snd.neg).prodMk measurable_fst)

/-- A bounded measurable factor preserves integrability of a product-measure integrand. -/
private theorem integrable_mul_bdd_prod {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {a : FieldPair d × Vec d → ℝ} (ha : Integrable a (Q.prod volume))
    {g : FieldPair d × Vec d → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ p, |g p| ≤ B) :
    Integrable (fun p => a p * g p) (Q.prod volume) :=
  ha.mul_bdd (c := B) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB p)

/-- The kernel-weighted translated observable is integrable on the product measure. -/
private theorem integrable_kernel_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ)
    {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    Integrable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1)) (Q.prod volume) := by
  have hmeas : Measurable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1)) :=
    (hκm.comp measurable_snd).mul (hum.comp measurable_translate_pair)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · exact (integrable_comp_translate hQ hui y).const_mul (κ y)
  · have hnorm : ∀ y : Vec d, (∫ ω, ‖κ y * u (translate y ω)‖ ∂Q) =
        ‖κ y‖ * ∫ ω, ‖u ω‖ ∂Q := by
      intro y
      have h1 : (fun ω => ‖κ y * u (translate y ω)‖) = fun ω => ‖κ y‖ * ‖u (translate y ω)‖ := by
        funext ω
        rw [norm_mul]
      rw [h1, integral_const_mul]
      congr 1
      exact Probability.integral_translate Q hQ y (fun η => ‖u η‖) hum.norm
    refine Integrable.congr (hκi.norm.mul_const (∫ ω, ‖u ω‖ ∂Q))
      (Filter.Eventually.of_forall fun y => ?_)
    exact (hnorm y).symm

/-! ### Fubini exchange and the adjoint identity -/

/-- Exchange of the kernel integral with an observable integral. -/
private theorem integral_kernel_pair_swap {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (κ : Vec d → ℝ) (V : FieldPair d → Vec d → ℝ) (W : FieldPair d → ℝ)
    (hint : Integrable (fun p : FieldPair d × Vec d => κ p.2 * V p.1 p.2 * W p.1)
      (Q.prod volume)) :
    (∫ ω, (∫ y, κ y * V ω y) * W ω ∂Q) = ∫ y, κ y * (∫ ω, V ω y * W ω ∂Q) := by
  have h1 : (fun ω => (∫ y, κ y * V ω y) * W ω) = fun ω => ∫ y, κ y * V ω y * W ω := by
    funext ω
    rw [← integral_mul_const]
  rw [h1, integral_integral_swap hint]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  show (∫ ω, κ y * V ω y * W ω ∂Q) = κ y * ∫ ω, V ω y * W ω ∂Q
  rw [← integral_const_mul]
  simp only [mul_assoc]

/-- The adjoint identity for the horizontal smoothing, tested against a bounded observable. -/
theorem integral_horizontalMollify_mul_eq_adj {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ)
    {u W : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q)
    (hWm : Measurable W) {B : ℝ} (hWB : ∀ ω, |W ω| ≤ B) :
    (∫ ω, horizontalMollify κ u ω * W ω ∂Q) =
      ∫ ω, u ω * (∫ y, κ y * W (translate (-y) ω) ∂volume) ∂Q := by
  have hint1 : Integrable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1) * W p.1)
      (Q.prod volume) :=
    integrable_mul_bdd_prod (integrable_kernel_translate hQ hκm hκi hum hui)
      (hWm.comp measurable_fst) (fun p => hWB p.1)
  have hint2 : Integrable (fun p : FieldPair d × Vec d => κ p.2 * W (translate (-p.2) p.1) * u p.1)
      (Q.prod volume) := by
    have hprod : Integrable (fun p : FieldPair d × Vec d => u p.1 * κ p.2) (Q.prod volume) :=
      hui.mul_prod hκi
    have hb := integrable_mul_bdd_prod hprod (g := fun p : FieldPair d × Vec d =>
        W (translate (-p.2) p.1)) (hWm.comp measurable_translate_neg_pair) (B := B)
      (fun p => hWB _)
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show u p.1 * κ p.2 * W (translate (-p.2) p.1) = κ p.2 * W (translate (-p.2) p.1) * u p.1
    ring
  -- First exchange: the translated observable under the kernel integral.
  have step1 : (∫ ω, horizontalMollify κ u ω * W ω ∂Q) =
      ∫ y, κ y * (∫ ω, u (translate y ω) * W ω ∂Q) ∂volume := by
    show (∫ ω, (∫ y, κ y * u (translate y ω)) * W ω ∂Q) = _
    exact integral_kernel_pair_swap κ (fun ω y => u (translate y ω)) W hint1
  -- Stationarity moves the translation onto the observable.
  have step2 : ∀ y : Vec d, (∫ ω, u (translate y ω) * W ω ∂Q) =
      ∫ ω, u ω * W (translate (-y) ω) ∂Q := by
    intro y
    have hcancel : ∀ ω : FieldPair d, translate (-y) (translate y ω) = ω := by
      intro ω
      rw [translate_add, neg_add_cancel, translate_zero]
    have hm : Measurable (fun η : FieldPair d => u η * W (translate (-y) η)) :=
      hum.mul (hWm.comp (Probability.measurable_translate (-y)))
    have h := Probability.integral_translate Q hQ y
      (fun η => u η * W (translate (-y) η)) hm
    simp only [hcancel] at h
    exact h
  have step3 : (∫ y, κ y * (∫ ω, u (translate y ω) * W ω ∂Q) ∂volume) =
      ∫ y, κ y * (∫ ω, u ω * W (translate (-y) ω) ∂Q) ∂volume := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    show κ y * (∫ ω, u (translate y ω) * W ω ∂Q) = κ y * ∫ ω, u ω * W (translate (-y) ω) ∂Q
    rw [step2 y]
  -- Second exchange, back to the observable side.
  have step4 := integral_kernel_pair_swap κ (fun ω y => W (translate (-y) ω)) u hint2
  rw [step1, step3]
  calc (∫ y, κ y * (∫ ω, u ω * W (translate (-y) ω) ∂Q) ∂volume)
      = ∫ y, κ y * (∫ ω, W (translate (-y) ω) * u ω ∂Q) ∂volume := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun y => ?_
        show κ y * (∫ ω, u ω * W (translate (-y) ω) ∂Q) =
          κ y * ∫ ω, W (translate (-y) ω) * u ω ∂Q
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    _ = ∫ ω, (∫ y, κ y * W (translate (-y) ω) ∂volume) * u ω ∂Q := step4.symm
    _ = ∫ ω, u ω * (∫ y, κ y * W (translate (-y) ω) ∂volume) ∂Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => mul_comm _ _

/-! ### Core-level weak identities and the mollified pairing -/

/-- A translate of a bounded orbit core is a bounded orbit core. -/
private theorem isHorizontalTest_translate_core {H : FieldPair d → ℝ} (hH : IsHorizontalTest H)
    (x : Vec d) : IsHorizontalTest (fun ω => H (translate x ω)) := by
  refine ⟨hH.1.comp (Probability.measurable_translate x), ?_, ?_⟩
  · intro ω
    have horbit : orbit (fun η => H (translate x η)) ω = orbit H (translate x ω) := by
      funext y
      simp [orbit, translate_add, add_comm]
    rw [horbit]
    exact hH.2.1 (translate x ω)
  · intro coordinates
    obtain ⟨M, hM⟩ := hH.2.2 coordinates
    refine ⟨M, ?_⟩
    intro ω y
    have horbit : orbit (fun η => H (translate x η)) ω = orbit H (translate x ω) := by
      funext z
      simp [orbit, translate_add, add_comm]
    rw [horbit]
    exact hM (translate x ω) y

/-- The horizontal derivative of a translated core is the translated horizontal derivative. -/
private theorem horizontalDerivative_translate_core {H : FieldPair d → ℝ} (i : Fin d) (x : Vec d)
    (ω : FieldPair d) :
    horizontalDerivative i (fun η => H (translate x η)) ω =
      horizontalDerivative i H (translate x ω) := by
  have hfun : orbit (fun η => H (translate x η)) ω = fun y => orbit H ω (x + y) := by
    funext y
    simp only [orbit, translate_add]
  rw [horizontalDerivative_translate]
  simp only [horizontalDerivative, coordinateDerivative, hfun, fderiv_comp_add_left, add_zero]

/-- The weak gradient identity of `f`, tested against a bounded orbit core. -/
theorem weakPairing_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (i : Fin d) {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, f ω * horizontalDerivative i H ω ∂Q) = -(∫ ω, Df ω i * H ω ∂Q) := by
  have hW := hf.2.2 i ((hH.memLp Q 2).toLp H)
    ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H))
    (hH.isHorizontallySmoothTest Q hQ) (hH.hasHorizontalLpDerivative_toLp Q hQ i)
  have hG : ∀ᵐ ω ∂Q, ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)) ω =
      horizontalDerivative i H ω := (hH.memLp_derivative Q 2 i).coeFn_toLp
  have hF : ∀ᵐ ω ∂Q, ((hH.memLp Q 2).toLp H) ω = H ω := (hH.memLp Q 2).coeFn_toLp
  have e1 : (∫ ω, f ω * horizontalDerivative i H ω ∂Q) =
      ∫ ω, f ω * ((hH.memLp_derivative Q 2 i).toLp (horizontalDerivative i H)) ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hG] with ω hω
    rw [hω]
  have e2 : (∫ ω, Df ω i * H ω ∂Q) = ∫ ω, Df ω i * ((hH.memLp Q 2).toLp H) ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hF] with ω hω
    rw [hω]
  rw [e1, e2]
  exact hW

/-- The derivative exchange for the adjoint smoothing. The weak identity, tested against the
translated cores `H(T_{-y} ·)`, moves the horizontal derivative from `H` onto the observable. -/
theorem integral_adjoint_derivative_eq {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {u Du : FieldPair d → ℝ} (hu : Integrable u Q) (hDu : Integrable Du Q)
    (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q))
    {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ) {H : FieldPair d → ℝ}
    (hH : IsHorizontalTest H) :
    (∫ ω, u ω * (∫ y, κ y * horizontalDerivative i H (translate (-y) ω) ∂volume) ∂Q) =
      -(∫ ω, (∫ y, κ y * H (translate (-y) ω) ∂volume) * Du ω ∂Q) := by
  obtain ⟨M, -, hM⟩ := hH.bound_orbit
  obtain ⟨B, -, hB⟩ := hH.bound_derivative i
  have hmeasD : Measurable (fun p : FieldPair d × Vec d =>
      horizontalDerivative i H (translate (-p.2) p.1)) :=
    (hH.measurable_derivative i).comp measurable_translate_neg_pair
  have hboundD : ∀ p : FieldPair d × Vec d,
      |horizontalDerivative i H (translate (-p.2) p.1)| ≤ B :=
    fun p => hB (translate (-p.2) p.1) 0
  have hmeasH : Measurable (fun p : FieldPair d × Vec d => H (translate (-p.2) p.1)) :=
    hH.1.comp measurable_translate_neg_pair
  have hboundH : ∀ p : FieldPair d × Vec d, |H (translate (-p.2) p.1)| ≤ M :=
    fun p => by simpa only [orbit_zero] using hM (translate (-p.2) p.1) 0
  -- Integrability of the two exchanged integrands.
  have hint1 : Integrable (fun p : FieldPair d × Vec d =>
      κ p.2 * horizontalDerivative i H (translate (-p.2) p.1) * u p.1) (Q.prod volume) := by
    have hprod : Integrable (fun p : FieldPair d × Vec d => u p.1 * κ p.2) (Q.prod volume) :=
      hu.mul_prod hκi
    have hb := integrable_mul_bdd_prod hprod (g := fun p : FieldPair d × Vec d =>
      horizontalDerivative i H (translate (-p.2) p.1)) hmeasD (B := B) hboundD
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show u p.1 * κ p.2 * horizontalDerivative i H (translate (-p.2) p.1) =
      κ p.2 * horizontalDerivative i H (translate (-p.2) p.1) * u p.1
    ring
  have hint2 : Integrable (fun p : FieldPair d × Vec d =>
      κ p.2 * H (translate (-p.2) p.1) * Du p.1) (Q.prod volume) := by
    have hprod : Integrable (fun p : FieldPair d × Vec d => Du p.1 * κ p.2) (Q.prod volume) :=
      hDu.mul_prod hκi
    have hb := integrable_mul_bdd_prod hprod (g := fun p : FieldPair d × Vec d =>
      H (translate (-p.2) p.1)) hmeasH (B := M) hboundH
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show Du p.1 * κ p.2 * H (translate (-p.2) p.1) =
      κ p.2 * H (translate (-p.2) p.1) * Du p.1
    ring
  -- The weak identity for each translation of the core.
  have hper : ∀ y : Vec d, (∫ ω, u ω * horizontalDerivative i H (translate (-y) ω) ∂Q) =
      -(∫ ω, Du ω * H (translate (-y) ω) ∂Q) := by
    intro y
    have h := hweak (fun η => H (translate (-y) η)) (isHorizontalTest_translate_core hH (-y))
    simp only [horizontalDerivative_translate_core] at h
    exact h
  have hL : (∫ ω, u ω * (∫ y, κ y * horizontalDerivative i H (translate (-y) ω) ∂volume) ∂Q) =
      ∫ y, κ y * (∫ ω, horizontalDerivative i H (translate (-y) ω) * u ω ∂Q) ∂volume := by
    have h1 : (fun ω => u ω * (∫ y, κ y * horizontalDerivative i H (translate (-y) ω) ∂volume)) =
        fun ω => (∫ y, κ y * horizontalDerivative i H (translate (-y) ω)) * u ω := by
      funext ω
      exact mul_comm _ _
    rw [h1]
    exact integral_kernel_pair_swap κ (fun ω y => horizontalDerivative i H (translate (-y) ω))
      u hint1
  have hc : ∀ y : Vec d, (∫ ω, horizontalDerivative i H (translate (-y) ω) * u ω ∂Q) =
      -(∫ ω, Du ω * H (translate (-y) ω) ∂Q) := by
    intro y
    rw [← hper y]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => mul_comm _ _
  have hS : (∫ ω, (∫ y, κ y * H (translate (-y) ω) ∂volume) * Du ω ∂Q) =
      ∫ y, κ y * (∫ ω, H (translate (-y) ω) * Du ω ∂Q) ∂volume :=
    integral_kernel_pair_swap κ (fun ω y => H (translate (-y) ω)) Du hint2
  rw [hL, hS]
  rw [← integral_neg]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  show κ y * (∫ ω, horizontalDerivative i H (translate (-y) ω) * u ω ∂Q) =
    -(κ y * ∫ ω, H (translate (-y) ω) * Du ω ∂Q)
  have hmul : (∫ ω, Du ω * H (translate (-y) ω) ∂Q) =
      ∫ ω, H (translate (-y) ω) * Du ω ∂Q := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => mul_comm _ _
  rw [hc y, hmul, mul_neg]

/-- The mollified pairing: the horizontal derivative of a bounded core is paired with the mollified
observable exactly as the mollified weak gradient. -/
theorem integral_horizontalMollify_mul_derivative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u Du : FieldPair d → ℝ}
    (hum : Measurable u) (hu : Integrable u Q) (hDum : Measurable Du) (hDu : Integrable Du Q)
    (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q))
    {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ) {H : FieldPair d → ℝ}
    (hH : IsHorizontalTest H) :
    (∫ ω, horizontalMollify κ u ω * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, horizontalMollify κ Du ω * H ω ∂Q) := by
  obtain ⟨M, -, hM⟩ := hH.bound_orbit
  obtain ⟨B, -, hB⟩ := hH.bound_derivative i
  have hWm : Measurable (horizontalDerivative i H) := hH.measurable_derivative i
  have hWB : ∀ ω, |horizontalDerivative i H ω| ≤ B := fun ω => hB ω 0
  have hHm : Measurable H := hH.1
  have hHB : ∀ ω, |H ω| ≤ M := fun ω => by simpa only [orbit_zero] using hM ω 0
  rw [integral_horizontalMollify_mul_eq_adj hQ hκm hκi hum hu hWm hWB]
  rw [integral_adjoint_derivative_eq hu hDu i hweak hκm hκi hH]
  rw [integral_horizontalMollify_mul_eq_adj hQ hκm hκi hDum hDu hHm hHB]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => mul_comm _ _

/-! ### Orbit calculus of the mollified field

The orbit of `S_ε u = horizontalMollify κ u` is the reflected convolution of `κ` with the
orbit of `u`, so it is smooth on every orbit whose `u`-orbit is locally integrable. -/

/-- Directional derivative of a convolution with a `C¹` compactly supported left factor. -/
private theorem fderiv_convolution_apply_kernel {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) {g : Vec d → ℝ} (hg : LocallyIntegrable g volume)
    (w v : Vec d) :
    (fderiv ℝ ψ ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d),
        volume] g) w v =
      ((fun x => fderiv ℝ ψ x v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) w := by
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL
      (Vec d) (fderiv ℝ ψ t) (g (w - t))) volume :=
    (hψc.fderiv ℝ).convolutionExists_left
      ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL (Vec d))
      (hψ.continuous_fderiv (by simp)) hg w
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hint v]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => rfl

/-- Moving one coordinate derivative through the reflected convolution gives one sign. -/
private theorem coordinateDerivative_conv_neg {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {g : Vec d → ℝ}
    (hg : LocallyIntegrable g volume) (c : ℝ) (i : Fin d) (y : Vec d) :
    coordinateDerivative i (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y =
      -(c * ((coordinateDerivative i ψ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-y)) := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (mod_cast le_top)
  have hK := hψc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hψ1 hg (-y)
  have hneg : HasFDerivAt (fun x : Vec d => -x) (-ContinuousLinearMap.id ℝ (Vec d)) y :=
    (hasFDerivAt_id y).fun_neg
  have hfd : fderiv ℝ (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y = _ :=
    ((hK.comp y hneg).const_mul c).fderiv
  have hD := fderiv_convolution_apply_kernel hψ1 hψc hg (-y) (unitVector i)
  show fderiv ℝ (fun x => c * (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (-x)) y
      (unitVector i) =
    -(c * ((fun x => fderiv ℝ ψ x (unitVector i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] g) (-y))
  rw [hfd, ← hD]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
  ring

/-- The orbit of the mollified field is the reflected convolution with the kernel. -/
private theorem contDiff_orbit_mollified_of_locallyIntegrable {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) {u : FieldPair d → ℝ}
    (ω : FieldPair d) (hloc : LocallyIntegrable (fun x : Vec d => u (translate (-x) ω)) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (orbit (horizontalMollify κ u) ω) := by
  have hc := hκc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hloc
  have heq : orbit (horizontalMollify κ u) ω = fun y : Vec d =>
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => orbit u ω (-x))) (-y) :=
    funext (orbit_horizontalMollify_eq_convolution κ u ω)
  rw [heq]
  exact hc.comp contDiff_id.neg

/-- The coordinate derivative of the mollified orbit, written as a convolution with the derivative
of the kernel. -/
private theorem coordinateDerivative_orbit_mollified {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) (i : Fin d) {u : FieldPair d → ℝ}
    (ω : FieldPair d) (hloc : LocallyIntegrable (fun x : Vec d => u (translate (-x) ω)) volume)
    (y : Vec d) :
    coordinateDerivative i (orbit (horizontalMollify κ u) ω) y =
      -(∫ t : Vec d, coordinateDerivative i κ t * u (translate (y + t) ω) ∂volume) := by
  have heq : orbit (horizontalMollify κ u) ω = fun z : Vec d =>
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun x => orbit u ω (-x))) (-z) :=
    funext (orbit_horizontalMollify_eq_convolution κ u ω)
  have hloc' : LocallyIntegrable (fun x : Vec d => orbit u ω (-x)) volume := hloc
  have h := coordinateDerivative_conv_neg hκ hκc hloc' 1 i y
  simp only [one_mul] at h
  have hconv : ((coordinateDerivative i κ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun x => orbit u ω (-x))) (-y) =
        ∫ t : Vec d, coordinateDerivative i κ t * u (translate (y + t) ω) ∂volume := by
    rw [convolution_lsmul]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun t => ?_
    have hneg : -(-y - t) = y + t := by abel
    show coordinateDerivative i κ t • orbit u ω (-(-y - t)) =
      coordinateDerivative i κ t * u (translate (y + t) ω)
    simp only [orbit, hneg, smul_eq_mul]
  rw [heq, h, hconv]

/-- A bounded measurable observable has only integrable orbit-line intensities: for almost every
environment, the observable is integrable along every bounded window of the orbit. -/
private theorem ae_integrableOn_orbit {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q)
    {T : Vec d → Vec d} (hT : Measurable T) {S : Set (Vec d)} (hSf : volume S ≠ ⊤) :
    ∀ᵐ ω ∂Q, IntegrableOn (fun x => u (translate (T x) ω)) S := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSf
  have hFm : Measurable (fun p : FieldPair d × Vec d => u (translate (T p.2) p.1)) :=
    hum.comp (Probability.continuous_translate.measurable.comp
      ((hT.comp measurable_snd).prodMk measurable_fst))
  have hFint : Integrable (fun p : FieldPair d × Vec d => u (translate (T p.2) p.1))
      (Q.prod (volume.restrict S)) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · exact integrable_comp_translate hQ hui (T x)
    · refine Integrable.congr (integrable_const (∫ ω, ‖u ω‖ ∂Q))
        (Filter.Eventually.of_forall fun x => ?_)
      show (∫ ω, ‖u ω‖ ∂Q) = ∫ ω, ‖u (translate (T x) ω)‖ ∂Q
      exact (Probability.integral_translate Q hQ (T x) (fun η => ‖u η‖) hum.norm).symm
  exact hFint.prod_right_ae

/-- A function whose restrictions to all closed balls are integrable is locally integrable. -/
private theorem locallyIntegrable_of_integrableOn_closedBall {g : Vec d → ℝ}
    (h : ∀ n : ℕ, IntegrableOn g (Metric.closedBall (0 : Vec d) n)) :
    LocallyIntegrable g volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hk.isBounded
  refine (h ⌈C⌉₊).mono_set fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hC x hx).trans (Nat.le_ceil C)

/-- For almost every environment, the mollification-relevant orbit of `u` is locally integrable. -/
private theorem ae_locallyIntegrable_orbit {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    ∀ᵐ ω ∂Q, LocallyIntegrable (fun x : Vec d => u (translate (-x) ω)) volume := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂Q, IntegrableOn (fun x : Vec d => u (translate (-x) ω))
      (Metric.closedBall (0 : Vec d) n) := fun n =>
    ae_integrableOn_orbit hQ hum hui (T := fun x : Vec d => -x) measurable_neg
      (measure_closedBall_lt_top.ne)
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact locallyIntegrable_of_integrableOn_closedBall fun n => hω n

/-! ### Derivative bounds and measurability along orbits -/

/-- The orbit of the mollified field is differentiable with a bound by the translated
observable's ball-restricted absolute mass. -/
private theorem abs_coordinateDerivative_orbit_mollified_le {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) (i : Fin d) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t : Vec d, |coordinateDerivative i κ t| ≤ C)
    (hsupp : ∀ t : Vec d, 1 < ‖t‖ → coordinateDerivative i κ t = 0)
    {u : FieldPair d → ℝ} (ω : FieldPair d)
    (hloc : LocallyIntegrable (fun x : Vec d => u (translate (-x) ω)) volume)
    (hint : Integrable (fun z : Vec d => (Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖) z) volume) {y : Vec d} (hy : ‖y‖ ≤ 1) :
    |coordinateDerivative i (orbit (horizontalMollify κ u) ω) y| ≤
      C * ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
        (fun z => ‖u (translate z ω)‖) z ∂volume := by
  rw [coordinateDerivative_orbit_mollified hκ hκc i ω hloc y, abs_neg, ← Real.norm_eq_abs]
  have hshift : (∫ t : Vec d, C * (Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖) (y + t) ∂volume) =
      C * ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
        (fun z => ‖u (translate z ω)‖) z ∂volume := by
    rw [integral_const_mul]
    congr 1
    exact integral_add_left_eq_self (fun z : Vec d => (Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖) z) y
  rw [← hshift]
  refine norm_integral_le_of_norm_le ((hint.comp_add_left y).const_mul C)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_eq_abs (coordinateDerivative i κ t)]
  by_cases ht : 1 < ‖t‖
  · rw [hsupp t ht, abs_zero, zero_mul]
    exact mul_nonneg hC0 (Set.indicator_nonneg (fun z _ => norm_nonneg _) _)
  · push_neg at ht
    have hmem : y + t ∈ Metric.closedBall (0 : Vec d) 2 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_add_le y t).trans (by linarith)
    rw [Set.indicator_of_mem hmem]
    exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _)

/-- The horizontal derivative of the mollified field, measured along orbits, is almost everywhere
measurable: it is an almost everywhere limit of measurable difference quotients. -/
private theorem aemeasurable_orbit_derivative_mollified {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hκc : HasCompactSupport κ) (i : Fin d) {u : FieldPair d → ℝ}
    (hum : Measurable u) (hui : Integrable u Q) :
    AEMeasurable (fun ω => coordinateDerivative i (orbit (horizontalMollify κ u) ω) 0) Q := by
  have hψm : Measurable (horizontalMollify κ u) :=
    measurable_horizontalMollify κ hκ.continuous.measurable hum
  have hmx : ∀ x : Vec d, Measurable (fun ω => orbit (horizontalMollify κ u) ω x) :=
    fun x => hψm.comp (Probability.measurable_translate x)
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by
      change 0 < 1 / ((n : ℝ) + 1)
      positivity
  have hfm : ∀ n : ℕ, AEMeasurable (fun ω => (1 / ((n : ℝ) + 1))⁻¹ *
      (orbit (horizontalMollify κ u) ω ((1 / ((n : ℝ) + 1)) • unitVector i) -
        orbit (horizontalMollify κ u) ω 0)) Q := fun n =>
    (((hmx _).sub (hmx 0)).const_mul _).aemeasurable
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))⁻¹ *
      (orbit (horizontalMollify κ u) ω ((1 / ((n : ℝ) + 1)) • unitVector i) -
        orbit (horizontalMollify κ u) ω 0)) atTop
      (𝓝 (coordinateDerivative i (orbit (horizontalMollify κ u) ω) 0)) := by
    filter_upwards [ae_locallyIntegrable_orbit hQ hum hui] with ω hω
    have hdiff := (contDiff_orbit_mollified_of_locallyIntegrable hκ hκc ω hω).differentiable
      (by simp)
    have hd : HasDerivAt (fun t : ℝ => orbit (horizontalMollify κ u) ω (t • unitVector i))
        (coordinateDerivative i (orbit (horizontalMollify κ u) ω) ((0 : ℝ) • unitVector i)) 0 :=
      hasDerivAt_orbit_line i (horizontalMollify κ u) ω 0 (hdiff _)
    simp only [zero_smul] at hd
    have h := hd.tendsto_slope_zero_right.comp hs
    simpa only [Function.comp_def, zero_add, smul_eq_mul, zero_smul] using h
  exact (aemeasurable_of_tendsto_metrizable_ae' hfm hlim)

/-- Integration by parts along horizontal orbits, tested against a bounded orbit core. The function
`h` has differentiable orbits whose coordinate derivative is dominated by an integrable function `K`
on the unit window of the orbit. -/
theorem integral_orbit_derivative_mul_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} (i : Fin d) {h : FieldPair d → ℝ} (hhm : Measurable h)
    (hhi : Integrable h Q) {K : FieldPair d → ℝ} (hKi : Integrable K Q)
    (hdiff : ∀ᵐ ω ∂Q, ∀ x : Vec d, DifferentiableAt ℝ (orbit h ω) x)
    (hbd : ∀ᵐ ω ∂Q, ∀ s : ℝ, |s| ≤ 1 →
      |coordinateDerivative i (orbit h ω) (s • unitVector i)| ≤ K ω)
    (hDm : AEStronglyMeasurable (fun ω => coordinateDerivative i (orbit h ω) 0) Q)
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, coordinateDerivative i (orbit h ω) 0 * H ω ∂Q) =
      -(∫ ω, h ω * horizontalDerivative i H ω ∂Q) := by
  obtain ⟨B, -, hB⟩ := hH.bound_orbit
  obtain ⟨C, -, hC⟩ := hH.bound_derivative i
  have hHm : Measurable H := hH.1
  have hHB : ∀ ω, |H ω| ≤ B := fun ω => by simpa only [orbit_zero] using hB ω 0
  have hHdiff : ∀ ω (x : Vec d), DifferentiableAt ℝ (orbit H ω) x :=
    fun ω x => ((hH.2.1 ω).differentiable (by simp)) x
  -- Derivative of the first representation at the origin.
  have hΦd : HasDerivAt (fun s : ℝ => ∫ ω, h (translate (s • unitVector i) ω) * H ω ∂Q)
      (∫ ω, coordinateDerivative i (orbit h ω) ((0 : ℝ) • unitVector i) * H ω ∂Q) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Q)
      (F := fun s ω => h (translate (s • unitVector i) ω) * H ω)
      (F' := fun s ω => coordinateDerivative i (orbit h ω) (s • unitVector i) * H ω)
      (x₀ := (0 : ℝ)) (bound := fun ω => K ω * B) (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun s =>
        ((hhm.comp (Probability.measurable_translate _)).mul hHm).aestronglyMeasurable
    · have hz : (fun ω => h (translate ((0 : ℝ) • unitVector i) ω) * H ω) = fun ω => h ω * H ω := by
        funext ω
        simp only [zero_smul, translate_zero]
      show Integrable (fun ω => h (translate ((0 : ℝ) • unitVector i) ω) * H ω) Q
      rw [hz]
      exact hhi.mul_bdd (c := B) hHm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hHB ω)
    · have hz : (fun ω => coordinateDerivative i (orbit h ω) ((0 : ℝ) • unitVector i) * H ω) =
          fun ω => coordinateDerivative i (orbit h ω) 0 * H ω := by
        funext ω
        simp only [zero_smul]
      show AEStronglyMeasurable (fun ω => coordinateDerivative i (orbit h ω) ((0 : ℝ) • unitVector i) * H ω) Q
      rw [hz]
      exact hDm.mul hHm.aestronglyMeasurable
    · filter_upwards [hbd] with ω hω
      intro s hs
      rw [Metric.mem_ball, dist_zero_right] at hs
      have hs' : |s| ≤ 1 := by
        rw [← Real.norm_eq_abs]
        exact hs.le
      have h1 := hω s hs'
      have h2 := hHB ω
      show ‖coordinateDerivative i (orbit h ω) (s • unitVector i) * H ω‖ ≤ K ω * B
      rw [norm_mul, Real.norm_eq_abs (coordinateDerivative i (orbit h ω) (s • unitVector i))]
      exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    · exact hKi.mul_const B
    · filter_upwards [hdiff] with ω hω
      intro s _
      exact (hasDerivAt_orbit_line i h ω s (hω _)).mul_const (H ω)
  -- Derivative of the second representation, the same integral after stationarity.
  have hΦΨ : ∀ s : ℝ, (∫ ω, h (translate (s • unitVector i) ω) * H ω ∂Q) =
      ∫ ω, h ω * orbit H ω ((-s) • unitVector i) ∂Q := by
    intro s
    have hcancel : ∀ ω : FieldPair d,
        translate ((-s) • unitVector i) (translate (s • unitVector i) ω) = ω := by
      intro ω
      rw [translate_add, ← add_smul, neg_add_cancel, zero_smul, translate_zero]
    have hm : Measurable (fun η : FieldPair d => h η * H (translate ((-s) • unitVector i) η)) :=
      hhm.mul (hHm.comp (Probability.measurable_translate _))
    have hst := Probability.integral_translate Q hQ (s • unitVector i)
      (fun η => h η * H (translate ((-s) • unitVector i) η)) hm
    simp only [hcancel] at hst
    exact hst
  have hΨd : HasDerivAt (fun s : ℝ => ∫ ω, h ω * orbit H ω ((-s) • unitVector i) ∂Q)
      (∫ ω, h ω * (coordinateDerivative i (orbit H ω) ((-(0 : ℝ)) • unitVector i) * -1) ∂Q) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Q)
      (F := fun s ω => h ω * orbit H ω ((-s) • unitVector i))
      (F' := fun s ω => h ω * (coordinateDerivative i (orbit H ω) ((-s) • unitVector i) * -1))
      (x₀ := (0 : ℝ)) (bound := fun ω => |h ω| * C) (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun s =>
        (hhm.mul (hHm.comp (Probability.measurable_translate _))).aestronglyMeasurable
    · exact hhi.mul_bdd (c := B) ((hHm.comp (Probability.measurable_translate _)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hB ω _)
    · have hz : (fun ω => h ω * (coordinateDerivative i (orbit H ω) ((-(0 : ℝ)) • unitVector i) * -1)) =
          fun ω => h ω * (horizontalDerivative i H ω * -1) := by
        funext ω
        simp only [neg_zero, zero_smul]
        rfl
      show AEStronglyMeasurable (fun ω => h ω * (coordinateDerivative i (orbit H ω)
        ((-(0 : ℝ)) • unitVector i) * -1)) Q
      rw [hz]
      exact hhm.aestronglyMeasurable.mul
        (((hH.measurable_derivative i).mul_const (-1)).aestronglyMeasurable)
    · filter_upwards with ω
      intro s _
      show ‖h ω * (coordinateDerivative i (orbit H ω) ((-s) • unitVector i) * -1)‖ ≤ |h ω| * C
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_one, mul_one]
      exact mul_le_mul_of_nonneg_left (hC ω _) (abs_nonneg _)
    · exact (hhi.abs.mul_const C)
    · filter_upwards with ω
      intro s _
      exact (((hasDerivAt_orbit_line i H ω (-s) (hHdiff ω _)).comp s
        (hasDerivAt_neg s)).const_mul (h ω))
  have hΦd' : HasDerivAt (fun s : ℝ => ∫ ω, h ω * orbit H ω ((-s) • unitVector i) ∂Q)
      (∫ ω, coordinateDerivative i (orbit h ω) ((0 : ℝ) • unitVector i) * H ω ∂Q) 0 := by
    have hfun : (fun s : ℝ => ∫ ω, h (translate (s • unitVector i) ω) * H ω ∂Q) =
        fun s : ℝ => ∫ ω, h ω * orbit H ω ((-s) • unitVector i) ∂Q := funext hΦΨ
    rw [← hfun]
    exact hΦd
  have key := hΦd'.unique hΨd
  have hsimp : (∫ ω, h ω * (coordinateDerivative i (orbit H ω) ((-(0 : ℝ)) • unitVector i) * -1)
      ∂Q) = -(∫ ω, h ω * horizontalDerivative i H ω ∂Q) := by
    rw [← integral_neg]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [neg_zero, zero_smul]
    show h ω * (coordinateDerivative i (orbit H ω) 0 * -1) = -(h ω * coordinateDerivative i (orbit H ω) 0)
    ring
  have hk1 : (∫ ω, coordinateDerivative i (orbit h ω) ((0 : ℝ) • unitVector i) * H ω ∂Q) =
      ∫ ω, coordinateDerivative i (orbit h ω) 0 * H ω ∂Q := by
    simp only [zero_smul]
  rw [← hk1, key, hsimp]

/-! ### Window masses and the identification of the orbit derivative -/

/-- The windowed absolute observable is integrable on the ball of radius two, for almost every
environment. -/
private theorem ae_window_integrable {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    ∀ᵐ ω ∂Q, Integrable ((Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖)) volume := by
  filter_upwards [ae_integrableOn_orbit hQ hum hui (T := fun x : Vec d => x) measurable_id
    (S := Metric.closedBall (0 : Vec d) 2) measure_closedBall_lt_top.ne] with ω hω
  exact (integrable_indicator_iff measurableSet_closedBall).mpr (Integrable.norm hω)

/-- The integral of a translated norm over a fixed set is integrable in the environment. -/
private theorem integrable_norm_translate_restrict {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hum : Measurable u)
    (hui : Integrable u Q) {S : Set (Vec d)} (hSf : volume S ≠ ⊤) :
    Integrable (fun ω => ∫ z : Vec d, ‖u (translate z ω)‖ ∂(volume.restrict S)) Q := by
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSf
  have hFm : Measurable (fun p : FieldPair d × Vec d => ‖u (translate p.2 p.1)‖) :=
    (hum.comp measurable_translate_pair).norm
  have hFint : Integrable (fun p : FieldPair d × Vec d => ‖u (translate p.2 p.1)‖)
      (Q.prod (volume.restrict S)) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
    · exact integrable_comp_translate hQ hui.norm z
    · refine Integrable.congr (integrable_const (∫ ω, ‖u ω‖ ∂Q))
        (Filter.Eventually.of_forall fun z => ?_)
      show (∫ ω, ‖u ω‖ ∂Q) = ∫ ω, ‖‖u (translate z ω)‖‖ ∂Q
      simp only [norm_norm]
      exact (Probability.integral_translate Q hQ z (fun η => ‖u η‖) hum.norm).symm
  exact hFint.integral_prod_left

/-- The window mass of the observable is integrable in the environment. -/
private theorem integrable_windowMass {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    Integrable (fun ω => ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖) z ∂volume) Q := by
  have hfun : (fun ω => ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
      (fun z => ‖u (translate z ω)‖) z ∂volume) =
      fun ω => ∫ z : Vec d, ‖u (translate z ω)‖ ∂(volume.restrict (Metric.closedBall (0 : Vec d) 2)) := by
    funext ω
    exact integral_indicator measurableSet_closedBall
  rw [hfun]
  exact integrable_norm_translate_restrict hQ hum hui measure_closedBall_lt_top.ne

/-- The norm of a unit coordinate vector is one. -/
private theorem norm_unitVector_eq_one (i : Fin d) : ‖unitVector i‖ = 1 := by
  unfold unitVector
  rw [Pi.norm_single, norm_one]

/-- Almost every environment has differentiable mollified orbit, with a uniform window bound on the
coordinate derivative in the unit window. -/
private theorem ae_mollified_orbit_bounds {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {u : FieldPair d → ℝ}
    (hum : Measurable u) (hui : Integrable u Q) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂Q,
      (∀ x : Vec d, DifferentiableAt ℝ
        (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) x) ∧
      ∀ s : ℝ, |s| ≤ 1 →
        |coordinateDerivative i (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω)
          (s • unitVector i)| ≤ C * ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
            (fun z => ‖u (translate z ω)‖) z ∂volume := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_coordinateDerivative_kernel i hε hε1
  refine ⟨C, hC0, ?_⟩
  filter_upwards [ae_locallyIntegrable_orbit hQ hum hui, ae_window_integrable hQ hum hui] with
    ω hω hW
  refine ⟨fun x => ((contDiff_orbit_mollified_of_locallyIntegrable (contDiff_unitMassScaled ε)
    (hasCompactSupport_unitMassScaled hε hε1) ω hω).differentiable (by simp)) x, fun s hs => ?_⟩
  have hnorm : ‖s • unitVector i‖ ≤ 1 := by
    rw [norm_smul, norm_unitVector_eq_one, mul_one, Real.norm_eq_abs]
    exact hs
  exact abs_coordinateDerivative_orbit_mollified_le (contDiff_unitMassScaled ε)
    (hasCompactSupport_unitMassScaled hε hε1) i hC0 hC
    (fun t ht => coordinateDerivative_kernel_eq_zero i hε hε1 ht) ω hω hW hnorm

/-- A class in `L¹` that pairs to zero with every bounded orbit core vanishes almost everywhere. -/
private theorem ae_eq_zero_of_pairing_zero {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {q : FieldPair d → ℝ} (hq : Integrable q Q)
    (hpair : ∀ H : FieldPair d → ℝ, IsHorizontalTest H → (∫ ω, q ω * H ω ∂Q) = 0) :
    ∀ᵐ ω ∂Q, q ω = 0 := by
  have hg0 : Integrable.toL1 q hq = 0 :=
    eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ (Integrable.toL1 q hq) (fun H hH => by
      refine (integral_congr_ae ?_).trans (hpair H hH)
      filter_upwards [Integrable.coeFn_toL1 hq] with ω hω
      rw [hω])
  filter_upwards [Integrable.coeFn_toL1 hq, Lp.coeFn_zero ℝ 1 Q] with ω hω hz
  have hzω : (Integrable.toL1 q hq) ω = 0 := (congrArg (fun z : Lp ℝ 1 Q => z ω) hg0).trans hz
  exact hω.symm.trans hzω

/-- A product of an integrable function with a bounded orbit core is integrable. -/
private theorem integrable_mul_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {f H : FieldPair d → ℝ} (hf : Integrable f Q) (hH : IsHorizontalTest H) :
    Integrable (fun ω => f ω * H ω) Q := by
  obtain ⟨B, -, hB⟩ := hH.bound_orbit
  exact hf.mul_bdd (c := B) hH.1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      simpa only [orbit_zero] using hB ω 0)

/-- The orbit derivative of the mollified field equals the mollified weak gradient, almost surely.
This is the identification of the classical derivative with the mollified `Du`, obtained by pairing
against bounded orbit cores. -/
theorem ae_orbit_derivative_mollify_eq {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {u Du : FieldPair d → ℝ}
    (hum : Measurable u) (hui : Integrable u Q) (hDum : Measurable Du) (hDui : Integrable Du Q)
    (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q)) :
    ∀ᵐ ω ∂Q, coordinateDerivative i
      (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 =
        horizontalMollify (unitMassScaledMollifier d ε) Du ω := by
  obtain ⟨C, hC0, hbd⟩ := ae_mollified_orbit_bounds hQ hε hε1 hum hui i
  have hκcont : Continuous (unitMassScaledMollifier d ε) :=
    (contDiff_unitMassScaled ε).continuous
  have hκm : Measurable (unitMassScaledMollifier d ε) := hκcont.measurable
  have hκi : Integrable (unitMassScaledMollifier d ε) volume :=
    hκcont.integrable_of_hasCompactSupport (hasCompactSupport_unitMassScaled hε hε1)
  have hψm : Measurable (horizontalMollify (unitMassScaledMollifier d ε) u) :=
    measurable_horizontalMollify _ hκm hum
  have hψi : Integrable (horizontalMollify (unitMassScaledMollifier d ε) u) Q :=
    (integrable_kernel_translate hQ hκm hκi hum hui).integral_prod_left
  have hsi : Integrable (horizontalMollify (unitMassScaledMollifier d ε) Du) Q :=
    (integrable_kernel_translate hQ hκm hκi hDum hDui).integral_prod_left
  have hKi := (integrable_windowMass hQ hum hui).const_mul C
  have hD0 : Integrable (fun ω => coordinateDerivative i
      (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0) Q := by
    refine Integrable.mono' hKi
      (aemeasurable_orbit_derivative_mollified hQ (contDiff_unitMassScaled ε)
        (hasCompactSupport_unitMassScaled hε hε1) i hum hui).aestronglyMeasurable ?_
    filter_upwards [hbd] with ω hω
    have h0 := (hω.2 0 (by simp))
    rw [zero_smul] at h0
    rw [Real.norm_eq_abs]
    exact h0
  have hpsi : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, coordinateDerivative i (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 *
        H ω ∂Q) = ∫ ω, horizontalMollify (unitMassScaledMollifier d ε) Du ω * H ω ∂Q := by
    intro H hH
    have hIBP := integral_orbit_derivative_mul_core (hQ := hQ) i hψm hψi
      (K := fun ω => C * ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
        (fun z => ‖u (translate z ω)‖) z ∂volume) hKi
      (Filter.Eventually.mono hbd fun ω hω => hω.1)
      (Filter.Eventually.mono hbd fun ω hω s hs => hω.2 s hs)
      (aemeasurable_orbit_derivative_mollified hQ (contDiff_unitMassScaled ε)
        (hasCompactSupport_unitMassScaled hε hε1) i hum hui).aestronglyMeasurable hH
    have hP8 := integral_horizontalMollify_mul_derivative hQ hum hui hDum hDui i hweak hκm hκi hH
    rw [hIBP, hP8, neg_neg]
  have hq : Integrable (fun ω => coordinateDerivative i
      (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 -
        horizontalMollify (unitMassScaledMollifier d ε) Du ω) Q := hD0.sub hsi
  have hzero := ae_eq_zero_of_pairing_zero hQ hq (fun H hH => by
    have h := hpsi H hH
    have hsplit : (∫ ω, (coordinateDerivative i
        (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 -
          horizontalMollify (unitMassScaledMollifier d ε) Du ω) * H ω ∂Q) =
        (∫ ω, coordinateDerivative i
          (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 * H ω ∂Q) -
        ∫ ω, horizontalMollify (unitMassScaledMollifier d ε) Du ω * H ω ∂Q := by
      rw [← integral_sub (integrable_mul_core hD0 hH) (integrable_mul_core hsi hH)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => sub_mul _ _ _
    rw [hsplit, h, sub_self])
  filter_upwards [hzero] with ω hω
  exact sub_eq_zero.mp hω

/-- A bounded continuous profile composed with an `L¹`-convergent sequence converges in the integral
against an integrable weight. -/
private theorem tendsto_integral_comp_sub_mul {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {a : ℕ → FieldPair d → ℝ} {a0 : FieldPair d → ℝ} (hm : ∀ n, AEStronglyMeasurable (a n) Q)
    (hm0 : AEStronglyMeasurable a0 Q)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => a n ω - a0 ω) 1 Q) atTop (𝓝 0))
    {φ : ℝ → ℝ} (hφc : Continuous φ) {M : ℝ} (hφM : ∀ x, |φ x| ≤ M)
    {w : FieldPair d → ℝ} (hw : Integrable w Q) :
    Tendsto (fun n => ∫ ω, (φ (a n ω) - φ (a0 ω)) * w ω ∂Q) atTop (𝓝 0) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  have hconv' : Tendsto (fun k => eLpNorm (fun ω => a (ns k) ω - a0 ω) 1 Q) atTop (𝓝 0) :=
    hconv.comp hns
  obtain ⟨ms, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    hconv').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖(φ (a (ns (ms k)) ω) - φ (a0 ω)) * w ω‖ ≤ 2 * M * ‖w ω‖ := by
    intro k
    refine Filter.Eventually.of_forall fun ω => ?_
    have h2 : |φ (a (ns (ms k)) ω) - φ (a0 ω)| ≤ 2 * M := by
      have h3 := abs_sub (φ (a (ns (ms k)) ω)) (φ (a0 ω))
      linarith [hφM (a (ns (ms k)) ω), hφM (a0 ω)]
    rw [norm_mul, Real.norm_eq_abs (φ (a (ns (ms k)) ω) - φ (a0 ω))]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun k => (φ (a (ns (ms k)) ω) - φ (a0 ω)) * w ω) atTop (𝓝 0) := by
    filter_upwards [hae] with ω hω
    have h1 : Tendsto (fun k => φ (a (ns (ms k)) ω)) atTop (𝓝 (φ (a0 ω))) :=
      (hφc.tendsto _).comp hω
    simpa using (h1.sub_const (φ (a0 ω))).mul_const (w ω)
  have hdct := tendsto_integral_of_dominated_convergence (μ := Q) (fun ω => 2 * M * ‖w ω‖)
    (fun k => ((hφc.comp_aestronglyMeasurable (hm (ns (ms k)))).sub
      (hφc.comp_aestronglyMeasurable hm0)).mul hw.aestronglyMeasurable)
    (hw.norm.const_mul (2 * M)) hbd hlim
  simpa using hdct

/-- A bounded sequence converging in `Lᵖ` against an integrable weight converges in the integral. -/
private theorem tendsto_integral_mul_of_bounded {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {a : ℕ → FieldPair d → ℝ} {a0 : FieldPair d → ℝ} {p : ℝ≥0∞}
    (hp : p ≠ 0) (hm : ∀ n, AEStronglyMeasurable (a n) Q) (hm0 : AEStronglyMeasurable a0 Q)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => a n ω - a0 ω) p Q) atTop (𝓝 0))
    {M : ℝ} (hM : ∀ n, ∀ᵐ ω ∂Q, |a n ω| ≤ M)
    {w : FieldPair d → ℝ} (hw : Integrable w Q) :
    Tendsto (fun n => ∫ ω, a n ω * w ω ∂Q) atTop (𝓝 (∫ ω, a0 ω * w ω ∂Q)) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  have hconv' : Tendsto (fun k => eLpNorm (fun ω => a (ns k) ω - a0 ω) p Q) atTop (𝓝 0) :=
    hconv.comp hns
  obtain ⟨ms, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp
    hconv').exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖a (ns (ms k)) ω * w ω‖ ≤ M * ‖w ω‖ := by
    intro k
    filter_upwards [hM (ns (ms k))] with ω hω
    rw [norm_mul, Real.norm_eq_abs (a (ns (ms k)) ω)]
    exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun k => a (ns (ms k)) ω * w ω) atTop (𝓝 (a0 ω * w ω)) := by
    filter_upwards [hae] with ω hω
    exact hω.mul_const (w ω)
  exact tendsto_integral_of_dominated_convergence (μ := Q) (fun ω => M * ‖w ω‖)
    (fun k => (hm (ns (ms k))).mul hw.aestronglyMeasurable) (hw.norm.const_mul M) hbd hlim

/-- A bounded measurable factor times an integrable function, times a horizontal core, is
integrable. -/
private theorem integrable_bdd_mul_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {c v H : FieldPair d → ℝ} {M : ℝ} (hc : Measurable c) (hcM : ∀ ω, |c ω| ≤ M)
    (hv : Integrable v Q) (hH : IsHorizontalTest H) :
    Integrable (fun ω => c ω * v ω * H ω) Q :=
  integrable_mul_core (hv.bdd_mul (c := M) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hcM ω)) hH

/-! ### Lipschitz profiles and the chain identity on cores -/

/-- A profile with bounded derivative is Lipschitz. -/
private theorem abs_sub_le_of_deriv_bound {g : ℝ → ℝ} (hg : Differentiable ℝ g) {L : ℝ}
    (hL : ∀ x, |deriv g x| ≤ L) (x y : ℝ) : |g x - g y| ≤ L * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.univ) (C := L)
    (fun z _ => hg z) (fun z _ => by rw [Real.norm_eq_abs]; exact hL z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- The composition of a Lipschitz profile with an integrable observable is integrable. -/
private theorem integrable_comp_of_lipschitz {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L : ℝ} (hL : ∀ x, |deriv g x| ≤ L)
    {v : FieldPair d → ℝ} (hvm : Measurable v) (hvi : Integrable v Q) :
    Integrable (fun ω => g (v ω)) Q := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  refine Integrable.mono' ((integrable_const |g 0|).add (hvi.abs.const_mul L))
    (hg.continuous.measurable.comp hvm).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := abs_sub_le_of_deriv_bound hgd hL (v ω) 0
  rw [sub_zero] at h1
  have h2 := abs_add_le (g (v ω) - g 0) (g 0)
  rw [sub_add_cancel] at h2
  rw [Real.norm_eq_abs]
  show |g (v ω)| ≤ |g 0| + L * |v ω|
  linarith

/-- The chain rule for a `C¹` profile composed with a differentiable real function of a vector. -/
private theorem coordinateDerivative_comp_real {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {φ : Vec d → ℝ} {x : Vec d} (hφ : DifferentiableAt ℝ φ x) (i : Fin d) :
    coordinateDerivative i (fun y => g (φ y)) x = deriv g (φ x) * coordinateDerivative i φ x := by
  have h1 : HasFDerivAt (g ∘ φ) (deriv g (φ x) • fderiv ℝ φ x) x :=
    HasDerivAt.comp_hasFDerivAt x (hg (φ x)).hasDerivAt hφ.hasFDerivAt
  show fderiv ℝ (fun y => g (φ y)) x (unitVector i) = deriv g (φ x) * fderiv ℝ φ x (unitVector i)
  rw [show (fun y => g (φ y)) = g ∘ φ from rfl, h1.fderiv]
  simp [smul_eq_mul]

/-- The integrals of the norms of an `L¹` sequence tending to zero tend to zero. -/
private theorem tendsto_integral_norm_of_eLpNorm_one {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {e : ℕ → FieldPair d → ℝ} (he : ∀ n, Integrable (e n) Q)
    (hconv : Tendsto (fun n => eLpNorm (e n) 1 Q) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ‖e n ω‖ ∂Q) atTop (𝓝 0) := by
  have h1 : ∀ n, (∫ ω, ‖e n ω‖ ∂Q) = (eLpNorm (e n) 1 Q).toReal := fun n => by
    rw [eLpNorm_one_eq_lintegral_enorm (he n).aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm (he n).aestronglyMeasurable]
  simp only [h1]
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  simpa only [Function.comp_def, ENNReal.toReal_zero] using h2

/-- A convergence-in-`L¹` version of the bound: if `|F_n| ≤ K |e_n|` and `e_n → 0` in `L¹`, then
`∫ F_n → 0`. -/
private theorem tendsto_integral_zero_of_abs_le {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {F e : ℕ → FieldPair d → ℝ} {K : ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) Q)
    (he : ∀ n, Integrable (e n) Q) (hFe : ∀ n, ∀ᵐ ω ∂Q, |F n ω| ≤ K * |e n ω|)
    (hconv : Tendsto (fun n => eLpNorm (e n) 1 Q) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, F n ω ∂Q) atTop (𝓝 0) := by
  have hbound : ∀ n, ‖∫ ω, F n ω ∂Q‖ ≤ |K| * ∫ ω, ‖e n ω‖ ∂Q := by
    intro n
    have hint : Integrable (fun ω => K * |e n ω|) Q := ((he n).abs).const_mul K
    have hpt : ∀ᵐ ω ∂Q, ‖F n ω‖ ≤ K * |e n ω| := by
      filter_upwards [hFe n] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    have h1 : ‖∫ ω, F n ω ∂Q‖ ≤ ∫ ω, K * |e n ω| ∂Q := norm_integral_le_of_norm_le hint hpt
    have h2 : (∫ ω, K * |e n ω| ∂Q) = K * ∫ ω, ‖e n ω‖ ∂Q := by
      simp only [integral_const_mul, Real.norm_eq_abs]
    calc ‖∫ ω, F n ω ∂Q‖ ≤ ∫ ω, K * |e n ω| ∂Q := h1
      _ = K * ∫ ω, ‖e n ω‖ ∂Q := h2
      _ ≤ |K| * ∫ ω, ‖e n ω‖ ∂Q :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (integral_nonneg fun ω => norm_nonneg _)
  refine squeeze_zero_norm' (Filter.Eventually.of_forall hbound) ?_
  simpa using (tendsto_integral_norm_of_eLpNorm_one he hconv).const_mul |K|

/-- The chain identity for the mollified field, tested against a bounded orbit core. The orbit
derivative of `g ∘ S_ε u` is `g'(S_ε u) · S_ε Du`, and integration by parts along the orbits gives
the identity. -/
theorem integral_chain_mollify_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L : ℝ} (hL : ∀ x, |deriv g x| ≤ L)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {u Du : FieldPair d → ℝ}
    (hum : Measurable u) (hui : Integrable u Q) (hDum : Measurable Du) (hDui : Integrable Du Q)
    (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q))
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, g (horizontalMollify (unitMassScaledMollifier d ε) u ω) * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, deriv g (horizontalMollify (unitMassScaledMollifier d ε) u ω) *
        horizontalMollify (unitMassScaledMollifier d ε) Du ω * H ω ∂Q) := by
  obtain ⟨C, hC0, hbd⟩ := ae_mollified_orbit_bounds hQ hε hε1 hum hui i
  have hκcont : Continuous (unitMassScaledMollifier d ε) := (contDiff_unitMassScaled ε).continuous
  have hκm : Measurable (unitMassScaledMollifier d ε) := hκcont.measurable
  have hκi : Integrable (unitMassScaledMollifier d ε) volume :=
    hκcont.integrable_of_hasCompactSupport (hasCompactSupport_unitMassScaled hε hε1)
  have hψm : Measurable (horizontalMollify (unitMassScaledMollifier d ε) u) :=
    measurable_horizontalMollify _ hκm hum
  have hψi : Integrable (horizontalMollify (unitMassScaledMollifier d ε) u) Q :=
    (integrable_kernel_translate hQ hκm hκi hum hui).integral_prod_left
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hKL := ((integrable_windowMass hQ hum hui).const_mul C).const_mul L
  have hgψm : Measurable (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) :=
    hg.continuous.measurable.comp hψm
  have hgψi := integrable_comp_of_lipschitz hg hL hψm hψi
  have hdiffh : ∀ᵐ ω ∂Q, ∀ x : Vec d, DifferentiableAt ℝ
      (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) ω) x := by
    filter_upwards [hbd] with ω hω
    intro x
    exact (hgd (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω x)).comp x (hω.1 x)
  have hbdh : ∀ᵐ ω ∂Q, ∀ s : ℝ, |s| ≤ 1 →
      |coordinateDerivative i (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω))
        ω) (s • unitVector i)| ≤ L * (C * ∫ z : Vec d, (Metric.closedBall (0 : Vec d) 2).indicator
          (fun z => ‖u (translate z ω)‖) z ∂volume) := by
    filter_upwards [hbd] with ω hω
    intro s hs
    have hD := hω.2 s hs
    have hcomp := coordinateDerivative_comp_real hgd (hω.1 (s • unitVector i)) i
    show |coordinateDerivative i (fun y => g (orbit (horizontalMollify (unitMassScaledMollifier d ε) u)
      ω y)) (s • unitVector i)| ≤ _
    rw [hcomp, abs_mul]
    exact mul_le_mul (hL _) hD (abs_nonneg _) hL0
  -- The orbit derivative of the composed field agrees with the chain rule almost surely.
  have hEq : (fun ω => coordinateDerivative i
      (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) ω) 0) =ᵐ[Q]
      fun ω => deriv g (horizontalMollify (unitMassScaledMollifier d ε) u ω) *
        coordinateDerivative i (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 := by
    filter_upwards [hbd] with ω hω
    have hc := coordinateDerivative_comp_real hgd (hω.1 0) i
    rw [orbit_zero] at hc
    exact hc
  have hDm : AEStronglyMeasurable (fun ω => coordinateDerivative i
      (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) ω) 0) Q := by
    refine AEStronglyMeasurable.congr ?_ hEq.symm
    exact ((hgc.measurable.comp hψm).aestronglyMeasurable).mul
      (aemeasurable_orbit_derivative_mollified hQ (contDiff_unitMassScaled ε)
        (hasCompactSupport_unitMassScaled hε hε1) i hum hui).aestronglyMeasurable
  have hIBP := integral_orbit_derivative_mul_core (hQ := hQ) i hgψm hgψi hKL hdiffh hbdh hDm hH
  have hLHS : (∫ ω, coordinateDerivative i
      (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) ω) 0 * H ω ∂Q) =
      ∫ ω, deriv g (horizontalMollify (unitMassScaledMollifier d ε) u ω) *
        horizontalMollify (unitMassScaledMollifier d ε) Du ω * H ω ∂Q := by
    apply integral_congr_ae
    filter_upwards [hEq, ae_orbit_derivative_mollify_eq hQ hε hε1 hum hui hDum hDui i hweak]
      with ω h1 h2
    have h1' : coordinateDerivative i
        (orbit (fun ω => g (horizontalMollify (unitMassScaledMollifier d ε) u ω)) ω) 0 =
        deriv g (horizontalMollify (unitMassScaledMollifier d ε) u ω) *
          coordinateDerivative i (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 :=
      h1
    have h2' : coordinateDerivative i (orbit (horizontalMollify (unitMassScaledMollifier d ε) u) ω) 0 =
        horizontalMollify (unitMassScaledMollifier d ε) Du ω := h2
    rw [h1', h2']
  have hfin := hLHS.symm.trans hIBP
  rw [hfin, neg_neg]

/-- The mollification kernel at the `n`-th scale `1/(n+1)`. -/
private noncomputable abbrev seqKernel (n : ℕ) : Vec d → ℝ :=
  unitMassScaledMollifier d (1 / ((n : ℝ) + 1))

private theorem seqKernel_facts (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

private theorem tendsto_one_div_succ_nhdsWithin :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  exact Filter.Eventually.of_forall fun n => by
    change 0 < 1 / ((n : ℝ) + 1)
    positivity

/-- The mollified observable at a scale `ε ∈ (0, 1]` is integrable. -/
private theorem integrable_horizontalMollify_unitMassScaled {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {v : FieldPair d → ℝ} (hvm : Measurable v) (hvi : Integrable v Q) :
    Integrable (horizontalMollify (unitMassScaledMollifier d ε) v) Q := by
  have hκcont : Continuous (unitMassScaledMollifier d ε) := (contDiff_unitMassScaled ε).continuous
  exact (integrable_kernel_translate hQ hκcont.measurable
    (hκcont.integrable_of_hasCompactSupport (hasCompactSupport_unitMassScaled hε hε1)) hvm
    hvi).integral_prod_left

/-- A bounded measurable derivative of a horizontal core multiplies integrable functions. -/
private theorem integrable_mul_deriv_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {f : FieldPair d → ℝ} {H : FieldPair d → ℝ} (i : Fin d) {B' : ℝ} (hf : Integrable f Q)
    (hH : IsHorizontalTest H) (hB' : ∀ ω, |horizontalDerivative i H ω| ≤ B') :
    Integrable (fun ω => f ω * horizontalDerivative i H ω) Q :=
  hf.mul_bdd (c := B') (hH.measurable_derivative i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hB' ω)

/-- The chain identity for a `C¹` profile with bounded derivative, tested against a bounded orbit
core, passes to the limit `ε → 0`. -/
theorem integral_chain_core {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L : ℝ} (hL : ∀ x, |deriv g x| ≤ L)
    {u Du : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q)
    (hDum : Measurable Du) (hDui : Integrable Du Q) (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q))
    {H : FieldPair d → ℝ} (hH : IsHorizontalTest H) :
    (∫ ω, g (u ω) * horizontalDerivative i H ω ∂Q) =
      -(∫ ω, deriv g (u ω) * Du ω * H ω ∂Q) := by
  haveI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  obtain ⟨B, -, hB⟩ := hH.bound_orbit
  obtain ⟨B', -, hB'⟩ := hH.bound_derivative i
  have hHB : ∀ ω, |H ω| ≤ B := fun ω => by simpa only [orbit_zero] using hB ω 0
  have hHD : ∀ ω, |horizontalDerivative i H ω| ≤ B' := fun ω => hB' ω 0
  have hHmeas : Measurable H := hH.1
  have hκm : ∀ n : ℕ, Measurable (seqKernel (d := d) n) := fun n =>
    (contDiff_unitMassScaled _).continuous.measurable
  have hψm : ∀ n : ℕ, Measurable (horizontalMollify (seqKernel (d := d) n) u) := fun n =>
    measurable_horizontalMollify _ (hκm n) hum
  have hψDm : ∀ n : ℕ, Measurable (horizontalMollify (seqKernel (d := d) n) Du) := fun n =>
    measurable_horizontalMollify _ (hκm n) hDum
  have hψi : ∀ n : ℕ, Integrable (horizontalMollify (seqKernel (d := d) n) u) Q := fun n =>
    integrable_horizontalMollify_unitMassScaled hQ (seqKernel_facts n).1 (seqKernel_facts n).2 hum hui
  have hψDi : ∀ n : ℕ, Integrable (horizontalMollify (seqKernel (d := d) n) Du) Q := fun n =>
    integrable_horizontalMollify_unitMassScaled hQ (seqKernel_facts n).1 (seqKernel_facts n).2
      hDum hDui
  -- `L¹` convergence of the mollified observables.
  have hconv_u : Tendsto (fun n : ℕ =>
      eLpNorm (fun ω => horizontalMollify (seqKernel (d := d) n) u ω - u ω) 1 Q) atTop (𝓝 0) :=
    (tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ 1 ENNReal.one_ne_top hum
      (memLp_one_iff_integrable.mpr hui)).comp tendsto_one_div_succ_nhdsWithin
  have hconv_D : Tendsto (fun n : ℕ =>
      eLpNorm (fun ω => horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) 1 Q) atTop (𝓝 0) :=
    (tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ 1 ENNReal.one_ne_top hDum
      (memLp_one_iff_integrable.mpr hDui)).comp tendsto_one_div_succ_nhdsWithin
  -- The mollified chain identities.
  have hchain : ∀ n : ℕ, (∫ ω, g (horizontalMollify (seqKernel (d := d) n) u ω) *
      horizontalDerivative i H ω ∂Q) = -(∫ ω, deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
        horizontalMollify (seqKernel (d := d) n) Du ω * H ω ∂Q) := fun n =>
    integral_chain_mollify_core hQ hg hL (seqKernel_facts n).1 (seqKernel_facts n).2 hum hui hDum
      hDui i hweak hH
  -- The left-hand side converges by the Lipschitz bound.
  have hLlim : Tendsto (fun n : ℕ => ∫ ω, g (horizontalMollify (seqKernel (d := d) n) u ω) *
      horizontalDerivative i H ω ∂Q) atTop
      (𝓝 (∫ ω, g (u ω) * horizontalDerivative i H ω ∂Q)) := by
    have hgu : Integrable (fun ω => g (u ω)) Q :=
      integrable_comp_of_lipschitz hg hL hum hui
    have hgψ : ∀ n : ℕ, Integrable (fun ω => g (horizontalMollify (seqKernel (d := d) n) u ω)) Q :=
      fun n => integrable_comp_of_lipschitz hg hL (hψm n) (hψi n)
    have hsplitL : ∀ n : ℕ, (∫ ω, g (horizontalMollify (seqKernel (d := d) n) u ω) *
        horizontalDerivative i H ω ∂Q) = (∫ ω, (g (horizontalMollify (seqKernel (d := d) n) u ω) -
          g (u ω)) * horizontalDerivative i H ω ∂Q) + ∫ ω, g (u ω) * horizontalDerivative i H ω ∂Q := by
      intro n
      have hA := integrable_mul_deriv_core i (hgψ n) hH hHD
      have hB₀ := integrable_mul_deriv_core i hgu hH hHD
      have e : (∫ ω, (g (horizontalMollify (seqKernel (d := d) n) u ω) - g (u ω)) *
          horizontalDerivative i H ω ∂Q) = (∫ ω, g (horizontalMollify (seqKernel (d := d) n) u ω) *
          horizontalDerivative i H ω ∂Q) - ∫ ω, g (u ω) * horizontalDerivative i H ω ∂Q := by
        rw [← integral_sub hA hB₀]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => sub_mul _ _ _
      rw [e]
      ring
    have hzero : Tendsto (fun n : ℕ => ∫ ω, (g (horizontalMollify (seqKernel (d := d) n) u ω) -
        g (u ω)) * horizontalDerivative i H ω ∂Q) atTop (𝓝 0) := by
      refine tendsto_integral_zero_of_abs_le (K := L * B') (F := fun n ω =>
        (g (horizontalMollify (seqKernel (d := d) n) u ω) - g (u ω)) * horizontalDerivative i H ω)
        (e := fun n ω => horizontalMollify (seqKernel (d := d) n) u ω - u ω) (fun n => ?_)
        (fun n => (hψi n).sub hui) (fun n => ?_) hconv_u
      · exact (((hg.continuous.measurable.comp (hψm n)).sub
          (hg.continuous.measurable.comp hum)).mul (hH.measurable_derivative i)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω => ?_
        have h1 := abs_sub_le_of_deriv_bound hgd hL (horizontalMollify (seqKernel (d := d) n) u ω) (u ω)
        calc |(g (horizontalMollify (seqKernel (d := d) n) u ω) - g (u ω)) *
              horizontalDerivative i H ω|
            = |g (horizontalMollify (seqKernel (d := d) n) u ω) - g (u ω)| *
              |horizontalDerivative i H ω| := abs_mul _ _
          _ ≤ (L * |horizontalMollify (seqKernel (d := d) n) u ω - u ω|) * B' :=
              mul_le_mul h1 (hHD ω) (abs_nonneg _) (mul_nonneg hL0 (abs_nonneg _))
          _ = L * B' * |horizontalMollify (seqKernel (d := d) n) u ω - u ω| := by ring
    have hfin := hzero.add_const (∫ ω, g (u ω) * horizontalDerivative i H ω ∂Q)
    rw [zero_add] at hfin
    exact hfin.congr (fun n => (hsplitL n).symm)
  -- The right-hand side converges by splitting off the derivative and the profile variation.
  have hRlim : Tendsto (fun n : ℕ => ∫ ω, deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
      horizontalMollify (seqKernel (d := d) n) Du ω * H ω ∂Q) atTop
      (𝓝 (∫ ω, deriv g (u ω) * Du ω * H ω ∂Q)) := by
    have hT1i : ∀ n : ℕ, Integrable (fun ω => deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
        (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω) Q := fun n =>
      integrable_bdd_mul_core (hgc.measurable.comp (hψm n)) (fun ω => hL _)
        ((hψDi n).sub hDui) hH
    have hT2i : ∀ n : ℕ, Integrable (fun ω => (deriv g (horizontalMollify (seqKernel (d := d) n) u ω) -
        deriv g (u ω)) * (Du ω * H ω)) Q := fun n => by
      refine (integrable_mul_core hDui hH).bdd_mul (c := 2 * L)
        ((hgc.measurable.comp (hψm n)).sub (hgc.measurable.comp hum)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      show ‖deriv g (horizontalMollify (seqKernel (d := d) n) u ω) - deriv g (u ω)‖ ≤ 2 * L
      rw [Real.norm_eq_abs]
      have h1 := abs_sub (deriv g (horizontalMollify (seqKernel (d := d) n) u ω)) (deriv g (u ω))
      linarith [hL (horizontalMollify (seqKernel (d := d) n) u ω), hL (u ω)]
    have hR0i : Integrable (fun ω => deriv g (u ω) * Du ω * H ω) Q :=
      integrable_bdd_mul_core (hgc.measurable.comp hum) (fun ω => hL _) hDui hH
    have hT1 : Tendsto (fun n : ℕ => ∫ ω, deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
        (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω ∂Q) atTop (𝓝 0) := by
      refine tendsto_integral_zero_of_abs_le (K := L * B) (F := fun n ω =>
        deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
          (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω)
        (e := fun n ω => horizontalMollify (seqKernel (d := d) n) Du ω - Du ω)
        (fun n => (hT1i n).aestronglyMeasurable) (fun n => (hψDi n).sub hDui) (fun n => ?_) hconv_D
      refine Filter.Eventually.of_forall fun ω => ?_
      show |deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
        (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω| ≤
          L * B * |horizontalMollify (seqKernel (d := d) n) Du ω - Du ω|
      rw [abs_mul, abs_mul]
      calc |deriv g (horizontalMollify (seqKernel (d := d) n) u ω)| *
            |horizontalMollify (seqKernel (d := d) n) Du ω - Du ω| * |H ω| ≤
            (L * |horizontalMollify (seqKernel (d := d) n) Du ω - Du ω|) * B :=
            mul_le_mul (mul_le_mul_of_nonneg_right (hL _) (abs_nonneg _)) (hHB ω)
              (abs_nonneg _) (mul_nonneg hL0 (abs_nonneg _))
        _ = L * B * |horizontalMollify (seqKernel (d := d) n) Du ω - Du ω| := by ring
    have hT2 : Tendsto (fun n : ℕ => ∫ ω, (deriv g (horizontalMollify (seqKernel (d := d) n) u ω) -
        deriv g (u ω)) * (Du ω * H ω) ∂Q) atTop (𝓝 0) :=
      tendsto_integral_comp_sub_mul (fun n => (hψm n).aestronglyMeasurable)
        hum.aestronglyMeasurable hconv_u hgc hL (integrable_mul_core hDui hH)
    have hfin := (hT1.add hT2).add_const (∫ ω, deriv g (u ω) * Du ω * H ω ∂Q)
    rw [zero_add, zero_add] at hfin
    refine hfin.congr (fun n => ?_)
    have hsplit : (∫ ω, deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
        horizontalMollify (seqKernel (d := d) n) Du ω * H ω ∂Q) =
        (∫ ω, deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
          (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω ∂Q) +
        (∫ ω, (deriv g (horizontalMollify (seqKernel (d := d) n) u ω) - deriv g (u ω)) *
          (Du ω * H ω) ∂Q) + ∫ ω, deriv g (u ω) * Du ω * H ω ∂Q := by
      have hA2 : Integrable (fun ω => deriv g (horizontalMollify (seqKernel (d := d) n) u ω) *
          (horizontalMollify (seqKernel (d := d) n) Du ω - Du ω) * H ω +
          (deriv g (horizontalMollify (seqKernel (d := d) n) u ω) - deriv g (u ω)) *
          (Du ω * H ω)) Q := (hT1i n).add (hT2i n)
      rw [← integral_add (hT1i n) (hT2i n), ← integral_add hA2 hR0i]
      congr 1
      funext ω
      ring
    exact hsplit.symm
  have hlim := tendsto_nhds_unique hLlim (hRlim.neg.congr fun n => (hchain n).symm)
  exact hlim

/-! ### The mollifier commutes with the `L²` translation group -/

/-- The mollified `L²` class: the Bochner integral of the translated classes against the mollifier.
It is the `L²` form of `∫ κ(x) F(T_{εx} ·) dx`. -/
noncomputable def mollifyLp (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ε : ℝ) (w : Lp ℝ 2 Q) : Lp ℝ 2 Q :=
  ∫ x : Vec d, mollifier d x • translationLp Q hQ (ε • x) w

private theorem integrable_mollifyLp_integrand (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (ε : ℝ) (w : Lp ℝ 2 Q) :
    Integrable (fun x : Vec d => mollifier d x • translationLp Q hQ (ε • x) w) volume := by
  have hcont : Continuous (fun x : Vec d => translationLp Q hQ (ε • x) w) :=
    (continuous_translationLp Q hQ).comp ((continuous_id.const_smul ε).prodMk continuous_const)
  exact ((contDiff_mollifier d).continuous.smul hcont).integrable_of_hasCompactSupport
    (hasCompactSupport_mollifier d).smul_right

private theorem mollifyLp_sub (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ε : ℝ) (w₁ w₂ : Lp ℝ 2 Q) :
    mollifyLp Q hQ ε (w₁ - w₂) = mollifyLp Q hQ ε w₁ - mollifyLp Q hQ ε w₂ := by
  unfold mollifyLp
  rw [← integral_sub (integrable_mollifyLp_integrand Q hQ ε w₁)
    (integrable_mollifyLp_integrand Q hQ ε w₂)]
  congr 1
  funext x
  rw [map_sub, smul_sub]

private theorem mollifyLp_smul (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ε c : ℝ) (w : Lp ℝ 2 Q) :
    mollifyLp Q hQ ε (c • w) = c • mollifyLp Q hQ ε w := by
  unfold mollifyLp
  rw [← integral_smul c]
  congr 1
  funext x
  rw [map_smul]
  exact smul_comm _ _ _

private theorem translationLp_comm_apply (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (a b : Vec d) (w : Lp ℝ 2 Q) :
    translationLp Q hQ a (translationLp Q hQ b w) = translationLp Q hQ b (translationLp Q hQ a w) := by
  rw [← translationLp_add Q hQ a b, ← translationLp_add Q hQ b a, add_comm]

private theorem translationLp_mollifyLp (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (a : Vec d) (ε : ℝ) (w : Lp ℝ 2 Q) :
    translationLp Q hQ a (mollifyLp Q hQ ε w) = mollifyLp Q hQ ε (translationLp Q hQ a w) := by
  unfold mollifyLp
  rw [← (translationLp Q hQ a).integral_comp_comm]
  congr 1
  funext x
  rw [map_smul, translationLp_comm_apply Q hQ a (ε • x) w]

/-- The mollified class has norm at most the norm of the class. -/
private theorem norm_mollifyLp_le (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (ε : ℝ) (w : Lp ℝ 2 Q) : ‖mollifyLp Q hQ ε w‖ ≤ ‖w‖ := by
  unfold mollifyLp
  have hint : Integrable (fun x : Vec d => mollifier d x * ‖w‖) volume :=
    ((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const ‖w‖
  have hpt : ∀ x : Vec d, ‖mollifier d x • translationLp Q hQ (ε • x) w‖ ≤ mollifier d x * ‖w‖ :=
    fun x => by
      rw [norm_smul, norm_translationLp, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg d x)]
  have h := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const, integral_mollifier d, one_mul] at h
  exact h

/-- The horizontal derivative passes through the mollified `L²` classes: the mollification of an
`L²`-generator pair is again an `L²`-generator pair. -/
theorem hasHorizontalLpDerivative_mollifyLp (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (i : Fin d) (ε : ℝ) {u v : Lp ℝ 2 Q}
    (h : HasHorizontalLpDerivative Q hQ i u v) :
    HasHorizontalLpDerivative Q hQ i (mollifyLp Q hQ ε u) (mollifyLp Q hQ ε v) := by
  have hquot : ∀ t : ℝ, t⁻¹ • (translationLp Q hQ (t • unitVector i) (mollifyLp Q hQ ε u) -
      mollifyLp Q hQ ε u) =
      mollifyLp Q hQ ε (t⁻¹ • (translationLp Q hQ (t • unitVector i) u - u)) := by
    intro t
    rw [mollifyLp_smul, mollifyLp_sub, translationLp_mollifyLp]
  unfold HasHorizontalLpDerivative at h ⊢
  refine Tendsto.congr (fun t => (hquot t).symm) ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.1 h)
  rw [← mollifyLp_sub]
  exact norm_mollifyLp_le Q hQ ε _

/-! ### Bounded representatives and the bridge to horizontally smooth tests -/

/-- A bounded measurable representative of an `L²` class with a.e. bound. -/
private theorem exists_bounded_measurable_representative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (F : Lp ℝ 2 Q) {M : ℝ} (hM : ∀ᵐ ω ∂Q, |F ω| ≤ M) :
    ∃ F₁ : FieldPair d → ℝ, Measurable F₁ ∧ (∀ ω, |F₁ ω| ≤ max M 0) ∧ F₁ =ᵐ[Q] ⇑F := by
  have hF := (Lp.memLp F).aestronglyMeasurable
  set F₀ : FieldPair d → ℝ := hF.mk ⇑F with hF₀def
  have hF₀m : Measurable F₀ := hF.measurable_mk
  have hF₀ae : F₀ =ᵐ[Q] ⇑F := hF.ae_eq_mk.symm
  refine ⟨fun ω => if |F₀ ω| ≤ max M 0 then F₀ ω else 0, ?_, ?_, ?_⟩
  · have hab : Measurable (fun ω => |F₀ ω|) := continuous_abs.measurable.comp hF₀m
    exact Measurable.ite (measurableSet_le hab measurable_const) hF₀m measurable_const
  · intro ω
    by_cases h : |F₀ ω| ≤ max M 0
    · simp only [if_pos h]
      exact h
    · simp only [if_neg h, abs_zero]
      exact le_max_right _ _
  · filter_upwards [hF₀ae, hM] with ω h1 h2
    have h3 : |F₀ ω| ≤ max M 0 := by
      rw [h1]
      exact h2.trans (le_max_left _ _)
    simp only [if_pos h3]
    exact h1

/-- The `L²`-smooth test has an almost everywhere bound. -/
private theorem ae_bound_of_smooth {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {F : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F) :
    ∃ M : ℝ, ∀ᵐ ω ∂Q, |F ω| ≤ M := by
  obtain ⟨G', hG', M, hM⟩ := hF []
  have hG'eq : G' = F := hG'
  rw [hG'eq] at hM
  exact ⟨M, hM⟩

/-- The horizontal derivative of an `L²`-smooth test has an almost everywhere bound. -/
private theorem ae_bound_deriv_of_smooth {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {F G : Lp ℝ 2 Q} {i : Fin d}
    (hF : IsHorizontallySmoothTest Q hQ F) (hG : HasHorizontalLpDerivative Q hQ i F G) :
    ∃ M : ℝ, ∀ᵐ ω ∂Q, |G ω| ≤ M := by
  obtain ⟨G'', hG'', M, hM⟩ := hF [i]
  obtain ⟨h, hh, hd⟩ := hG''
  have hhF : h = F := hh
  rw [hhF] at hd
  have hGG : G'' = G := HasHorizontalLpDerivative.unique hd hG
  rw [hGG] at hM
  exact ⟨M, hM⟩

/-- The mollified kernel integral of a bounded observable is bounded by the same constant. -/
private theorem abs_mollifier_integral_le {v : FieldPair d → ℝ} {M : ℝ} (ε : ℝ)
    (hvb : ∀ ω, |v ω| ≤ M) (ω : FieldPair d) :
    |∫ x : Vec d, mollifier d x * v (translate (ε • x) ω)| ≤ M := by
  have hint : Integrable (fun x : Vec d => mollifier d x * M) volume :=
    ((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const M
  have hpt : ∀ x : Vec d, ‖mollifier d x * v (translate (ε • x) ω)‖ ≤ mollifier d x * M := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs (v _), abs_of_nonneg (mollifier_nonneg d x)]
    exact mul_le_mul_of_nonneg_left (hvb _) (mollifier_nonneg d x)
  have h := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const, integral_mollifier d, one_mul, Real.norm_eq_abs] at h
  exact h

/-- The bridge: the weak chain identity on a horizontally smooth test, obtained from the mollified
cores by the commutation of the mollifier with the `L²` translation group. -/
theorem integral_chain_smooth {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L : ℝ} (hL : ∀ x, |deriv g x| ≤ L)
    {u Du : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q)
    (hDum : Measurable Du) (hDui : Integrable Du Q) (i : Fin d)
    (hweak : ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Du ω * K ω ∂Q))
    {F G : Lp ℝ 2 Q} (hFs : IsHorizontallySmoothTest Q hQ F)
    (hG : HasHorizontalLpDerivative Q hQ i F G) :
    (∫ ω, g (u ω) * G ω ∂Q) = -(∫ ω, deriv g (u ω) * Du ω * F ω ∂Q) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  obtain ⟨M1, hM1⟩ := ae_bound_of_smooth hFs
  obtain ⟨M2, hM2⟩ := ae_bound_deriv_of_smooth hFs hG
  obtain ⟨F₁, hF₁m, hF₁b, hF₁ae⟩ := exists_bounded_measurable_representative F hM1
  obtain ⟨G₁, hG₁m, hG₁b, hG₁ae⟩ := exists_bounded_measurable_representative G hM2
  set MF := max M1 0 with hMF
  set MG := max M2 0 with hMG
  have hF₁2 : MemLp F₁ 2 Q := MemLp.of_bound hF₁m.aestronglyMeasurable MF
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hF₁b ω)
  have hG₁2 : MemLp G₁ 2 Q := MemLp.of_bound hG₁m.aestronglyMeasurable MG
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hG₁b ω)
  set u2 : Lp ℝ 2 Q := hF₁2.toLp F₁ with hu2
  set v2 : Lp ℝ 2 Q := hG₁2.toLp G₁ with hv2
  have hu2F : u2 = F := Lp.ext ((MemLp.coeFn_toLp hF₁2).trans hF₁ae)
  have hv2G : v2 = G := Lp.ext ((MemLp.coeFn_toLp hG₁2).trans hG₁ae)
  have hG2 : HasHorizontalLpDerivative Q hQ i u2 v2 := by
    rw [hu2F, hv2G]
    exact hG
  -- The mollified cores of the bounded representatives, at the scales `ε n = 1/(n+1)`.
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  set H : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x : Vec d, mollifier d x * F₁ (translate (ε n • x) ω) with hHdef
  set KG : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x : Vec d, mollifier d x * G₁ (translate (ε n • x) ω) with hKGdef
  have hεpos : ∀ n, 0 < ε n := fun n => (seqKernel_facts n).1
  have hεtend : Tendsto (fun n : ℕ => ε n) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hHcore : ∀ n, IsHorizontalTest (H n) := fun n =>
    EinsteinRelation.Correctors.isHorizontalTest_scaled_mollifier hF₁m ⟨MF, hF₁b⟩ (ε n) (hεpos n)
  have hHmeas : ∀ n, Measurable (H n) := fun n => (hHcore n).1
  -- The `L²` classes of the cores are the mollified classes.
  have hcls : ∀ n, ((hHcore n).memLp Q 2).toLp (H n) = mollifyLp Q hQ (ε n) u2 := fun n => by
    obtain ⟨hS, hSeq⟩ := EinsteinRelation.Correctors.exists_mollifier_representative_eq_translation_integral
      Q hQ hF₁m ⟨MF, hF₁b⟩ hF₁2 (ε n)
    exact hSeq
  have hKGL : ∀ n, ∃ hS : MemLp (KG n) 2 Q, hS.toLp (KG n) = mollifyLp Q hQ (ε n) v2 := fun n => by
    obtain ⟨hS, hSeq⟩ := EinsteinRelation.Correctors.exists_mollifier_representative_eq_translation_integral
      Q hQ hG₁m ⟨MG, hG₁b⟩ hG₁2 (ε n)
    exact ⟨hS, hSeq⟩
  -- The derivative of each core is the mollified `G₁` almost everywhere, by the commutation.
  have hdae : ∀ n, ∀ᵐ ω ∂Q, horizontalDerivative i (H n) ω = KG n ω := by
    intro n
    obtain ⟨hS, hSeq⟩ := hKGL n
    have hcore_der := (hHcore n).hasHorizontalLpDerivative_toLp Q hQ i
    rw [hcls n] at hcore_der
    have hcom := hasHorizontalLpDerivative_mollifyLp Q hQ i (ε n) hG2
    have hDeq := hcore_der.unique hcom
    have e1 := ((hHcore n).memLp_derivative Q 2 i).coeFn_toLp
    have e2 : ⇑(mollifyLp Q hQ (ε n) v2) =ᵐ[Q] KG n := by
      rw [← hSeq]
      exact hS.coeFn_toLp
    filter_upwards [e1, e2] with ω h1 h2
    rw [hDeq, h2] at h1
    exact h1.symm
  -- The `L²` convergence of the cores to `F₁` and of their derivatives to `G₁`.
  have hHlim : Tendsto (fun n => eLpNorm (fun ω => H n ω - F₁ ω) 2 Q) atTop (𝓝 0) := by
    have hLp : Tendsto (fun n => mollifyLp Q hQ (ε n) u2) atTop (𝓝 u2) :=
      (EinsteinRelation.Correctors.tendsto_horizontalMollifier_translation_integral Q hQ u2).comp
        hεtend
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ u2).1 hLp).congr'
      (Filter.Eventually.of_forall fun n => ?_)
    have hA : ⇑(mollifyLp Q hQ (ε n) u2) =ᵐ[Q] H n := by
      rw [← hcls n]
      exact MemLp.coeFn_toLp _
    exact eLpNorm_congr_ae (hA.sub (MemLp.coeFn_toLp hF₁2))
  have hKGlim : Tendsto (fun n => eLpNorm (fun ω => KG n ω - G₁ ω) 2 Q) atTop (𝓝 0) := by
    have hLp : Tendsto (fun n => mollifyLp Q hQ (ε n) v2) atTop (𝓝 v2) :=
      (EinsteinRelation.Correctors.tendsto_horizontalMollifier_translation_integral Q hQ v2).comp
        hεtend
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ v2).1 hLp).congr'
      (Filter.Eventually.of_forall fun n => ?_)
    obtain ⟨hS, hSeq⟩ := hKGL n
    have hA : ⇑(mollifyLp Q hQ (ε n) v2) =ᵐ[Q] KG n := by
      rw [← hSeq]
      exact hS.coeFn_toLp
    exact eLpNorm_congr_ae (hA.sub (MemLp.coeFn_toLp hG₁2))
  -- Bounds and measurability of the sequences.
  have hHb : ∀ n ω, |H n ω| ≤ MF := fun n ω => abs_mollifier_integral_le (ε n) hF₁b ω
  have hKGb : ∀ n ω, |KG n ω| ≤ MG := fun n ω => abs_mollifier_integral_le (ε n) hG₁b ω
  have hKGaesm : ∀ n, AEStronglyMeasurable (KG n) Q := fun n =>
    ((hHcore n).measurable_derivative i).aestronglyMeasurable.congr (hdae n)
  have hgu : Integrable (fun ω => g (u ω)) Q := integrable_comp_of_lipschitz hg hL hum hui
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hDuw : Integrable (fun ω => deriv g (u ω) * Du ω) Q :=
    hDui.bdd_mul (c := L) (hgc.measurable.comp hum).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hL _)
  -- Passage to the limit on both sides.
  have hLHS : Tendsto (fun n => ∫ ω, KG n ω * g (u ω) ∂Q) atTop
      (𝓝 (∫ ω, G₁ ω * g (u ω) ∂Q)) :=
    tendsto_integral_mul_of_bounded (p := 2) two_ne_zero hKGaesm hG₁m.aestronglyMeasurable hKGlim
      (M := MG) (fun n => Filter.Eventually.of_forall fun ω => hKGb n ω) hgu
  have hRHS : Tendsto (fun n => ∫ ω, H n ω * (deriv g (u ω) * Du ω) ∂Q) atTop
      (𝓝 (∫ ω, F₁ ω * (deriv g (u ω) * Du ω) ∂Q)) :=
    tendsto_integral_mul_of_bounded (p := 2) two_ne_zero (fun n => (hHmeas n).aestronglyMeasurable)
      hF₁m.aestronglyMeasurable hHlim (M := MF) (fun n => Filter.Eventually.of_forall fun ω => hHb n ω)
      hDuw
  -- The chain identity on each core.
  have hstep : ∀ n, (∫ ω, KG n ω * g (u ω) ∂Q) = -(∫ ω, H n ω * (deriv g (u ω) * Du ω) ∂Q) := by
    intro n
    have e1 : (∫ ω, KG n ω * g (u ω) ∂Q) = ∫ ω, g (u ω) * horizontalDerivative i (H n) ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hdae n] with ω hω
      rw [hω, mul_comm]
    have e2 : (∫ ω, deriv g (u ω) * Du ω * H n ω ∂Q) =
        ∫ ω, H n ω * (deriv g (u ω) * Du ω) ∂Q := by
      congr 1
      funext ω
      ring
    rw [e1, integral_chain_core hQ hg hL hum hui hDum hDui i hweak (hHcore n), e2]
  have hlimit := tendsto_nhds_unique hLHS (hRHS.neg.congr fun n => (hstep n).symm)
  -- Transfer the limit identity back to the given test `F` and its derivative `G`.
  have hGint : (∫ ω, g (u ω) * G ω ∂Q) = ∫ ω, G₁ ω * g (u ω) ∂Q := by
    apply integral_congr_ae
    filter_upwards [hG₁ae] with ω h
    rw [← h, mul_comm]
  have hFint : (∫ ω, deriv g (u ω) * Du ω * F ω ∂Q) =
      ∫ ω, F₁ ω * (deriv g (u ω) * Du ω) ∂Q := by
    apply integral_congr_ae
    filter_upwards [hF₁ae] with ω h
    rw [← h]
    ring
  rw [hGint, hFint]
  exact hlimit

/-! ### The weak horizontal chain rule -/

/-- The weak horizontal chain rule for a `C¹` profile with bounded derivative, for every stationary
probability law on coefficient pairs: composition with `g` preserves the weak horizontal gradient,
which becomes `g'(f) Df`. -/
theorem hasWeakChainRule_of_contDiff {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {L : ℝ}
    (hL : ∀ x, |deriv g x| ≤ L) : Entropy.HasWeakChainRule Q hQ g := by
  intro f Df hf
  have hgc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨fm, hfm, hfae⟩ : ∃ fm : FieldPair d → ℝ, Measurable fm ∧ f =ᵐ[Q] fm :=
    ⟨hf.1.aestronglyMeasurable.mk f, hf.1.aestronglyMeasurable.measurable_mk,
      hf.1.aestronglyMeasurable.ae_eq_mk⟩
  have hfi : Integrable fm Q := hf.1.congr hfae
  have hDi : ∀ i : Fin d, ∃ Dm : FieldPair d → ℝ, Measurable Dm ∧ Integrable Dm Q ∧
      (fun ω => Df ω i) =ᵐ[Q] Dm := fun i =>
    ⟨(hf.2.1 i).aestronglyMeasurable.mk _, (hf.2.1 i).aestronglyMeasurable.measurable_mk,
      (hf.2.1 i).congr (hf.2.1 i).aestronglyMeasurable.ae_eq_mk,
      (hf.2.1 i).aestronglyMeasurable.ae_eq_mk⟩
  choose Dm hDm hDmi hDmae using hDi
  have hweak : ∀ i : Fin d, ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, fm ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, Dm i ω * K ω ∂Q) := by
    intro i K hK
    have h := weakPairing_core hf i hK
    have e1 : (∫ ω, fm ω * horizontalDerivative i K ω ∂Q) =
        ∫ ω, f ω * horizontalDerivative i K ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hfae] with ω hω
      rw [hω]
    have e2 : (∫ ω, Dm i ω * K ω ∂Q) = ∫ ω, Df ω i * K ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hDmae i] with ω hω
      rw [← hω]
    rw [e1, e2]
    exact h
  unfold HasWeakHorizontalGradient
  refine ⟨?_, fun i => ?_, fun i F G hFs hG => ?_⟩
  · exact (integrable_comp_of_lipschitz hg hL hfm hfi).congr (by
      filter_upwards [hfae] with ω hω
      rw [hω])
  · exact (hf.2.1 i).bdd_mul (c := L) (hgc.comp_aestronglyMeasurable hf.1.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hL _)
  · have key := integral_chain_smooth hQ hg hL hfm hfi (hDm i) (hDmi i) i (hweak i) hFs hG
    have e1 : (∫ ω, g (f ω) * G ω ∂Q) = ∫ ω, g (fm ω) * G ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hfae] with ω hω
      rw [hω]
    have e2 : (∫ ω, deriv g (f ω) * Df ω i * F ω ∂Q) =
        ∫ ω, deriv g (fm ω) * Dm i ω * F ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hfae, hDmae i] with ω h1 h2
      rw [h1, ← h2]
    show (∫ ω, g (f ω) * G ω ∂Q) = -(∫ ω, deriv g (f ω) * Df ω i * F ω ∂Q)
    rw [e1, e2]
    exact key

/-- The truncation profile `r ↦ r exp (-(l r²))` has the weak horizontal chain rule for `0 ≤ l`. -/
theorem hasWeakChainRule_truncProfile {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {l : ℝ} (hl : 0 ≤ l) :
    Entropy.HasWeakChainRule Q hQ (Entropy.truncProfile l) := by
  have hC1 : ContDiff ℝ 1 (Entropy.truncProfile l) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun r => (Entropy.hasDerivAt_truncProfile l r).differentiableAt, ?_⟩
    have hd : deriv (Entropy.truncProfile l) = Entropy.truncDeriv l :=
      funext fun r => (Entropy.hasDerivAt_truncProfile l r).deriv
    rw [hd]
    exact Entropy.continuous_truncDeriv l
  refine hasWeakChainRule_of_contDiff Q hQ hC1 (L := 2) fun r => ?_
  rw [(Entropy.hasDerivAt_truncProfile l r).deriv]
  exact Entropy.abs_truncDeriv_le_two hl r

end EinsteinRelation.Calculus
