import EinsteinFull.Calculus.C16ReducedGeneratorAE
import EinsteinFull.Calculus.S4CountableBasicSupport
import EinsteinFull.Calculus.S4GammaSupport
import EinsteinRelation.Diffusion.NullOccupation
import EinsteinRelation.Calculus.Weak
import EllipticRegularity.Parabolic.SliceEstimate.WeakC1
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Group.Integral
import PDEFoundation.FunctionalInequalities.SobolevSharpOne.Assembly

/-!
# Generator transfer under spatial null-occupation

These support lemmas justify the actual default-derivative generator along paths.
Positive-time marginal densities suffice via Fubini; no pathwise absolute continuity
of an individual trajectory's occupation measure is needed for that route.
The actual martingale law also satisfies the finite-time weak Dynkin equation.
They do not construct a reduced diffusion or assert reduced martingale-problem existence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open scoped Topology

namespace EinsteinFull
open EinsteinRelation

/-- Time-almost-everywhere equality of generators along almost every path transfers the
martingale problem, including interval integrability and strong adaptedness. -/
theorem c16_solves_of_ae_path_generator {d : ℕ}
    {L L' : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P)
    (hm : ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      Measurable (L' f))
    (he : ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ t : ℝ≥0, ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.uIoc 0 (t : ℝ)),
        L f (γ u.toNNReal) = L' f (γ u.toNNReal)) :
    SolvesMartingaleProblem L' x P := by
  refine ⟨hP.1, hP.2.1, fun f hf hc => ?_⟩
  obtain ⟨hi, hint, hmart⟩ := hP.2.2 f hf hc
  have hcomp : ∀ t, compensatedTest L f t =ᵐ[P] compensatedTest L' f t := by
    intro t
    filter_upwards [he f hf hc t] with γ hγ
    unfold compensatedTest
    rw [intervalIntegral.integral_congr_ae_restrict hγ]
  refine ⟨fun t => ?_, fun t => (hint t).congr (hcomp t), ?_⟩
  · filter_upwards [hi t, he f hf hc t] with γ hiγ heγ
    exact hiγ.congr_ae heγ
  · exact hmart.congr
      (stronglyAdapted_compensatedTest_of_measurable L' f hf.continuous (hm f hf hc))
      hcomp

private theorem c16_measurable_actual_reduced {d : ℕ} (ω : FieldPair d)
    (i : Fin d) (lam : ℝ) (f : Vec d → ℝ) :
    Measurable (reducedGenerator i ω lam f) := by
  unfold reducedGenerator divergence coordinateDerivative dot
  refine Measurable.add (measurable_const.mul ?_) (measurable_const.mul ?_)
  · exact Finset.measurable_sum _ fun k _ => measurable_fderiv_apply_const ℝ _ _
  · refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · simpa only [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
        ((continuous_reducedCoefficient ω).matrix_elem k i).measurable
    · exact measurable_fderiv_apply_const ℝ f (unitVector k)

/-- A textbook solution with absolutely continuous positive-time occupation solves the
literal reduced martingale problem. Spatial equality is transported through the occupation
measure, rather than rewritten pointwise at nondifferentiability points. -/
theorem c16_reduced_solves_of_textbook_and_occupation {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (hocc : ∀ᵐ γ ∂P,
      Measure.map (fun u : ℝ => γ u.toNNReal) (volume.restrict (Set.Ioi 0)) ≪
        (volume : Measure (Vec d))) :
    SolvesMartingaleProblem (reducedGenerator i ω lam) x P := by
  refine c16_solves_of_ae_path_generator hP
    (fun f _ _ => c16_measurable_actual_reduced ω i lam f) ?_
  intro f hf _ t
  filter_upwards [hocc] with γ hγ
  have ha := hγ.ae_le (c16_reduced_generator_ae_textbook hΛ hω)
  have hp := ae_of_ae_map
    (γ.continuous.comp continuous_real_toNNReal).measurable.aemeasurable ha
  have hs : Set.uIoc (0 : ℝ) (t : ℝ) ⊆ Set.Ioi 0 := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    exact fun _ hu => hu.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hp] with u hu
  exact (hu i lam f (contDiff_two_of_top hf)).symm

/-- Positive-time marginal absolute continuity transports the common spatial generator
identity along paths. The path event is chosen before the force, test, and terminal time. -/
theorem c16_ae_path_generator_eq_of_marginals {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (P : Measure (Path d)) [SFinite P]
    (hmarg : ∀ t : ℝ≥0, 0 < t →
      P.map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    ∀ᵐ γ ∂P, ∀ (i : Fin d) (lam : ℝ) (f : Vec d → ℝ),
      ContDiff ℝ 2 f → ∀ T : ℝ≥0,
      ∀ᵐ u ∂volume.restrict (Set.uIoc 0 (T : ℝ)),
        reducedGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (reducedCoefficient ω)
            (forcedDrift (reducedCoefficient ω) i lam) f (γ u.toNNReal) := by
  filter_upwards [ae_ae_path_of_ae P hmarg
    (c16_reduced_generator_ae_textbook hΛ hω)] with γ hγ
  intro i lam f hf T
  have hs : Set.uIoc (0 : ℝ) (T : ℝ) ⊆ Set.Ioi 0 := by
    rw [Set.uIoc_of_le T.coe_nonneg]
    exact fun _ hu => hu.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hγ] with u hu
  exact hu i lam f hf

/-- A textbook solution whose positive-time marginals have densities solves the literal
reduced martingale problem. Probability supplies the finiteness needed for Fubini. -/
theorem c16_reduced_solves_of_textbook_and_marginals {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (hmarg : ∀ t : ℝ≥0, 0 < t →
      P.map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    SolvesMartingaleProblem (reducedGenerator i ω lam) x P := by
  letI : IsProbabilityMeasure P := hP.1
  refine c16_solves_of_ae_path_generator hP
    (fun f _ _ => c16_measurable_actual_reduced ω i lam f) ?_
  intro f hf _ t
  filter_upwards [c16_ae_path_generator_eq_of_marginals hΛ hω P hmarg] with γ hγ
  filter_upwards [hγ i lam f (contDiff_two_of_top hf) t] with u hu
  exact hu.symm

/-- Absolute continuity of the averaged occupation measure transports a spatial
full-measure property to almost every time on almost every path. This does not
require absolute continuity of any individual path's occupation measure. -/
theorem c16_ae_path_of_averaged_occupation {d : ℕ}
    (P : Measure (Path d))
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    {p : Vec d → Prop} (hp : ∀ᵐ x ∂(volume : Measure (Vec d)), p x) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), p (γ u.toNNReal) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  exact Measure.ae_ae_of_ae_prod (ae_of_ae_map heval.aemeasurable (hocc.ae_le hp))

/-- Averaged occupation absolute continuity suffices to identify the literal
reduced generator of a textbook solution. The common spatial event precedes
the force, test and terminal-time quantifiers. -/
theorem c16_reduced_solves_of_textbook_and_averaged_occupation {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    SolvesMartingaleProblem (reducedGenerator i ω lam) x P := by
  have he := c16_ae_path_of_averaged_occupation P hocc
    (c16_reduced_generator_ae_textbook hΛ hω)
  refine c16_solves_of_ae_path_generator hP
    (fun f _ _ => c16_measurable_actual_reduced ω i lam f) ?_
  intro f hf _ t
  filter_upwards [he] with γ hγ
  have hs : Set.uIoc (0 : ℝ) (t : ℝ) ⊆ Set.Ioi 0 := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    exact fun _ hu => hu.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hγ] with u hu
  exact (hu i lam f (contDiff_two_of_top hf)).symm

/-- The compensated compact test of an actual martingale-problem solution has
zero mean at every finite time. This uses the supplied law, without a Markov
or density assumption. -/
theorem c16_integral_compensated_test_eq_zero {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (t : ℝ≥0) :
    (∫ γ, compensatedTest L f t γ ∂P) = 0 := by
  let _ : IsProbabilityMeasure P := hP.1
  have hz : compensatedTest L f 0 = fun _ => (0 : ℝ) := by
    funext γ
    simp only [compensatedTest, NNReal.coe_zero, intervalIntegral.integral_same, sub_self]
  have hmean := (hP.2.2 f hf hc).2.2.setIntegral_eq
    (show (0 : ℝ≥0) ≤ t from bot_le) MeasurableSet.univ
  simpa only [Measure.restrict_univ, hz, integral_zero] using hmean.symm

/-- The actual law's finite-time expected generator integral satisfies the
weak Dynkin equation. Integrability follows from the compact test and the
martingale-problem integrability clauses, without an occupation estimate. -/
theorem c16_integral_generator_eq_sub {d : ℕ}
    {L : (Vec d → ℝ) → Vec d → ℝ} {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem L x P) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (t : ℝ≥0) :
    Integrable (fun γ => ∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal)) P ∧
      (∫ γ, (∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal)) ∂P) =
        (∫ γ, f (γ t) ∂P) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hc
  have hF (s : ℝ≥0) : Integrable (fun γ : Path d => f (γ s)) P := by
    exact Integrable.of_bound
      (hf.continuous.measurable.comp (measurable_pathPosition s)).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun γ => hC (γ s))
  have hM := (hP.2.2 f hf hc).2.1 t
  have hsub : Integrable (fun γ : Path d => f (γ t) - f (γ 0)) P :=
    (hF t).sub (hF 0)
  have heq : (fun γ : Path d => ∫ u in (0 : ℝ)..(t : ℝ), L f (γ u.toNNReal)) =
      fun γ => f (γ t) - f (γ 0) - compensatedTest L f t γ := by
    funext γ
    dsimp only [compensatedTest]
    ring
  have hstart : (∫ γ, f (γ 0) ∂P) = f x := by
    calc
      (∫ γ, f (γ 0) ∂P) = ∫ _ : Path d, f x ∂P :=
        integral_congr_ae (hP.2.1.mono fun _ h => congrArg f h)
      _ = f x := by simp
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hsub.sub hM
  · rw [heq, integral_sub hsub hM,
      integral_sub (hF t) (hF 0), hstart,
      c16_integral_compensated_test_eq_zero hP hf hc t, sub_zero]

/-- The finite-horizon averaged occupation measure of the actual textbook law
satisfies its spatial weak equation. All coefficients and the supplied law
are the ones in the reduced problem; no density representation is used. -/
theorem c16_textbook_occupation_weak_equation {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (t : ℝ≥0) :
    (∫ y, External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) f y
      ∂Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (t : ℝ))))) =
      (∫ γ, f (γ t) ∂P) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hg := hcoef.measurable_gen f
  obtain ⟨C, hC⟩ := bounded_svGenerator _ _ hAb hbb (contDiff_two_of_top hf) hc
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hi : Integrable (fun z : Path d × ℝ =>
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f (z.1 z.2.toNNReal))
      (P.prod (volume.restrict (Set.Ioc 0 (t : ℝ)))) := by
    exact Integrable.of_bound (hg.comp heval).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using hC (z.1 z.2.toNNReal))
  rw [integral_map heval.aemeasurable hg.aestronglyMeasurable, integral_prod _ hi]
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
    (c16_integral_generator_eq_sub hP hf hc t).2

/-- Polynomial tails use the explicit Euclidean quadratic form, independent of
`Vec`'s ambient coordinate norm. -/
noncomputable def c16PolynomialKernel {d : ℕ} (r : ℝ) (m : ℕ) (w : Vec d) : ℝ :=
  ((r ^ 2 + euclideanSq w)⁻¹) ^ m

private theorem c16_norm_sq_le_euclideanSq {d : ℕ} (w : Vec d) :
    ‖w‖ ^ 2 ≤ euclideanSq w := by
  have hsq : 0 ≤ euclideanSq w := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (w k))
  have hn : ‖w‖ ≤ Real.sqrt (euclideanSq w) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [sq_abs, Real.sq_sqrt hsq]
    simpa only [euclideanSq, dot, pow_two] using
      Finset.single_le_sum (fun k _ => mul_self_nonneg (w k)) (Finset.mem_univ j)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hsq)

private noncomputable def c16_sq_gradient {d : ℕ} (w : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ j, (w j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
    w j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))

private theorem c16_hasFDerivAt_euclideanSq {d : ℕ} (w : Vec d) :
    HasFDerivAt (fun z : Vec d => euclideanSq z) (c16_sq_gradient w) w := by
  unfold euclideanSq dot c16_sq_gradient
  exact HasFDerivAt.fun_sum fun j _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) j w).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) j w)

private theorem c16_sq_gradient_unit {d : ℕ} (w : Vec d) (l : Fin d) :
    c16_sq_gradient w (unitVector l) = 2 * w l := by
  simp [c16_sq_gradient, unitVector, Pi.single_apply, Finset.sum_add_distrib, two_mul]

/-- The reciprocal quadratic kernel has a derivative envelope uniform in its scale. -/
theorem c16_reciprocal_kernel_derivative_bound {d : ℕ} {r : ℝ} (hr : 0 < r)
    (w : Vec d) (l : Fin d) :
    ‖w‖ * |fderiv ℝ (c16PolynomialKernel r 1) w (unitVector l)| ≤
      2 * c16PolynomialKernel r 1 w := by
  let q := r ^ 2 + euclideanSq w
  have hsq := c16_norm_sq_le_euclideanSq w
  have hq : 0 < q := by dsimp [q]; nlinarith [sq_pos_of_pos hr, sq_nonneg ‖w‖]
  have hD := (hasDerivAt_inv hq.ne').comp_hasFDerivAt w
    ((c16_hasFDerivAt_euclideanSq w).const_add (r ^ 2))
  have hd : fderiv ℝ (c16PolynomialKernel r 1) w (unitVector l) =
      -(q ^ 2)⁻¹ * (2 * w l) := by
    unfold c16PolynomialKernel
    simp only [pow_one]
    simpa only [Function.comp_def, smul_apply,
      smul_eq_mul, c16_sq_gradient_unit] using
      congrArg (fun D : Vec d →L[ℝ] ℝ => D (unitVector l)) hD.fderiv
  have hc : |w l| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w l
  have hprod : ‖w‖ * |w l| ≤ q := by
    have := mul_le_mul_of_nonneg_left hc (norm_nonneg w)
    dsimp [q]
    nlinarith [sq_nonneg r]
  rw [hd]
  calc
    ‖w‖ * |-(q ^ 2)⁻¹ * (2 * w l)| =
        2 * (‖w‖ * |w l|) * (q ^ 2)⁻¹ := by
      rw [abs_mul, abs_neg, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hq)),
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ 2 * q * (q ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num))
        (inv_nonneg.mpr (sq_nonneg q))
    _ = 2 * c16PolynomialKernel r 1 w := by
      simp only [c16PolynomialKernel, pow_one]
      change 2 * q * (q ^ 2)⁻¹ = 2 * q⁻¹
      field_simp [hq.ne']

/-- The polynomial kernel is positive at every point and every natural power. -/
theorem c16_polynomial_kernel_pos {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (w : Vec d) : 0 < c16PolynomialKernel r m w := by
  have hsq := c16_norm_sq_le_euclideanSq w
  have hq : 0 < r ^ 2 + euclideanSq w := by nlinarith [sq_pos_of_pos hr, sq_nonneg ‖w‖]
  exact pow_pos (inv_pos.mpr hq) m

/-- All polynomial-tail kernels are smooth. -/
theorem c16_polynomial_kernel_contDiff {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (c16PolynomialKernel (d := d) r m) := by
  unfold c16PolynomialKernel
  apply ContDiff.pow
  apply ContDiff.inv
  · unfold euclideanSq dot
    fun_prop
  · intro w
    have hsq := c16_norm_sq_le_euclideanSq w
    have hq : 0 < r ^ 2 + euclideanSq w := by nlinarith [sq_pos_of_pos hr, sq_nonneg ‖w‖]
    exact hq.ne'

/-- Raising the reciprocal quadratic kernel to a natural power preserves its
scale-uniform derivative envelope, with constant twice the power. -/
theorem c16_polynomial_kernel_derivative_bound {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (w : Vec d) (l : Fin d) :
    ‖w‖ * |fderiv ℝ (c16PolynomialKernel r m) w (unitVector l)| ≤
      (2 * (m : ℝ)) * c16PolynomialKernel r m w := by
  cases m with
  | zero =>
    have hz : c16PolynomialKernel (d := d) r 0 = fun _ => 1 := by
      funext z
      simp only [c16PolynomialKernel, pow_zero]
    rw [hz]
    simp
  | succ n =>
    let κ : Vec d → ℝ := c16PolynomialKernel r 1
    have hκ : DifferentiableAt ℝ κ w :=
      ((c16_polynomial_kernel_contDiff hr 1).differentiable (by simp)) w
    have heq : c16PolynomialKernel (d := d) r (n + 1) =
        fun z => κ z ^ (n + 1) := by
      funext z
      simp only [κ, c16PolynomialKernel, pow_one]
    have hpos : 0 < κ w := c16_polynomial_kernel_pos hr 1 w
    have hcoeff : 0 ≤ ((n + 1 : ℕ) : ℝ) * κ w ^ n := by positivity
    rw [heq, fderiv_fun_pow (n + 1) hκ]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_apply, smul_eq_mul,
      abs_mul, abs_of_nonneg hcoeff]
    calc
      ‖w‖ * (((n + 1 : ℕ) : ℝ) * κ w ^ n * |fderiv ℝ κ w (unitVector l)|) =
          (((n + 1 : ℕ) : ℝ) * κ w ^ n) *
            (‖w‖ * |fderiv ℝ κ w (unitVector l)|) := by ring
      _ ≤ (((n + 1 : ℕ) : ℝ) * κ w ^ n) * (2 * κ w) :=
        mul_le_mul_of_nonneg_left (c16_reciprocal_kernel_derivative_bound hr w l) hcoeff
      _ = (2 * ((n + 1 : ℕ) : ℝ)) * κ w ^ (n + 1) := by rw [pow_succ]; ring

private theorem c16_sq_gradient_norm_le {d : ℕ} (w : Vec d) :
    ‖c16_sq_gradient w‖ ≤ 2 * (d : ℝ) * ‖w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  calc
    ‖c16_sq_gradient w v‖ = ‖∑ j, (w j * v j + w j * v j)‖ := by
      simp only [c16_sq_gradient, sum_apply,
        add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    _ ≤ ∑ j : Fin d, ‖w j * v j + w j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, 2 * ‖w‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖w j * v j + w j * v j‖ ≤ ‖w j * v j‖ + ‖w j * v j‖ := norm_add_le _ _
        _ = 2 * (‖w j‖ * ‖v j‖) := by rw [norm_mul]; ring
        _ ≤ 2 * (‖w‖ * ‖v‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul (norm_le_pi_norm w j) (norm_le_pi_norm v j)
            (norm_nonneg _) (norm_nonneg _)) (by norm_num)
        _ = 2 * ‖w‖ * ‖v‖ := by ring
    _ = (2 * (d : ℝ) * ‖w‖) * ‖v‖ := by simp; ring

private theorem c16_reciprocal_kernel_fderiv_norm_le {d : ℕ} {r : ℝ} (hr : 0 < r)
    (w : Vec d) :
    ‖fderiv ℝ (c16PolynomialKernel r 1) w‖ ≤
      ((d : ℝ) / r) * c16PolynomialKernel r 1 w := by
  let q := r ^ 2 + euclideanSq w
  have hsq := c16_norm_sq_le_euclideanSq w
  have hq : 0 < q := by dsimp [q]; nlinarith [sq_pos_of_pos hr, sq_nonneg ‖w‖]
  have hD := (hasDerivAt_inv hq.ne').comp_hasFDerivAt w
    ((c16_hasFDerivAt_euclideanSq w).const_add (r ^ 2))
  have hd : fderiv ℝ (c16PolynomialKernel r 1) w =
      -(q ^ 2)⁻¹ • c16_sq_gradient w := by
    unfold c16PolynomialKernel
    simp only [pow_one]
    exact hD.fderiv
  have hratio : 2 * ‖w‖ ≤ q / r := by
    apply (le_div_iff₀ hr).mpr
    dsimp [q]
    nlinarith [sq_nonneg (r - ‖w‖)]
  rw [hd, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hq))]
  calc
    (q ^ 2)⁻¹ * ‖c16_sq_gradient w‖ ≤ (q ^ 2)⁻¹ * (2 * (d : ℝ) * ‖w‖) :=
      mul_le_mul_of_nonneg_left (c16_sq_gradient_norm_le w) (by positivity)
    _ ≤ (q ^ 2)⁻¹ * ((d : ℝ) * (q / r)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    _ = ((d : ℝ) / r) * c16PolynomialKernel r 1 w := by
      simp only [c16PolynomialKernel, pow_one]
      change (q ^ 2)⁻¹ * ((d : ℝ) * (q / r)) = ((d : ℝ) / r) * q⁻¹
      field_simp [hq.ne', hr.ne']

/-- At a fixed positive scale the full derivative has a global bound by the
kernel. This bound permits differentiation against a possibly singular measure. -/
theorem c16_polynomial_kernel_fderiv_norm_le {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (w : Vec d) :
    ‖fderiv ℝ (c16PolynomialKernel r m) w‖ ≤
      ((d : ℝ) * (m : ℝ) / r) * c16PolynomialKernel r m w := by
  cases m with
  | zero =>
    have hz : c16PolynomialKernel (d := d) r 0 = fun _ => 1 := by
      funext z
      simp only [c16PolynomialKernel, pow_zero]
    rw [hz]
    simp
  | succ n =>
    let κ : Vec d → ℝ := c16PolynomialKernel r 1
    have hκ : DifferentiableAt ℝ κ w :=
      ((c16_polynomial_kernel_contDiff hr 1).differentiable (by simp)) w
    have heq : c16PolynomialKernel (d := d) r (n + 1) =
        fun z => κ z ^ (n + 1) := by
      funext z
      simp only [κ, c16PolynomialKernel, pow_one]
    have hpos : 0 < κ w := c16_polynomial_kernel_pos hr 1 w
    have hcoeff : 0 ≤ ((n + 1 : ℕ) : ℝ) * κ w ^ n := by positivity
    rw [heq, fderiv_fun_pow (n + 1) hκ]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hcoeff]
    calc
      (((n + 1 : ℕ) : ℝ) * κ w ^ n) * ‖fderiv ℝ κ w‖ ≤
          (((n + 1 : ℕ) : ℝ) * κ w ^ n) * (((d : ℝ) / r) * κ w) :=
        mul_le_mul_of_nonneg_left (c16_reciprocal_kernel_fderiv_norm_le hr w) hcoeff
      _ = ((d : ℝ) * ((n + 1 : ℕ) : ℝ) / r) * κ w ^ (n + 1) := by
        rw [pow_succ]; ring

/-- The polynomial kernel is bounded at every fixed positive scale. -/
theorem c16_polynomial_kernel_le {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (w : Vec d) : c16PolynomialKernel r m w ≤ ((r ^ 2)⁻¹) ^ m := by
  have hsq : 0 ≤ euclideanSq w :=
    (sq_nonneg ‖w‖).trans (c16_norm_sq_le_euclideanSq w)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by positivity))
    (inv_anti₀ (sq_pos_of_pos hr) (le_add_of_nonneg_right hsq)) m

/-- Against any finite measure the polynomial kernel and every translate are integrable.
The measure need not have a density. -/
theorem c16_polynomial_kernel_integrable {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (μ : Measure (Vec d)) [IsFiniteMeasure μ] (y : Vec d) :
    Integrable (fun z => c16PolynomialKernel r m (z - y)) μ := by
  have hm : AEStronglyMeasurable (fun z => c16PolynomialKernel r m (z - y)) μ :=
    ((c16_polynomial_kernel_contDiff hr m).continuous.comp
    (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable (μ := μ)
  refine (integrable_const ((r ^ 2)⁻¹ ^ m)).mono' hm ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_pos (c16_polynomial_kernel_pos hr m (z - y))]
  have hsq : 0 ≤ euclideanSq (z - y) :=
    (sq_nonneg ‖z - y‖).trans (c16_norm_sq_le_euclideanSq (z - y))
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by positivity))
    (inv_anti₀ (sq_pos_of_pos hr) (le_add_of_nonneg_right hsq)) m

/-- The derivative of a translated polynomial kernel is integrable against
any finite measure, independently of occupation absolute continuity. -/
theorem c16_polynomial_kernel_fderiv_integrable {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (μ : Measure (Vec d)) [IsFiniteMeasure μ] (y : Vec d) :
    Integrable (fun z => fderiv ℝ (c16PolynomialKernel r m) (z - y)) μ := by
  have hm : AEStronglyMeasurable
      (fun z => fderiv ℝ (c16PolynomialKernel r m) (z - y)) μ :=
    (((c16_polynomial_kernel_contDiff hr m).continuous_fderiv (by simp)).comp
      (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable
  exact ((c16_polynomial_kernel_integrable hr m μ y).const_mul
    ((d : ℝ) * (m : ℝ) / r)).mono' hm
      (Filter.Eventually.of_forall fun z => c16_polynomial_kernel_fderiv_norm_le hr m (z - y))

/-- Differentiate the smoothing of a finite measure directly under the integral.
The original measure may be singular. -/
theorem c16_polynomial_smoothing_hasFDerivAt {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (μ : Measure (Vec d)) [IsFiniteMeasure μ] (y : Vec d) :
    HasFDerivAt (fun v => ∫ z, c16PolynomialKernel r m (z - v) ∂μ)
      (∫ z, -(fderiv ℝ (c16PolynomialKernel r m) (z - y)) ∂μ) y := by
  let D : ℝ := (d : ℝ) * (m : ℝ) / r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcont := c16_polynomial_kernel_contDiff (d := d) hr m
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun v z => c16PolynomialKernel r m (z - v))
    (F' := fun v z => -(fderiv ℝ (c16PolynomialKernel r m) (z - v)))
    (s := Set.univ) (bound := fun _ => D * ((r ^ 2)⁻¹) ^ m)
    Filter.univ_mem ?_ (c16_polynomial_kernel_integrable hr m μ y) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun v =>
      (hcont.continuous.comp
        (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable
  · exact (((hcont.continuous_fderiv (by simp)).comp
      (continuous_id.sub continuous_const)).neg).measurable.aestronglyMeasurable
  · filter_upwards [] with z v _
    rw [norm_neg]
    exact (c16_polynomial_kernel_fderiv_norm_le hr m (z - v)).trans
      (mul_le_mul_of_nonneg_left (c16_polynomial_kernel_le hr m (z - v)) hD)
  · filter_upwards [] with z v _
    simpa [Function.comp_def] using (((hcont.differentiable (by simp)) (z - v)).hasFDerivAt.comp v
      ((hasFDerivAt_id v).const_sub z))

/-- The gradient of the smoothing is bounded by the smoothing itself at each
fixed scale, with no regularity assumption on the finite measure. -/
theorem c16_polynomial_smoothing_fderiv_norm_le {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (μ : Measure (Vec d)) [IsFiniteMeasure μ] (y : Vec d) :
    ‖fderiv ℝ (fun v => ∫ z, c16PolynomialKernel r m (z - v) ∂μ) y‖ ≤
      ((d : ℝ) * (m : ℝ) / r) * ∫ z, c16PolynomialKernel r m (z - y) ∂μ := by
  rw [(c16_polynomial_smoothing_hasFDerivAt hr m μ y).fderiv]
  calc
    ‖∫ z, -(fderiv ℝ (c16PolynomialKernel r m) (z - y)) ∂μ‖ ≤
        ∫ z, ((d : ℝ) * (m : ℝ) / r) * c16PolynomialKernel r m (z - y) ∂μ := by
      apply norm_integral_le_of_norm_le
        ((c16_polynomial_kernel_integrable hr m μ y).const_mul _)
      filter_upwards [] with z
      rw [norm_neg]
      exact c16_polynomial_kernel_fderiv_norm_le hr m (z - y)
    _ = ((d : ℝ) * (m : ℝ) / r) * ∫ z, c16PolynomialKernel r m (z - y) ∂μ :=
      integral_const_mul _ _

/-- Polynomial smoothing of a finite measure is continuously differentiable. -/
theorem c16_polynomial_smoothing_contDiff_one {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (μ : Measure (Vec d)) [IsFiniteMeasure μ] :
    ContDiff ℝ 1 (fun y => ∫ z, c16PolynomialKernel r m (z - y) ∂μ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y => (c16_polynomial_smoothing_hasFDerivAt hr m μ y).differentiableAt, ?_⟩
  have heq : fderiv ℝ (fun y => ∫ z, c16PolynomialKernel r m (z - y) ∂μ) =
      fun y => ∫ z, -(fderiv ℝ (c16PolynomialKernel r m) (z - y)) ∂μ := by
    funext y
    exact (c16_polynomial_smoothing_hasFDerivAt hr m μ y).fderiv
  rw [heq]
  let D : ℝ := (d : ℝ) * (m : ℝ) / r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hc := (c16_polynomial_kernel_contDiff (d := d) hr m).continuous_fderiv (by simp)
  refine continuous_of_dominated (bound := fun _ : Vec d => D * ((r ^ 2)⁻¹) ^ m)
    ?_ ?_ (integrable_const _) ?_
  · intro y
    exact ((hc.comp (continuous_id.sub continuous_const)).neg).measurable.aestronglyMeasurable
  · intro y
    filter_upwards [] with z
    rw [norm_neg]
    exact (c16_polynomial_kernel_fderiv_norm_le hr m (z - y)).trans
      (mul_le_mul_of_nonneg_left (c16_polynomial_kernel_le hr m (z - y)) hD)
  · filter_upwards [] with z
    exact (hc.comp (continuous_const.sub continuous_id)).neg

/-- Polynomial tails are Lebesgue integrable once twice their power exceeds
the dimension. This estimate still uses the explicit Euclidean quadratic form. -/
theorem c16_polynomial_kernel_volume_integrable {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    Integrable (c16PolynomialKernel (d := d) r m) (volume : Measure (Vec d)) := by
  have hdim : (Module.finrank ℝ (Vec d) : ℝ) < 2 * (m : ℝ) := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using hdm
  have hg0 := integrable_rpow_neg_one_add_norm_sq
    (μ := (volume : Measure (Vec d))) hdim
  have hg : Integrable (fun w : Vec d => ((1 + ‖w‖ ^ 2)⁻¹) ^ m)
      (volume : Measure (Vec d)) := by
    refine hg0.congr (Filter.Eventually.of_forall fun w => ?_)
    dsimp only
    rw [show -(2 * (m : ℝ)) / 2 = -(m : ℝ) by ring,
      Real.rpow_neg (by positivity : 0 ≤ (1 : ℝ) + ‖w‖ ^ 2),
      Real.rpow_natCast, inv_pow]
  let c : ℝ := min (r ^ 2) 1
  have hc : 0 < c := lt_min (sq_pos_of_pos hr) one_pos
  have hcR : c ≤ r ^ 2 := min_le_left _ _
  have hc1 : c ≤ 1 := min_le_right _ _
  refine (hg.const_mul (c⁻¹ ^ m)).mono'
    (c16_polynomial_kernel_contDiff hr m).continuous.measurable.aestronglyMeasurable ?_
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_pos (c16_polynomial_kernel_pos hr m w)]
  have hcmp : c * (1 + ‖w‖ ^ 2) ≤ r ^ 2 + euclideanSq w := by
    have hn := c16_norm_sq_le_euclideanSq w
    have hmul := mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖w‖)
    nlinarith
  have hq : 0 < r ^ 2 + euclideanSq w :=
    lt_of_lt_of_le (mul_pos hc (by positivity)) hcmp
  calc
    c16PolynomialKernel r m w ≤ ((c * (1 + ‖w‖ ^ 2))⁻¹) ^ m :=
      pow_le_pow_left₀ (inv_nonneg.mpr hq.le)
        (inv_anti₀ (mul_pos hc (by positivity)) hcmp) m
    _ = c⁻¹ ^ m * ((1 + ‖w‖ ^ 2)⁻¹) ^ m := by
      rw [mul_inv_rev, mul_pow]
      ring

/-- The integrable polynomial kernel has strictly positive mass, so it can be normalized. -/
theorem c16_polynomial_kernel_integral_pos {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    0 < ∫ w : Vec d, c16PolynomialKernel r m w := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (c16_polynomial_kernel_contDiff hr m).continuous
    (c16_polynomial_kernel_volume_integrable hr m hdm)
    (fun w => (c16_polynomial_kernel_pos hr m w).le)
    (c16_polynomial_kernel_pos hr m (0 : Vec d)).ne'

/-- Normalize the polynomial kernel by its Lebesgue mass. -/
noncomputable def c16NormalizedPolynomialKernel {d : ℕ} (r : ℝ) (m : ℕ)
    (w : Vec d) : ℝ :=
  (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹ * c16PolynomialKernel r m w

/-- The normalized smoothing kernel is positive, smooth, and has mass one. -/
theorem c16_normalized_polynomial_kernel_properties {d : ℕ} {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    (∀ w : Vec d, 0 < c16NormalizedPolynomialKernel r m w) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c16NormalizedPolynomialKernel (d := d) r m) ∧
    Integrable (c16NormalizedPolynomialKernel (d := d) r m) volume ∧
    (∫ w : Vec d, c16NormalizedPolynomialKernel r m w) = 1 := by
  have hmass := c16_polynomial_kernel_integral_pos hr m hdm
  refine ⟨fun w => mul_pos (inv_pos.mpr hmass) (c16_polynomial_kernel_pos hr m w),
    contDiff_const.mul (c16_polynomial_kernel_contDiff hr m),
    (c16_polynomial_kernel_volume_integrable hr m hdm).const_mul _, ?_⟩
  change (∫ w : Vec d, (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹ *
    c16PolynomialKernel r m w) = 1
  rw [integral_const_mul, inv_mul_cancel₀ hmass.ne']

/-- Normalization preserves the scale-uniform commutator envelope. -/
theorem c16_normalized_polynomial_kernel_derivative_bound {d : ℕ} {r : ℝ}
    (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    (w : Vec d) (l : Fin d) :
    ‖w‖ * |fderiv ℝ (c16NormalizedPolynomialKernel r m) w (unitVector l)| ≤
      (2 * (m : ℝ)) * c16NormalizedPolynomialKernel r m w := by
  let c : ℝ := (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹
  have hc : 0 < c := inv_pos.mpr (c16_polynomial_kernel_integral_pos hr m hdm)
  have hf := ((c16_polynomial_kernel_contDiff (d := d) hr m).differentiable
    (by simp)) w
  change ‖w‖ * |fderiv ℝ (fun z => c * c16PolynomialKernel r m z) w
    (unitVector l)| ≤ (2 * (m : ℝ)) * (c * c16PolynomialKernel r m w)
  rw [fderiv_const_mul hf c, smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  nlinarith [mul_le_mul_of_nonneg_left
    (c16_polynomial_kernel_derivative_bound hr m w l) hc.le]

/-- Convolution of any finite measure with a nonnegative integrable continuous
kernel is integrable, with the product of the two masses. No density of the
original measure is required. -/
theorem c16_smoothing_integrable_mass {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {κ : Vec d → ℝ} (hc : Continuous κ) (h0 : ∀ w, 0 ≤ κ w)
    (hi : Integrable κ (volume : Measure (Vec d))) :
    Integrable (fun y => ∫ z, κ (z - y) ∂μ) volume ∧
    (∫ y, ∫ z, κ (z - y) ∂μ) = μ.real Set.univ * ∫ w, κ w := by
  have hm : AEStronglyMeasurable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) :=
    (hc.comp (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
  have hprod : Integrable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun z => hi.comp_sub_left z), ?_⟩
    have heq : (fun z : Vec d => ∫ y, ‖κ (z - y)‖) = fun _ => ∫ w, κ w := by
      funext z
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact integral_sub_left_eq_self κ volume z
    rw [heq]
    exact integrable_const _
  refine ⟨hprod.integral_prod_right, ?_⟩
  calc
    (∫ y, ∫ z, κ (z - y) ∂μ) = ∫ z, ∫ y, κ (z - y) ∂volume ∂μ :=
      (integral_integral_swap (f := fun z y => κ (z - y)) hprod).symm
    _ = μ.real Set.univ * ∫ w, κ w := by
      simp_rw [integral_sub_left_eq_self κ volume]
      simp only [integral_const, smul_eq_mul]

/-- The normalized smoothing of a finite measure retains exactly its mass. -/
theorem c16_normalized_polynomial_smoothing_mass {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    Integrable (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ) volume ∧
    (∫ y, ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ) = μ.real Set.univ := by
  obtain ⟨hpos, hc, hi, hmass⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  simpa only [hmass, mul_one] using
    c16_smoothing_integrable_mass μ hc.continuous (fun w => (hpos w).le) hi

/-- Normalization preserves continuous differentiability of finite-measure smoothing. -/
theorem c16_normalized_polynomial_smoothing_contDiff_one {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ContDiff ℝ 1 (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ) := by
  have heq : (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ) =
      fun y => (∫ w : Vec d, c16PolynomialKernel r m w)⁻¹ *
        ∫ z, c16PolynomialKernel r m (z - y) ∂μ := by
    funext y
    exact integral_const_mul _ _
  rw [heq]
  exact contDiff_const.mul (c16_polynomial_smoothing_contDiff_one hr m μ)

/-- The derivative bound for normalized smoothing is relative to its own density. -/
theorem c16_normalized_polynomial_smoothing_fderiv_norm_le {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (y : Vec d) :
    ‖fderiv ℝ (fun v => ∫ z, c16NormalizedPolynomialKernel r m (z - v) ∂μ) y‖ ≤
      ((d : ℝ) * (m : ℝ) / r) * ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ := by
  let c : ℝ := (∫ w : Vec d, c16PolynomialKernel r m w)⁻¹
  have hc : 0 < c := inv_pos.mpr (c16_polynomial_kernel_integral_pos hr m hdm)
  have heq : (fun v => ∫ z, c16NormalizedPolynomialKernel r m (z - v) ∂μ) =
      fun v => c * ∫ z, c16PolynomialKernel r m (z - v) ∂μ := by
    funext v
    exact integral_const_mul _ _
  rw [heq, fderiv_const_mul
    (c16_polynomial_smoothing_hasFDerivAt hr m μ y).differentiableAt c,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  calc
    c * ‖fderiv ℝ (fun v => ∫ z, c16PolynomialKernel r m (z - v) ∂μ) y‖ ≤
        c * (((d : ℝ) * (m : ℝ) / r) * ∫ z, c16PolynomialKernel r m (z - y) ∂μ) :=
      mul_le_mul_of_nonneg_left (c16_polynomial_smoothing_fderiv_norm_le hr m μ y) hc.le
    _ = ((d : ℝ) * (m : ℝ) / r) * (c * ∫ z, c16PolynomialKernel r m (z - y) ∂μ) := by
      ring
    _ = ((d : ℝ) * (m : ℝ) / r) * ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ :=
      congrArg (fun v : ℝ => ((d : ℝ) * (m : ℝ) / r) * v) (congrFun heq y).symm

/-- Both the normalized smoothed measure and its derivative are Lebesgue integrable
at every positive scale. -/
theorem c16_normalized_polynomial_smoothing_fderiv_integrable {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    Integrable (fun y : Vec d => fderiv ℝ
      (fun v : Vec d => ∫ z, c16NormalizedPolynomialKernel r m (z - v) ∂μ) y) volume := by
  have hm : AEStronglyMeasurable (fun y : Vec d => fderiv ℝ
      (fun v : Vec d => ∫ z, c16NormalizedPolynomialKernel r m (z - v) ∂μ) y) volume :=
    ((c16_normalized_polynomial_smoothing_contDiff_one μ hr m).continuous_fderiv
      (by norm_num)).measurable.aestronglyMeasurable
  exact ((c16_normalized_polynomial_smoothing_mass μ hr m hdm).1.const_mul
    ((d : ℝ) * (m : ℝ) / r)).mono' hm
      (Filter.Eventually.of_forall (c16_normalized_polynomial_smoothing_fderiv_norm_le μ hr m hdm))

/-- The actual finite-horizon occupation measure of any probability path law
has mass equal to the horizon, regardless of spatial singularities. -/
theorem c16_probability_occupation_mass {d : ℕ} (P : Measure (Path d))
    [IsProbabilityMeasure P] (T : ℝ≥0) :
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))).real Set.univ = T := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  rw [measureReal_def, Measure.map_apply heval MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul]
  simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Ioc]

/-- The normalized smoothing of the actual finite occupation measure is C¹,
with an integrable derivative, and retains exactly the time horizon as its mass.
This construction applies to the same path law for any martingale generator. -/
theorem c16_probability_occupation_normalized_smoothing {d : ℕ} (P : Measure (Path d))
    [IsProbabilityMeasure P] (T : ℝ≥0) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    let μ : Measure (Vec d) := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ
    ContDiff ℝ 1 u ∧ Integrable u volume ∧
      Integrable (fderiv ℝ u) volume ∧ (∫ y, u y) = T := by
  dsimp only
  refine ⟨c16_normalized_polynomial_smoothing_contDiff_one _ hr m,
    (c16_normalized_polynomial_smoothing_mass _ hr m hdm).1,
    c16_normalized_polynomial_smoothing_fderiv_integrable _ hr m hdm, ?_⟩
  rw [(c16_normalized_polynomial_smoothing_mass _ hr m hdm).2,
    c16_probability_occupation_mass P T]

/-- A bounded measurable scalar field contributes a smoothing flux controlled
by the smoothing itself. This applies to every bounded Borel drift component. -/
theorem c16_bounded_smoothing_flux {d : ℕ} (μ : Measure (Vec d))
    {b κ : Vec d → ℝ} (hb : Measurable b) (B : ℝ≥0)
    (hB : ∀ z, |b z| ≤ B) (hκm : Measurable κ) (hκ0 : ∀ z, 0 ≤ κ z)
    (y : Vec d) (hκ : Integrable (fun z => κ (z - y)) μ) :
    Integrable (fun z => b z * κ (z - y)) μ ∧
    |∫ z, b z * κ (z - y) ∂μ| ≤ (B : ℝ) * ∫ z, κ (z - y) ∂μ := by
  have hm : Measurable (fun z => b z * κ (z - y)) :=
    hb.mul (hκm.comp (measurable_id.sub measurable_const))
  have hbound (z : Vec d) : ‖b z * κ (z - y)‖ ≤ (B : ℝ) * κ (z - y) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hκ0 _)]
    exact mul_le_mul_of_nonneg_right (hB z) (hκ0 _)
  have hi := hκ.const_mul (B : ℝ)
  refine ⟨hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc
    |∫ z, b z * κ (z - y) ∂μ| = ‖∫ z, b z * κ (z - y) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, (B : ℝ) * κ (z - y) ∂μ :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbound)
    _ = (B : ℝ) * ∫ z, κ (z - y) ∂μ := integral_const_mul _ _

/-- A Lipschitz scalar coefficient has a smoothing commutator bounded by the
smoothed measure. This estimate does not use the reduced-coefficient formula. -/
theorem c16_lipschitz_coefficient_smoothing_commutator {d : ℕ}
    {a : Vec d → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L a)
    (l : Fin d) (μ : Measure (Vec d)) (κ : Vec d → ℝ) (C : ℝ≥0)
    (hgrad : ∀ w, ‖w‖ * |fderiv ℝ κ w (unitVector l)| ≤ (C : ℝ) * κ w)
    (y : Vec d) (hκ : Integrable (fun z => κ (z - y)) μ) :
    Integrable (fun z => (a z - a y) * fderiv ℝ κ (z - y) (unitVector l)) μ ∧
    |∫ z, (a z - a y) * fderiv ℝ κ (z - y) (unitVector l) ∂μ| ≤
      (L : ℝ) * (C : ℝ) * ∫ z, κ (z - y) ∂μ := by
  let F : Vec d → ℝ := fun z =>
    (a z - a y) *
      fderiv ℝ κ (z - y) (unitVector l)
  have hbound (z : Vec d) : ‖F z‖ ≤ (L : ℝ) * (C : ℝ) * κ (z - y) := by
    have ha := hLip.dist_le_mul z y
    rw [Real.dist_eq, dist_eq_norm] at ha
    calc
      ‖F z‖ = |a z - a y| *
          |fderiv ℝ κ (z - y) (unitVector l)| := by
        exact (norm_mul _ _).trans (congrArg₂ (· * ·)
          (Real.norm_eq_abs _) (Real.norm_eq_abs _))
      _ ≤ ((L : ℝ) * ‖z - y‖) * |fderiv ℝ κ (z - y) (unitVector l)| :=
        mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ = (L : ℝ) * (‖z - y‖ * |fderiv ℝ κ (z - y) (unitVector l)|) :=
        mul_assoc _ _ _
      _ ≤ (L : ℝ) * ((C : ℝ) * κ (z - y)) :=
        mul_le_mul_of_nonneg_left (hgrad _) L.coe_nonneg
      _ = (L : ℝ) * (C : ℝ) * κ (z - y) := (mul_assoc _ _ _).symm
  have hm : Measurable F :=
    (hLip.continuous.measurable.sub measurable_const).mul
      ((measurable_fderiv_apply_const ℝ κ (unitVector l)).comp
        (measurable_id.sub measurable_const))
  have hg := hκ.const_mul ((L : ℝ) * (C : ℝ))
  refine ⟨hg.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hbound), ?_⟩
  calc
    |∫ z, F z ∂μ| = ‖∫ z, F z ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, (L : ℝ) * (C : ℝ) * κ (z - y) ∂μ :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
    _ = (L : ℝ) * (C : ℝ) * ∫ z, κ (z - y) ∂μ := integral_const_mul _ _

/-- A smoothing kernel with a pointwise derivative envelope controls the coefficient
commutator by the smoothed measure itself. The measure may still be singular;
integrability of its smoothing is the only measure hypothesis. -/
theorem c16_reduced_coefficient_smoothing_commutator {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (j k l : Fin d) (μ : Measure (Vec d)) (κ : Vec d → ℝ) (C : ℝ≥0)
    (hgrad : ∀ w, ‖w‖ * |fderiv ℝ κ w (unitVector l)| ≤ (C : ℝ) * κ w)
    (y : Vec d) (hκ : Integrable (fun z => κ (z - y)) μ) :
    Integrable (fun z => (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ κ (z - y) (unitVector l)) μ ∧
    |∫ z, (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ κ (z - y) (unitVector l) ∂μ| ≤
      (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ) *
        (C : ℝ) * ∫ z, κ (z - y) ∂μ := by
  exact c16_lipschitz_coefficient_smoothing_commutator
    (reducedCoefficient_lipschitz hΛ hω j k) l μ κ C hgrad y hκ

/-- For a finite measure, polynomial smoothing controls the coefficient commutator
without a density or an additional integrability hypothesis. -/
theorem c16_reduced_polynomial_smoothing_commutator {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (j k l : Fin d) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (m : ℕ) (y : Vec d) :
    Integrable (fun z => (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ (c16PolynomialKernel r m) (z - y) (unitVector l)) μ ∧
    |∫ z, (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ (c16PolynomialKernel r m) (z - y) (unitVector l) ∂μ| ≤
      (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ) *
        (2 * (m : ℝ)) * ∫ z, c16PolynomialKernel r m (z - y) ∂μ := by
  have hgrad (w : Vec d) :
      ‖w‖ * |fderiv ℝ (c16PolynomialKernel r m) w (unitVector l)| ≤
        ((2 * (m : ℝ≥0) : ℝ≥0) : ℝ) * c16PolynomialKernel r m w := by
    simpa using c16_polynomial_kernel_derivative_bound hr m w l
  simpa using c16_reduced_coefficient_smoothing_commutator hΛ hω j k l μ
    (c16PolynomialKernel r m) (2 * (m : ℝ≥0)) hgrad y
    (c16_polynomial_kernel_integrable hr m μ y)

/-- The coefficient commutator of the actual law's finite-horizon occupation
measure satisfies the polynomial smoothing estimate, even before occupation AC. -/
theorem c16_textbook_occupation_smoothing_commutator {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (T : ℝ≥0) (j k l : Fin d) {r : ℝ} (hr : 0 < r) (m : ℕ) (y : Vec d) :
    let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    Integrable (fun z => (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ (c16PolynomialKernel r m) (z - y) (unitVector l)) μ ∧
    |∫ z, (reducedCoefficient ω z j k - reducedCoefficient ω y j k) *
      fderiv ℝ (c16PolynomialKernel r m) (z - y) (unitVector l) ∂μ| ≤
      (Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d) : ℝ) *
        (2 * (m : ℝ)) * ∫ z, c16PolynomialKernel r m (z - y) ∂μ := by
  let _ : IsProbabilityMeasure P := hP.1
  exact c16_reduced_polynomial_smoothing_commutator hΛ hω j k l _ hr m y

/-- Coordinate derivatives are controlled by the corresponding multilinear
operator norms on the original coordinate carrier. -/
theorem c16_test_coordinate_derivative_bounds {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ}
    (hB : ∀ k ≤ 2, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ B) (y : Vec d) :
    (∀ i, |fderiv ℝ f y (unitVector i)| ≤ B) ∧
      ∀ i j, |fderiv ℝ (fun z => fderiv ℝ f z (unitVector j)) y (unitVector i)| ≤ B := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · calc
      _ ≤ ‖fderiv ℝ f y‖ := by
        simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
          (fderiv ℝ f y).le_opNorm (unitVector i)
      _ = ‖iteratedFDeriv ℝ 1 f y‖ := (norm_iteratedFDeriv_one f).symm
      _ ≤ B := hB 1 (by omega) y
  · have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
      ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) y
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    have hb := (iteratedFDeriv ℝ 2 f y).le_opNorm ![unitVector i, unitVector j]
    have hb' : |fderiv ℝ (fderiv ℝ f) y (unitVector i) (unitVector j)| ≤
        ‖iteratedFDeriv ℝ 2 f y‖ := by
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.norm_eq_abs, Fin.prod_univ_two, unitVector, Pi.norm_single, norm_one,
        mul_one] using hb
    exact hb'.trans (hB 2 le_rfl y)

/-- Bounded measurable coefficients and bounded first and second derivatives
give a global generator bound, without a compact-support requirement. -/
theorem c16_bddCoef_generator_bound {d : ℕ} {A : Vec d → Mat d}
    {b : Vec d → Vec d} {M : ℝ} (h : BddCoef A b M) {f : Vec d → ℝ}
    {B : ℝ} (h1 : ∀ y i, |fderiv ℝ f y (unitVector i)| ≤ B)
    (h2 : ∀ y i j,
      |fderiv ℝ (fun z => fderiv ℝ f z (unitVector j)) y (unitVector i)| ≤ B)
    (y : Vec d) :
    |External.Draft.svGenerator A b f y| ≤
      (1 / 2 : ℝ) * (d * (d * (M * B))) + d * (M * B) := by
  unfold External.Draft.svGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, M * B := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        refine Finset.sum_le_sum fun i _ => ?_
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (h.Ab y i j) (h2 y i j) (abs_nonneg _)
          ((abs_nonneg _).trans (h.Ab y i j))
      _ = d * (d * (M * B)) := by simp
  · calc
      _ ≤ ∑ i : Fin d, M * B := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (h.bb y i) (h1 y i) (abs_nonneg _)
          ((abs_nonneg _).trans (h.bb y i))
      _ = d * (M * B) := by simp

/-- Local equality of tests preserves the textbook generator, including its
default derivatives. No coefficient regularity is needed for this identity. -/
theorem c16_svGenerator_congr_of_eventuallyEq {d : ℕ} (A : Vec d → Mat d)
    (b : Vec d → Vec d) {f g : Vec d → ℝ} {y : Vec d}
    (h : f =ᶠ[𝓝 y] g) :
    External.Draft.svGenerator A b f y = External.Draft.svGenerator A b g y := by
  have h2 (j : Fin d) :
      fderiv ℝ (fun z => fderiv ℝ f z (unitVector j)) y =
        fderiv ℝ (fun z => fderiv ℝ g z (unitVector j)) y := by
    have he : (fun z => fderiv ℝ f z (unitVector j)) =ᶠ[𝓝 y]
        (fun z => fderiv ℝ g z (unitVector j)) := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
      exact congrArg (fun D => D (unitVector j)) hz
    exact he.fderiv_eq
  simp only [External.Draft.svGenerator, h.fderiv_eq, h2]

/-- A bounded smooth test with bounded derivatives through order two admits
compact smooth cutoffs with the same bounds uniformly up to a constant.
The approximants eventually agree with the test on a neighborhood of each point. -/
theorem c16_exists_bounded_smooth_cutoffs {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ}
    (hB : ∀ k ≤ 2, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ B) :
    ∃ u : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n) ∧ HasCompactSupport (u n)) ∧
      (∃ C : ℝ, ∀ n k, k ≤ 2 → ∀ y, ‖iteratedFDeriv ℝ k (u n) y‖ ≤ C) ∧
      ∀ y, ∀ᶠ n in Filter.atTop, u n =ᶠ[𝓝 y] f := by
  obtain ⟨χ, hχ, hχc, _, hχ1, hχ0⟩ := exists_cutoff d
  have hb (k : Fin 3) : ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k χ y‖ ≤ C :=
    (hχ.continuous_iteratedFDeriv (by simp)).bounded_above_of_compact_support
      (hχc.iteratedFDeriv k)
  choose C hC using hb
  let A : ℝ := ∑ k : Fin 3, |C k|
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  have hχA (k : ℕ) (hk : k ≤ 2) (y : Vec d) :
      ‖iteratedFDeriv ℝ k χ y‖ ≤ A := by
    let j : Fin 3 := ⟨k, by omega⟩
    exact (hC j y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun k => |C k|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)))
  let u : ℕ → Vec d → ℝ := fun n => cutoffFn χ ((n : ℝ) + 1) f
  have hR (n : ℕ) : 1 ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hscaled (n k : ℕ) (hk : k ≤ 2) (y : Vec d) :
      ‖iteratedFDeriv ℝ k (fun z => χ (((n : ℝ) + 1)⁻¹ • z)) y‖ ≤ A := by
    have hR0 : 0 < (n : ℝ) + 1 := by positivity
    rw [iteratedFDeriv_comp_const_smul _ (hχ.of_le (by simp)),
      norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hR0)]
    calc
      _ ≤ 1 * A := mul_le_mul
        (pow_le_one₀ (inv_nonneg.mpr hR0.le) (inv_le_one_of_one_le₀ (hR n)))
        (hχA k hk _) (norm_nonneg _) zero_le_one
      _ = A := one_mul A
  refine ⟨u, fun n => ⟨contDiff_cutoffFn hχ hf _,
    hasCompactSupport_cutoffFn f (by positivity) hχ0⟩, ⟨4 * A * B, ?_⟩, ?_⟩
  · intro n k hk y
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec d => χ (((n : ℝ) + 1)⁻¹ • z)) :=
      hχ.comp (contDiff_const_smul _)
    apply (norm_iteratedFDeriv_mul_le hsmooth hf y (by simp)).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hscaled n j (hjk.trans hk) y) (Nat.cast_nonneg _))
          (hB (k - j) ((Nat.sub_le _ _).trans hk) y) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) * A * B := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ 4 * A * B := by
        have hs : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) ≤ 4 := by
          interval_cases k <;> norm_num [Finset.sum_range_succ]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hA) hB0
  · intro y
    have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (Filter.eventually_gt_atTop ‖y‖)] with n hn
    exact cutoffFn_eventuallyEq f (by positivity) hχ1 hn

/-- Expanding cutoffs extend the actual occupation weak equation to bounded
smooth tests with bounded derivatives through order two. The same supplied
martingale law and the original signed force are retained. -/
theorem c16_textbook_occupation_weak_equation_bounded {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B : ℝ}
    (hB : ∀ k ≤ 2, ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ B) (T : ℝ≥0) :
    (∫ y, External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) f y
      ∂Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
      (∫ γ, f (γ T) ∂P) - f x := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ : Measure (Vec d) := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  let L := External.Draft.svGenerator (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
  obtain ⟨u, hu, ⟨C, hC⟩, hlocal⟩ := c16_exists_bounded_smooth_cutoffs hf hB
  let K : ℝ := (1 / 2 : ℝ) * (d * (d * (max Ma Mb * C))) + d * (max Ma Mb * C)
  have hgen (n : ℕ) (y : Vec d) : ‖L (u n) y‖ ≤ K := by
    have hbnd := c16_test_coordinate_derivative_bounds (hu n).1 (hC n)
    exact c16_bddCoef_generator_bound hcoef (fun z => (hbnd z).1)
      (fun z => (hbnd z).2) y
  have hlim_gen : Filter.Tendsto (fun n => ∫ y, L (u n) y ∂μ)
      Filter.atTop (𝓝 (∫ y, L f y ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hcoef.measurable_gen (u n)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall (hgen n)) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hlocal y] with n hn
    exact (c16_svGenerator_congr_of_eventuallyEq _ _ hn).symm
  have hval (n : ℕ) (y : Vec d) : ‖u n y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using hC n 0 (by omega) y
  have hlim_val (y : Vec d) : Filter.Tendsto (fun n => u n y)
      Filter.atTop (𝓝 (f y)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hlocal y] with n hn
    exact hn.eq_of_nhds.symm
  have hlim_endpoint : Filter.Tendsto (fun n => ∫ γ, u n (γ T) ∂P)
      Filter.atTop (𝓝 (∫ γ, f (γ T) ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hu n).1.continuous.measurable.comp
        (measurable_pathPosition T)).aestronglyMeasurable)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun γ => hval n (γ T))
      (Filter.Eventually.of_forall fun γ => hlim_val (γ T))
  have heq (n : ℕ) : (∫ y, L (u n) y ∂μ) = (∫ γ, u n (γ T) ∂P) - u n x :=
    c16_textbook_occupation_weak_equation hΛ hω i lam hP (hu n).1 (hu n).2 T
  exact tendsto_nhds_unique hlim_gen
    ((hlim_endpoint.sub (hlim_val x)).congr fun n => (heq n).symm)

/-- Fubini and translation invariance move an integrable smoothing kernel
from the translation parameter to the space variable. Only a finite supplied
measure and a bounded measurable pairing are used; no density is assumed. -/
theorem c16_smoothing_recenter_pairing {d : ℕ} (μ : Measure (Vec d))
    [IsFiniteMeasure μ] {κ : Vec d → ℝ} (hc : Continuous κ)
    (h0 : ∀ w, 0 ≤ κ w) (hi : Integrable κ (volume : Measure (Vec d)))
    {G : Vec d → Vec d → ℝ} (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : ∀ z y, |G z y| ≤ B) :
    Integrable (fun s => κ s * ∫ z, G z (z - s) ∂μ) volume ∧
    Integrable (fun y => ∫ z, κ (z - y) * G z y ∂μ) volume ∧
    (∫ s, κ s * ∫ z, G z (z - s) ∂μ) =
      ∫ y, ∫ z, κ (z - y) * G z y ∂μ := by
  have hmκ : AEStronglyMeasurable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) :=
    (hc.comp (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
  have hκprod : Integrable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) := by
    apply (integrable_prod_iff hmκ).mpr
    refine ⟨Filter.Eventually.of_forall (fun z => hi.comp_sub_left z), ?_⟩
    have heq : (fun z : Vec d => ∫ y, ‖κ (z - y)‖) = fun _ => ∫ w, κ w := by
      funext z
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact integral_sub_left_eq_self κ volume z
    rw [heq]
    exact integrable_const _
  have hright : Integrable (fun p : Vec d × Vec d => κ (p.1 - p.2) * G p.1 p.2)
      (μ.prod volume) := by
    refine (hκprod.mul_const B).mono'
      (((hc.measurable.comp (measurable_fst.sub measurable_snd)).mul hG).aestronglyMeasurable) ?_
    filter_upwards [] with p
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h0 _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _ _) (h0 _)
  have hbase : Integrable (fun p : Vec d × Vec d => κ p.2 * B)
      (μ.prod volume) := by
    simpa only [one_mul] using
      ((integrable_const (1 : ℝ) : Integrable (fun _ : Vec d => (1 : ℝ)) μ).mul_prod hi).mul_const B
  have hleft : Integrable (fun p : Vec d × Vec d => κ p.2 * G p.1 (p.1 - p.2))
      (μ.prod volume) := by
    refine hbase.mono'
      (((hc.measurable.comp measurable_snd).mul
        (hG.comp (measurable_fst.prodMk (measurable_fst.sub measurable_snd)))).aestronglyMeasurable) ?_
    filter_upwards [] with p
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h0 _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _ _) (h0 _)
  refine ⟨?_, hright.integral_prod_right, ?_⟩
  · simpa only [integral_const_mul] using hleft.integral_prod_right
  · calc
      (∫ s, κ s * ∫ z, G z (z - s) ∂μ) =
          ∫ s, ∫ z, κ s * G z (z - s) ∂μ := by simp_rw [integral_const_mul]
      _ = ∫ z, ∫ s, κ s * G z (z - s) ∂volume ∂μ :=
        (integral_integral_swap (f := fun z s => κ s * G z (z - s)) hleft).symm
      _ = ∫ z, ∫ y, κ (z - y) * G z y ∂volume ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        simpa only [sub_sub_cancel] using
          integral_sub_left_eq_self (fun y => κ (z - y) * G z y) volume z
      _ = ∫ y, ∫ z, κ (z - y) * G z y ∂μ :=
        integral_integral_swap hright

/-- Translating a test translates its derivatives while keeping the original
coefficient values at the original point. -/
theorem c16_svGenerator_translate {d : ℕ} (A : Vec d → Mat d)
    (b : Vec d → Vec d) (f : Vec d → ℝ) (s z : Vec d) :
    External.Draft.svGenerator A b (fun w => f (w - s)) z =
      External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f (z - s) := by
  have hsecond (j : Fin d) :
      fderiv ℝ (fun w => fderiv ℝ f (w - s) (unitVector j)) z =
        fderiv ℝ (fun w => fderiv ℝ f w (unitVector j)) (z - s) :=
    fderiv_comp_sub (𝕜 := ℝ) (f := fun w : Vec d => fderiv ℝ f w (unitVector j))
      (x := z) s
  simp only [External.Draft.svGenerator, fderiv_comp_sub, hsecond]

/-- A bounded measurable coefficient field gives a jointly measurable frozen
coordinate generator, with coefficient point and test point kept separate. -/
theorem c16_bddCoef_measurable_frozen_generator {d : ℕ} {A : Vec d → Mat d}
    {b : Vec d → Vec d} {M : ℝ} (h : BddCoef A b M) (f : Vec d → ℝ) :
    Measurable (fun p : Vec d × Vec d =>
      External.Draft.svGenerator (fun _ => A p.1) (fun _ => b p.1) f p.2) := by
  unfold External.Draft.svGenerator
  refine Measurable.add ?_ ?_
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => ?_)
    exact ((h.Am i j).comp measurable_fst).mul
      ((measurable_fderiv_apply_const ℝ
        (fun y => fderiv ℝ f y (unitVector j)) (unitVector i)).comp measurable_snd)
  · refine Finset.measurable_sum _ fun i _ => ?_
    exact ((h.bm i).comp measurable_fst).mul
      ((measurable_fderiv_apply_const ℝ f (unitVector i)).comp measurable_snd)

/-- The actual finite occupation measure satisfies the convolved adjoint weak
equation. The smoothing kernel needs no second derivative, and neither the
occupation nor the endpoint law is assumed to have a density. -/
theorem c16_textbook_occupation_smoothed_weak_equation {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {κ : Vec d → ℝ} (hc : Continuous κ) (h0 : ∀ w, 0 ≤ κ w)
    (hi : Integrable κ (volume : Measure (Vec d)))
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (T : ℝ≥0) :
    (∫ y, ∫ z, κ (z - y) *
      External.Draft.svGenerator (fun _ => reducedCoefficient ω z)
        (fun _ => forcedDrift (reducedCoefficient ω) i lam z) f y
      ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
      ∫ y, ((∫ γ, κ (γ T - y) ∂P) - κ (x - y)) * f y := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ : Measure (Vec d) := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let ν : Measure (Vec d) := Measure.map (fun γ : Path d => γ T) P
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  let G : Vec d → Vec d → ℝ := fun z y =>
    External.Draft.svGenerator (fun _ => reducedCoefficient ω z)
      (fun _ => forcedDrift (reducedCoefficient ω) i lam z) f y
  obtain ⟨m, hm⟩ := exists_inH hf hfc
  have hconst (z : Vec d) : BddCoef (fun _ => reducedCoefficient ω z)
      (fun _ => forcedDrift (reducedCoefficient ω) i lam z) (max Ma Mb) :=
    ⟨fun _ _ => measurable_const, fun _ => measurable_const,
      fun _ => hcoef.Ab z, fun _ => hcoef.bb z⟩
  have hG : ∀ z y, |G z y| ≤
      (1 / 2 : ℝ) * (d * (d * (max Ma Mb * m))) + d * (max Ma Mb * m) :=
    fun z y => (hconst z).gen_bound hm y
  obtain ⟨hμleft, _, hμeq⟩ := c16_smoothing_recenter_pairing μ hc h0 hi (G := G)
    (c16_bddCoef_measurable_frozen_generator hcoef f) hG
  let F : Vec d → Vec d → ℝ := fun _ y => f y
  have hF : Measurable (Function.uncurry F) := hf.continuous.measurable.comp measurable_snd
  have hFm : ∀ z y, |F z y| ≤ m := fun _ y => hm.2.1.1 y
  have hν := c16_smoothing_recenter_pairing ν hc h0 hi hF hFm
  have hδ := c16_smoothing_recenter_pairing (Measure.dirac x) hc h0 hi hF hFm
  simp only [F] at hν
  simp only [F, integral_dirac] at hδ
  have hweak (s : Vec d) : (∫ z, G z (z - s) ∂μ) =
      (∫ z, f (z - s) ∂ν) - f (x - s) := by
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun z => f (z - s)) :=
      hf.comp (contDiff_id.sub contDiff_const)
    have hcshift : HasCompactSupport (fun z => f (z - s)) := by
      simpa [Function.comp_def, sub_eq_add_neg] using
        hfc.comp_homeomorph (Homeomorph.addRight (-s))
    have h := c16_textbook_occupation_weak_equation hΛ hω i lam hP hshift hcshift T
    have he : (∫ z, f (z - s) ∂ν) = ∫ γ, f (γ T - s) ∂P :=
      integral_map (measurable_pathPosition T).aemeasurable
        ((hf.continuous.comp (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable)
    rw [he]
    simpa only [c16_svGenerator_translate] using h
  have hνkernel (y : Vec d) : (∫ z, κ (z - y) * f y ∂ν) =
      (∫ γ, κ (γ T - y) ∂P) * f y := by
    rw [integral_mul_const]
    congr 1
    exact integral_map (measurable_pathPosition T).aemeasurable
      ((hc.comp (continuous_id.sub continuous_const)).measurable.aestronglyMeasurable)
  calc
    _ = ∫ s, κ s * ∫ z, G z (z - s) ∂μ := hμeq.symm
    _ = ∫ s, (κ s * ∫ z, f (z - s) ∂ν) - κ s * f (x - s) := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [hweak, mul_sub]
    _ = (∫ s, κ s * ∫ z, f (z - s) ∂ν) - ∫ s, κ s * f (x - s) :=
      integral_sub hν.1 hδ.1
    _ = (∫ y, ∫ z, κ (z - y) * f y ∂ν) - ∫ y, κ (x - y) * f y := by
      rw [hν.2.2, hδ.2.2]
    _ = ∫ y, ((∫ z, κ (z - y) * f y ∂ν) - κ (x - y) * f y) :=
      (integral_sub hν.2.1 hδ.2.1).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hνkernel, sub_mul]

/-- Bounded measurable weights can be smoothed against a finite, possibly
singular measure. Differentiation acts on the kernel alone. -/
theorem c16_weighted_smoothing_c1 {d : ℕ} (μ : Measure (Vec d))
    [IsFiniteMeasure μ] {a κ : Vec d → ℝ} (ha : Measurable a)
    (B K D : ℝ≥0) (hB : ∀ z, |a z| ≤ B)
    (hc : ContDiff ℝ 1 κ) (hK : ∀ w, |κ w| ≤ K)
    (hD : ∀ w, ‖fderiv ℝ κ w‖ ≤ D) :
    ContDiff ℝ 1 (fun y => ∫ z, a z * κ (z - y) ∂μ) ∧
    ∀ y, HasFDerivAt (fun v => ∫ z, a z * κ (z - v) ∂μ)
      (∫ z, a z • -(fderiv ℝ κ (z - y)) ∂μ) y := by
  have hkc := hc.continuous_fderiv (by norm_num)
  have hi (y : Vec d) : Integrable (fun z => a z * κ (z - y)) μ := by
    refine (integrable_const ((B : ℝ) * K)).mono'
      ((ha.mul (hc.continuous.measurable.comp
        (measurable_id.sub measurable_const))).aestronglyMeasurable) ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB z) (hK _) (abs_nonneg _) B.coe_nonneg
  have hdBound (z y : Vec d) :
      ‖a z • -(fderiv ℝ κ (z - y))‖ ≤ (B : ℝ) * D := by
    rw [norm_smul, Real.norm_eq_abs, norm_neg]
    exact mul_le_mul (hB z) (hD _) (norm_nonneg _) B.coe_nonneg
  have hdm (y : Vec d) : AEStronglyMeasurable
      (fun z => a z • -(fderiv ℝ κ (z - y))) μ :=
    (ha.smul ((hkc.comp (continuous_id.sub continuous_const)).neg.measurable)).aestronglyMeasurable
  have hd (y : Vec d) : HasFDerivAt (fun v => ∫ z, a z * κ (z - v) ∂μ)
      (∫ z, a z • -(fderiv ℝ κ (z - y)) ∂μ) y := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun v z => a z * κ (z - v))
      (F' := fun v z => a z • -(fderiv ℝ κ (z - v)))
      (s := Set.univ) (bound := fun _ => (B : ℝ) * D)
      Filter.univ_mem ?_ (hi y) (hdm y) ?_ (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun v => (hi v).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z v _ => hdBound z v
    · filter_upwards [] with z v _
      simpa [Function.comp_def] using
        ((((hc.differentiable (by norm_num)) (z - v)).hasFDerivAt.comp v
          ((hasFDerivAt_id v).const_sub z)).const_mul (a z))
  refine ⟨?_, hd⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y => (hd y).differentiableAt, ?_⟩
  have heq : fderiv ℝ (fun y => ∫ z, a z * κ (z - y) ∂μ) =
      fun y => ∫ z, a z • -(fderiv ℝ κ (z - y)) ∂μ :=
    funext fun y => (hd y).fderiv
  rw [heq]
  refine continuous_of_dominated (bound := fun _ : Vec d => (B : ℝ) * D)
    hdm (fun y => Filter.Eventually.of_forall fun z => hdBound z y)
    (integrable_const _) ?_
  exact Filter.Eventually.of_forall fun z =>
    (continuous_const : Continuous (fun _ : Vec d => a z)).smul
      ((hkc.comp ((continuous_const : Continuous (fun _ : Vec d => z)).sub continuous_id)).neg)

/-- One integration by parts with a compactly supported C1 test. -/
theorem c16_integral_mul_fderiv {d : ℕ} {a f : Vec d → ℝ}
    (ha : ContDiff ℝ 1 a) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (v : Vec d) :
    (∫ y, a y * fderiv ℝ f y v) = -∫ y, fderiv ℝ a y v * f y := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun y _ => (ha.differentiable (by norm_num)) y)
    (fun y _ => (hf.differentiable (by norm_num)) y)
  · exact ((((ha.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hf.continuous).integrable_of_hasCompactSupport hfc.mul_left)
  · exact ((ha.continuous.mul
      ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) v).mul_left)
  · exact (ha.continuous.mul hf.continuous).integrable_of_hasCompactSupport hfc.mul_left

/-- Coefficient-weighted normalized polynomial smoothing is C1 without assuming
that the finite measure has a density. The weight need only be bounded Borel. -/
theorem c16_normalized_weighted_smoothing_contDiff_one {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) (m : ℕ)
    {a : Vec d → ℝ} (ha : Measurable a) (B : ℝ≥0) (hB : ∀ z, |a z| ≤ B) :
    ContDiff ℝ 1 (fun y => ∫ z, a z * c16NormalizedPolynomialKernel r m (z - y) ∂μ) := by
  let K : ℝ≥0 := ⟨((r ^ 2)⁻¹) ^ m, by positivity⟩
  let D : ℝ≥0 := ⟨((d : ℝ) * (m : ℝ) / r) * K, by positivity⟩
  have hK (w : Vec d) : |c16PolynomialKernel r m w| ≤ K := by
    rw [abs_of_pos (c16_polynomial_kernel_pos hr m w)]
    exact c16_polynomial_kernel_le hr m w
  have hD (w : Vec d) : ‖fderiv ℝ (c16PolynomialKernel r m) w‖ ≤ D := by
    exact (c16_polynomial_kernel_fderiv_norm_le hr m w).trans
      (mul_le_mul_of_nonneg_left (c16_polynomial_kernel_le hr m w) (by positivity))
  have hraw := (c16_weighted_smoothing_c1 μ ha B K D hB
    ((c16_polynomial_kernel_contDiff hr m).of_le (by simp)) hK hD).1
  have heq : (fun y => ∫ z, a z * c16NormalizedPolynomialKernel r m (z - y) ∂μ) =
      fun y => (∫ w : Vec d, c16PolynomialKernel r m w)⁻¹ *
        ∫ z, a z * c16PolynomialKernel r m (z - y) ∂μ := by
    funext y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [c16NormalizedPolynomialKernel]
    ring
  rw [heq]
  exact contDiff_const.mul hraw

/-- Expand the convolved frozen generator into the smoothed coefficient and
drift entries. All summands are integrable against the supplied finite measure. -/
theorem c16_smoothed_generator_pointwise {d : ℕ} (μ : Measure (Vec d))
    {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ} (h : BddCoef A b M)
    {κ : Vec d → ℝ} (hc : Continuous κ) (h0 : ∀ w, 0 ≤ κ w)
    (f : Vec d → ℝ) (y : Vec d) (hi : Integrable (fun z => κ (z - y)) μ) :
    (∫ z, κ (z - y) * External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f y ∂μ) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (∫ z, A z i j * κ (z - y) ∂μ) *
        fderiv ℝ (fun w => fderiv ℝ f w (unitVector j)) y (unitVector i) +
      ∑ i, (∫ z, b z i * κ (z - y) ∂μ) * fderiv ℝ f y (unitVector i) := by
  let S (i j : Fin d) (z : Vec d) := A z i j * κ (z - y)
  let V (i : Fin d) (z : Vec d) := b z i * κ (z - y)
  let H (i j : Fin d) := fderiv ℝ (fun w => fderiv ℝ f w (unitVector j)) y (unitVector i)
  let J (i : Fin d) := fderiv ℝ f y (unitVector i)
  let B : ℝ≥0 := ⟨|M|, abs_nonneg M⟩
  have hS (i j : Fin d) : Integrable (S i j) μ :=
    (c16_bounded_smoothing_flux μ (h.Am i j) B
      (fun z => (h.Ab z i j).trans (le_abs_self M)) hc.measurable h0 y hi).1
  have hV (i : Fin d) : Integrable (V i) μ :=
    (c16_bounded_smoothing_flux μ (h.bm i) B
      (fun z => (h.bb z i).trans (le_abs_self M)) hc.measurable h0 y hi).1
  have hIH (i : Fin d) : Integrable (fun z => ∑ j, S i j z * H i j) μ :=
    integrable_finsetSum _ fun j _ => (hS i j).mul_const _
  have hII : Integrable (fun z => ∑ i, ∑ j, S i j z * H i j) μ :=
    integrable_finsetSum _ fun i _ => hIH i
  have hIJ : Integrable (fun z => ∑ i, V i z * J i) μ :=
    integrable_finsetSum _ fun i _ => (hV i).mul_const _
  have heq (z : Vec d) :
      κ (z - y) * External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f y =
        (1 / 2 : ℝ) * (∑ i, ∑ j, S i j z * H i j) + ∑ i, V i z * J i := by
    have hA : κ (z - y) * (∑ i, ∑ j, A z i j * H i j) =
        ∑ i, ∑ j, S i j z * H i j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [S]
      ring
    have hb : κ (z - y) * (∑ i, b z i * J i) = ∑ i, V i z * J i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [V]
      ring
    change κ (z - y) * ((1 / 2 : ℝ) * (∑ i, ∑ j, A z i j * H i j) +
      ∑ i, b z i * J i) = _
    rw [mul_add, mul_left_comm (κ (z - y)) (1 / 2 : ℝ), hA, hb]
  calc
    _ = ∫ z, (1 / 2 : ℝ) * (∑ i, ∑ j, S i j z * H i j) + ∑ i, V i z * J i ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j, (∫ z, S i j z ∂μ) * H i j +
        ∑ i, (∫ z, V i z ∂μ) * J i := by
      rw [integral_add (hII.const_mul _) hIJ, integral_const_mul,
        integral_finsetSum _ (fun i _ => hIH i),
        integral_finsetSum _ (fun i _ => (hV i).mul_const _)]
      simp_rw [integral_finsetSum _ (fun j _ => (hS _ j).mul_const _), integral_mul_const]

/-- One derivative transfers from a compact smooth test to the smoothed
coefficient entries, without differentiating the original coefficients. -/
theorem c16_smoothed_generator_divergence {d : ℕ} (μ : Measure (Vec d))
    [IsFiniteMeasure μ] {A : Vec d → Mat d} {b : Vec d → Vec d} {M : ℝ}
    (h : BddCoef A b M) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (hdm : (d : ℝ) < 2 * (m : ℝ)) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    (∫ y, ∫ z, κ (z - y) *
      External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f y ∂μ) =
      -((1 / 2 : ℝ) * ∑ i, ∑ j, ∫ y,
        fderiv ℝ (fun v => ∫ z, A z i j * κ (z - v) ∂μ) y (unitVector i) *
          fderiv ℝ f y (unitVector j)) +
        ∑ i, ∫ y, (∫ z, b z i * κ (z - y) ∂μ) * fderiv ℝ f y (unitVector i) := by
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let S (i j : Fin d) (y : Vec d) := ∫ z, A z i j * κ (z - y) ∂μ
  let V (i : Fin d) (y : Vec d) := ∫ z, b z i * κ (z - y) ∂μ
  let H (i j : Fin d) (y : Vec d) :=
    fderiv ℝ (fun w => fderiv ℝ f w (unitVector j)) y (unitVector i)
  let J (i : Fin d) (y : Vec d) := fderiv ℝ f y (unitVector i)
  let B : ℝ≥0 := ⟨|M|, abs_nonneg M⟩
  have hS (i j : Fin d) : ContDiff ℝ 1 (S i j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m (h.Am i j) B
      (fun z => (h.Ab z i j).trans (le_abs_self M))
  have hV (i : Fin d) : ContDiff ℝ 1 (V i) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m (h.bm i) B
      (fun z => (h.bb z i).trans (le_abs_self M))
  have hJ (j : Fin d) : ContDiff ℝ 1 (J j) :=
    (((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).of_le (by simp))
  have hIH (i j : Fin d) : Integrable (fun y => S i j y * H i j y) volume := by
    exact ((hS i j).continuous.mul
      (((hJ j).continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (((hfc.fderiv_apply (𝕜 := ℝ) (unitVector j)).fderiv_apply
          (𝕜 := ℝ) (unitVector i)).mul_left)
  have hIJ (i : Fin d) : Integrable (fun y => V i y * J i y) volume :=
    ((hV i).continuous.mul (hJ i).continuous).integrable_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) (unitVector i)).mul_left
  have hII (i : Fin d) : Integrable (fun y => ∑ j, S i j y * H i j y) volume :=
    integrable_finsetSum _ fun j _ => hIH i j
  have hIII : Integrable (fun y => ∑ i, ∑ j, S i j y * H i j y) volume :=
    integrable_finsetSum _ fun i _ => hII i
  have hIV : Integrable (fun y => ∑ i, V i y * J i y) volume :=
    integrable_finsetSum _ fun i _ => hIJ i
  obtain ⟨hpos, hκ, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have heq (y : Vec d) : (∫ z, κ (z - y) *
      External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f y ∂μ) =
      (1 / 2 : ℝ) * (∑ i, ∑ j, S i j y * H i j y) + ∑ i, V i y * J i y :=
    c16_smoothed_generator_pointwise μ h hκ.continuous (fun w => (hpos w).le) f y
      ((c16_polynomial_kernel_integrable hr m μ y).const_mul _)
  have hibp (i j : Fin d) : (∫ y, S i j y * H i j y) =
      -∫ y, fderiv ℝ (S i j) y (unitVector i) * J j y :=
    c16_integral_mul_fderiv (hS i j) (hJ j)
      (hfc.fderiv_apply (𝕜 := ℝ) (unitVector j)) (unitVector i)
  calc
    _ = ∫ y, (1 / 2 : ℝ) * (∑ i, ∑ j, S i j y * H i j y) +
        ∑ i, V i y * J i y := integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ y, S i j y * H i j y) +
        ∑ i, ∫ y, V i y * J i y := by
      rw [integral_add (hIII.const_mul _) hIV, integral_const_mul,
        integral_finsetSum _ (fun i _ => hII i), integral_finsetSum _ (fun i _ => hIJ i)]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => hIH i j)
    _ = _ := by
      simp_rw [hibp, Finset.sum_neg_distrib, mul_neg]
      rfl

/-- Divergence-form weak equation for the smoothed occupation of the same
supplied martingale law, with its actual endpoint law and starting atom. -/
theorem c16_textbook_occupation_smoothed_divergence {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (T : ℝ≥0) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y,
      fderiv ℝ (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k) *
        fderiv ℝ f y (unitVector j)) =
      (∑ k, ∫ y, (∫ z, forcedDrift (reducedCoefficient ω) i lam z k * κ (z - y) ∂μ) *
        fderiv ℝ f y (unitVector k)) -
      ∫ y, ((∫ γ, κ (γ T - y) ∂P) - κ (x - y)) * f y := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  obtain ⟨hpos, hκ, hκi, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hdiv := c16_smoothed_generator_divergence μ hcoef hr m hdm hf hfc
  have hweak := c16_textbook_occupation_smoothed_weak_equation hΛ hω i lam hP
    hκ.continuous (fun w => (hpos w).le) hκi hf hfc T
  have he := hdiv.symm.trans hweak
  dsimp only at he ⊢
  linarith only [he]

/-- A directional derivative of weighted smoothing is the integral of the
kernel derivative, with the sign from translation by minus the center. -/
theorem c16_weighted_smoothing_fderiv_apply {d : ℕ} (μ : Measure (Vec d))
    [IsFiniteMeasure μ] {a κ : Vec d → ℝ} (ha : Measurable a)
    (B K D : ℝ≥0) (hB : ∀ z, |a z| ≤ B)
    (hc : ContDiff ℝ 1 κ) (hK : ∀ w, |κ w| ≤ K)
    (hD : ∀ w, ‖fderiv ℝ κ w‖ ≤ D) (y v : Vec d) :
    Integrable (fun z => a z * fderiv ℝ κ (z - y) v) μ ∧
    fderiv ℝ (fun w => ∫ z, a z * κ (z - w) ∂μ) y v =
      -∫ z, a z * fderiv ℝ κ (z - y) v ∂μ := by
  have hkc := hc.continuous_fderiv (by norm_num)
  have hi : Integrable (fun z => a z • -(fderiv ℝ κ (z - y))) μ := by
    refine (integrable_const ((B : ℝ) * D)).mono'
      ((ha.smul ((hkc.comp (continuous_id.sub continuous_const)).neg.measurable)).aestronglyMeasurable) ?_
    filter_upwards [] with z
    rw [norm_smul, Real.norm_eq_abs, norm_neg]
    exact mul_le_mul (hB z) (hD _) (norm_nonneg _) B.coe_nonneg
  have hie := hi.apply_continuousLinearMap v
  have heval (z : Vec d) : (a z • -(fderiv ℝ κ (z - y))) v =
      -(a z * fderiv ℝ κ (z - y) v) := by simp
  refine ⟨?_, ?_⟩
  · exact hie.neg.congr (Filter.Eventually.of_forall fun z => by simp)
  · rw [((c16_weighted_smoothing_c1 μ ha B K D hB hc hK hD).2 y).fderiv,
      ContinuousLinearMap.integral_apply hi v]
    simp_rw [heval]
    exact integral_neg _

/-- The normalized polynomial kernel and its full derivative have global
bounds at every fixed positive scale. -/
theorem c16_normalized_polynomial_kernel_bounded {d : ℕ} {r : ℝ}
    (hr : 0 < r) (m : ℕ) :
    ∃ K D : ℝ≥0,
      (∀ w : Vec d, |c16NormalizedPolynomialKernel r m w| ≤ K) ∧
      ∀ w : Vec d, ‖fderiv ℝ (c16NormalizedPolynomialKernel r m) w‖ ≤ D := by
  let c : ℝ := (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹
  let K : ℝ≥0 := ⟨|c| * ((r ^ 2)⁻¹) ^ m, by positivity⟩
  let D : ℝ≥0 := ⟨|c| * (((d : ℝ) * (m : ℝ) / r) * ((r ^ 2)⁻¹) ^ m),
    by positivity⟩
  refine ⟨K, D, ?_, ?_⟩
  · intro w
    change |c * c16PolynomialKernel r m w| ≤ (K : ℝ)
    rw [abs_mul, abs_of_pos (c16_polynomial_kernel_pos hr m w)]
    exact mul_le_mul_of_nonneg_left (c16_polynomial_kernel_le hr m w) (abs_nonneg c)
  · intro w
    change ‖fderiv ℝ (fun z => c * c16PolynomialKernel r m z) w‖ ≤ (D : ℝ)
    rw [fderiv_const_mul ((c16_polynomial_kernel_contDiff hr m).differentiable (by simp) w) c,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      ((c16_polynomial_kernel_fderiv_norm_le hr m w).trans
        (mul_le_mul_of_nonneg_left (c16_polynomial_kernel_le hr m w) (by positivity)))
      (abs_nonneg c)

/-- Directional differentiation of normalized weighted smoothing requires no
density of the original measure. -/
theorem c16_normalized_weighted_smoothing_fderiv_apply {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) (m : ℕ)
    {a : Vec d → ℝ} (ha : Measurable a) (B : ℝ≥0) (hB : ∀ z, |a z| ≤ B)
    (y v : Vec d) :
    Integrable (fun z => a z *
      fderiv ℝ (c16NormalizedPolynomialKernel r m) (z - y) v) μ ∧
    fderiv ℝ (fun w => ∫ z, a z * c16NormalizedPolynomialKernel r m (z - w) ∂μ) y v =
      -∫ z, a z * fderiv ℝ (c16NormalizedPolynomialKernel r m) (z - y) v ∂μ := by
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hc : ContDiff ℝ 1 (c16NormalizedPolynomialKernel (d := d) r m) :=
    contDiff_const.mul ((c16_polynomial_kernel_contDiff hr m).of_le (by simp))
  exact c16_weighted_smoothing_fderiv_apply μ ha B K D hB hc hK hD y v

/-- Separate a bounded Borel weight at the smoothing center from its coordinate
commutator. No Lipschitz or density assumption is required for the identity. -/
theorem c16_weighted_smoothing_coordinate_commutator {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) (m : ℕ)
    {a : Vec d → ℝ} (ha : Measurable a) (B : ℝ≥0) (hB : ∀ z, |a z| ≤ B)
    (y : Vec d) (j : Fin d) :
    let κ := c16NormalizedPolynomialKernel r m
    fderiv ℝ (fun v => ∫ z, a z * κ (z - v) ∂μ) y (unitVector j) =
      a y * fderiv ℝ (fun v => ∫ z, κ (z - v) ∂μ) y (unitVector j) -
        ∫ z, (a z - a y) * fderiv ℝ κ (z - y) (unitVector j) ∂μ := by
  let κ := c16NormalizedPolynomialKernel (d := d) r m
  obtain ⟨hi, hd⟩ := c16_normalized_weighted_smoothing_fderiv_apply μ hr m
    ha B hB y (unitVector j)
  obtain ⟨hi1, hd1⟩ := c16_normalized_weighted_smoothing_fderiv_apply μ hr m
    (a := fun _ => 1) measurable_const 1 (by intro z; simp) y (unitVector j)
  simp only [one_mul] at hi1 hd1
  have he : (∫ z, (a z - a y) * fderiv ℝ κ (z - y) (unitVector j) ∂μ) =
      (∫ z, a z * fderiv ℝ κ (z - y) (unitVector j) ∂μ) -
        a y * ∫ z, fderiv ℝ κ (z - y) (unitVector j) ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hi (hi1.const_mul (a y)), integral_const_mul]
  dsimp only
  rw [hd, hd1, he]
  ring

/-- The coefficient derivative splits into the principal smoothed gradient and
a commutator controlled uniformly in the positive smoothing scale. -/
theorem c16_normalized_smoothing_derivative_commutator {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {a : Vec d → ℝ} {L : ℝ≥0}
    (hLip : LipschitzWith L a) (B : ℝ≥0) (hB : ∀ z, |a z| ≤ B)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    (y : Vec d) (l : Fin d) :
    let κ := c16NormalizedPolynomialKernel (d := d) r m
    let u := fun w => ∫ z, κ (z - w) ∂μ
    let q := -∫ z, (a z - a y) * fderiv ℝ κ (z - y) (unitVector l) ∂μ
    fderiv ℝ (fun w => ∫ z, a z * κ (z - w) ∂μ) y (unitVector l) =
        a y * fderiv ℝ u y (unitVector l) + q ∧
      |q| ≤ (L : ℝ) * (2 * (m : ℝ)) * u y := by
  let κ := c16NormalizedPolynomialKernel (d := d) r m
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hκi : Integrable (fun z => κ (z - y)) μ := by
    refine (integrable_const (K : ℝ)).mono' ?_ ?_
    · exact (((c16_normalized_polynomial_kernel_properties hr m hdm).2.1.continuous.measurable.comp
        (measurable_id.sub measurable_const)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hK _)
  have hgrad (w : Vec d) :
      ‖w‖ * |fderiv ℝ κ w (unitVector l)| ≤ ((2 * (m : ℝ≥0) : ℝ≥0) : ℝ) * κ w := by
    simpa using c16_normalized_polynomial_kernel_derivative_bound hr m hdm w l
  have hq := (c16_lipschitz_coefficient_smoothing_commutator
    hLip l μ κ (2 * (m : ℝ≥0)) hgrad y hκi).2
  dsimp only
  constructor
  · simpa only [sub_eq_add_neg] using
      c16_weighted_smoothing_coordinate_commutator μ hr m
        hLip.continuous.measurable B hB y l
  · simpa using hq

open PDE PDE.Parabolic.Energy Metric Set Filter in
/-- Smooth approximation of a compact C1 test, with common compact support. -/
private theorem c16_compact_C1_test_approximation {d : ℕ} {φ : EinsteinRelation.Vec d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    {K : Set (EinsteinRelation.Vec d)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ)
    (hδK : cthickening δ (tsupport φ) ⊆ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : EinsteinRelation.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ K ∧ (∀ x, |φ x - ψ x| ≤ ε) ∧
      ∀ j x, |coordinateDerivative j φ x - coordinateDerivative j ψ x| ≤ ε := by
  let Dφ : Fin d → EinsteinRelation.Vec d → ℝ := fun j x => fderiv ℝ φ x (basisVec j)
  have hDc (j : Fin d) : Continuous (Dφ j) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDzero (j : Fin d) (x : EinsteinRelation.Vec d) (hx : x ∉ tsupport φ) : Dφ j x = 0 := by
    simp [Dφ, fderiv_of_notMem_tsupport ℝ hx]
  have hDcs (j : Fin d) : HasCompactSupport (Dφ j) := by
    refine HasCompactSupport.of_support_subset_isCompact hφc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (hDzero j x h)
  obtain ⟨a₀, ha₀, hclose₀⟩ :=
    exists_forall_dist_wholeSpaceMollify_le hφ.continuous hφc hε
  have hex (j : Fin d) := exists_forall_dist_wholeSpaceMollify_le (hDc j) (hDcs j) hε
  choose a₁ ha₁ hclose₁ using hex
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      0 < a ∧ a ≤ δ ∧ a ≤ a₀ ∧ ∀ j, a ≤ a₁ j := by
    have hall : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ j, a ≤ a₁ j := by
      rw [eventually_all]
      intro j
      filter_upwards [Ioc_mem_nhdsGT (ha₁ j)] with a ha using ha.2
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hδ,
      Ioc_mem_nhdsGT ha₀, hall] with a ha hδa h₀a h₁a
    exact ⟨ha, hδa.2, h₀a.2, h₁a⟩
  obtain ⟨a, ha, haδ, haa₀, haa₁⟩ := hev.exists
  let ψ := wholeSpaceMollify a φ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := moll_contDiff ha hφ.continuous.locallyIntegrable
  have hsupp : Function.support ψ ⊆ cthickening a (tsupport φ) :=
    PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening ha
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact (hφc.isCompact.cthickening (r := a)) hsupp
  have hψK : tsupport ψ ⊆ K :=
    closure_minimal (hsupp.trans ((cthickening_mono haδ _).trans hδK)) hK.isClosed
  refine ⟨ψ, hψ, hψc, hψK, ?_, ?_⟩
  · intro x
    have hb := hclose₀ a ha haa₀ x
    rwa [Real.dist_eq, abs_sub_comm] at hb
  · intro j x
    have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
    have hd : fderiv ℝ ψ x (basisVec j) = wholeSpaceMollify a (Dφ j) x :=
      congrFun (euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
        (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha)
        (contDiff_scaledConvexApproxKernel hρ _) hφ.continuous.locallyIntegrable
        (HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := j) hφ)) x
    have hb := hclose₁ j a ha (haa₁ j) x
    rw [Real.dist_eq, abs_sub_comm] at hb
    rw [← hd] at hb
    simpa only [coordinateDerivative, unitVector, basisVec, Dφ] using hb


open Set Filter Metric in
/-- A weak divergence identity extends from smooth tests to compact C1 tests. -/
theorem c16_weak_divergence_C1 {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {F : Vec d → Vec d} {g : Vec d → ℝ} (hw : HasWeakDivergence U F g)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ interior U) :
    (∫ x in U, dot (F x) (gradient φ x)) = -(∫ x in U, g x * φ x) := by
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open isOpen_interior hφU
  let K := Metric.cthickening δ (tsupport φ)
  have hK : IsCompact K := hφc.isCompact.cthickening
  have hKU : K ⊆ U := hδU.trans interior_subset
  have hφK : tsupport φ ⊆ K := Metric.self_subset_cthickening _
  have hF (j : Fin d) : Integrable (fun x => F x j) (volume.restrict K) :=
    (hw.1 j).integrableOn_compact_subset hKU hK
  have hg : Integrable g (volume.restrict K) :=
    hw.2.1.integrableOn_compact_subset hKU hK
  have hbd {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
      (hq : Continuous q) (hqc : HasCompactSupport q) :
      Integrable (fun x => f x * q x) (volume.restrict K) := by
    obtain ⟨C, hC⟩ := hq.bounded_above_of_compact_support hqc
    exact hf.mul_bdd hq.aestronglyMeasurable (c := C) (Eventually.of_forall hC)
  have hder {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q)
      (j : Fin d) : Continuous (coordinateDerivative j q) ∧
      HasCompactSupport (coordinateDerivative j q) := by
    refine ⟨(hq.continuous_fderiv one_ne_zero).clm_apply continuous_const, ?_⟩
    refine HasCompactSupport.of_support_subset_isCompact hqc.isCompact ?_
    intro x hx
    by_contra h
    exact hx (by simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ h])
  have hcut {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, dot (F x) (gradient q x)) =
        ∫ x in K, dot (F x) (gradient q x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    have hxq : x ∉ tsupport q := fun h => hx.2 (hqK h)
    simp [dot, gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxq]
  have hcutg {q : Vec d → ℝ} (hqK : tsupport q ⊆ K) :
      (∫ x in U, g x * q x) = ∫ x in K, g x * q x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hKU
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hqK h)), mul_zero]
  have hsum {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ x in K, dot (F x) (gradient q x)) =
        ∑ j, ∫ x in K, F x j * coordinateDerivative j q x := by
    exact integral_finsetSum _ (fun j _ => hbd (hF j) (hder hq hqc j).1
      (hder hq hqc j).2)
  let E := (∫ x in K, dot (F x) (gradient φ x)) + ∫ x in K, g x * φ x
  let C := (∑ j, ∫ x in K, |F x j|) + ∫ x in K, |g x|
  have hmain (ε : ℝ) (hε : 0 < ε) : |E| ≤ ε * C := by
    obtain ⟨ψ, hψ, hψc, hψK, hclose, hDclose⟩ :=
      c16_compact_C1_test_approximation hφ hφc hK hδ (Subset.refl K) hε
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
    have hid := hw.2.2 ψ ⟨hψ, hψc, hψK.trans hKU⟩
    rw [hcut hψK, hcutg hψK] at hid
    have hdiff : E = (∑ j, ∫ x in K, F x j *
        (coordinateDerivative j φ x - coordinateDerivative j ψ x)) +
        ∫ x in K, g x * (φ x - ψ x) := by
      simp_rw [mul_sub]
      rw [integral_sub (hbd hg hφ.continuous hφc) (hbd hg hψ.continuous hψc)]
      have hj (j : Fin d) := integral_sub
        (hbd (hF j) (hder hφ hφc j).1 (hder hφ hφc j).2)
        (hbd (hF j) (hder hψ1 hψc j).1 (hder hψ1 hψc j).2)
      simp_rw [hj]
      rw [Finset.sum_sub_distrib, ← hsum hφ hφc, ← hsum hψ1 hψc]
      dsimp [E]
      linarith
    have hb {f q : Vec d → ℝ} (hf : Integrable f (volume.restrict K))
        (hq : ∀ x, |q x| ≤ ε) :
        |∫ x in K, f x * q x| ≤ ε * ∫ x in K, |f x| := by
      calc
        |∫ x in K, f x * q x| ≤ ∫ x in K, |f x * q x| :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x in K, ε * |f x| := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hf.abs.const_mul ε) (Eventually.of_forall ?_)
          intro x
          change |f x * q x| ≤ ε * |f x|
          rw [abs_mul]
          nlinarith [hq x, abs_nonneg (f x)]
        _ = ε * ∫ x in K, |f x| := integral_const_mul _ _
    rw [hdiff]
    calc
      _ ≤ |∑ j, ∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)| +
          |∫ x in K, g x * (φ x - ψ x)| := abs_add_le _ _
      _ ≤ (∑ j, |∫ x in K, F x j *
          (coordinateDerivative j φ x - coordinateDerivative j ψ x)|) +
          |∫ x in K, g x * (φ x - ψ x)| :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
      _ ≤ (∑ j, ε * ∫ x in K, |F x j|) + ε * ∫ x in K, |g x| :=
        add_le_add (Finset.sum_le_sum fun j _ => hb (hF j) (hDclose j)) (hb hg hclose)
      _ = ε * C := by rw [← Finset.mul_sum]; dsimp [C]; ring
  have hC : 0 ≤ C := add_nonneg
    (Finset.sum_nonneg fun j _ => integral_nonneg fun x => abs_nonneg _)
    (integral_nonneg fun x => abs_nonneg _)
  have hE : E = 0 := by
    by_contra hne
    have hpos := abs_pos.mpr hne
    have hb := hmain (|E| / (2 * (C + 1))) (by positivity)
    have hh : |E| / (2 * (C + 1)) * C < |E| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hcut hφK, hcutg hφK]
  dsimp [E] at hE
  linarith

/-- The smoothed occupation equation holds for compact C1 tests of the same
supplied martingale law. The extension uses continuous fluxes, not a density
assumption on its occupation measure. -/
theorem c16_textbook_occupation_smoothed_divergence_C1 {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (T : ℝ≥0) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y,
      fderiv ℝ (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k) *
        fderiv ℝ f y (unitVector j)) =
      (∑ k, ∫ y, (∫ z, forcedDrift (reducedCoefficient ω) i lam z k * κ (z - y) ∂μ) *
        fderiv ℝ f y (unitVector k)) -
      ∫ y, ((∫ γ, κ (γ T - y) ∂P) - κ (x - y)) * f y := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let S (k j : Fin d) (y : Vec d) := ∫ z, reducedCoefficient ω z k j * κ (z - y) ∂μ
  let V (j : Fin d) (y : Vec d) :=
    ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
  let H (k j : Fin d) (y : Vec d) := fderiv ℝ (S k j) y (unitVector k)
  let F : Vec d → Vec d := fun y j => (1 / 2 : ℝ) * (∑ k, H k j y) - V j y
  let ρ (y : Vec d) := (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hS (k j : Fin d) : ContDiff ℝ 1 (S k j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m (hA.matrix_elem k j).measurable
      ⟨|Ma|, abs_nonneg Ma⟩ (fun z => (hAb z k j).trans (le_abs_self Ma))
  have hV (j : Fin d) : ContDiff ℝ 1 (V j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m
      ((measurable_pi_apply j).comp hb) ⟨|Mb|, abs_nonneg Mb⟩
      (fun z => (hbb z j).trans (le_abs_self Mb))
  have hH (k j : Fin d) : Continuous (H k j) :=
    ((hS k j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF (j : Fin d) : Continuous (fun y => F y j) :=
    (continuous_const.mul (continuous_finsetSum _ fun k _ => hH k j)).sub (hV j).continuous
  obtain ⟨_, hκ, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hρ : Continuous ρ := by
    apply Continuous.sub ?_ (hκ.continuous.comp (continuous_const.sub continuous_id))
    refine continuous_of_dominated (bound := fun _ : Path d => (K : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · intro y
      exact ((hκ.continuous.measurable.comp
        (((continuous_eval.comp (continuous_id.prodMk continuous_const)).measurable).sub
          measurable_const)).aestronglyMeasurable)
    · intro y
      exact Filter.Eventually.of_forall fun γ => (Real.norm_eq_abs _).trans_le (hK _)
    · exact Filter.Eventually.of_forall fun γ =>
        hκ.continuous.comp (continuous_const.sub continuous_id)
  have hpair {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ y, dot (F y) (gradient q y)) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j) := by
    have hI (k j : Fin d) : Integrable (fun y => H k j y * fderiv ℝ q y (unitVector j)) :=
      ((hH k j).mul ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hIV (j : Fin d) : Integrable (fun y => V j y * fderiv ℝ q y (unitVector j)) :=
      ((hV j).continuous.mul
        ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
          (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hII (k : Fin d) := integrable_finsetSum Finset.univ (fun j _ => hI k j)
    have hIII := integrable_finsetSum Finset.univ (fun k _ => hII k)
    have hIVs := integrable_finsetSum Finset.univ (fun j _ => hIV j)
    have hp (y : Vec d) : dot (F y) (gradient q y) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, V j y * fderiv ℝ q y (unitVector j) := by
      dsimp only [F, dot, gradient, coordinateDerivative]
      simp_rw [sub_mul, mul_assoc, Finset.sum_mul, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hp), integral_sub (hIII.const_mul _) hIVs,
      integral_const_mul, integral_finsetSum _ (fun j _ => hIV j),
      integral_finsetSum _ (fun k _ => hII k)]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finsetSum _ (fun j _ => hI k j)
  have hw : HasWeakDivergence Set.univ F ρ := by
    refine ⟨fun j => (hF j).locallyIntegrable.locallyIntegrableOn _,
      hρ.locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro q hq
    simp only [Measure.restrict_univ]
    rw [hpair (hq.1.of_le (by simp)) hq.2.1]
    have he := c16_textbook_occupation_smoothed_divergence hΛ hω i lam hP
      hr m hdm hq.1 hq.2.1 T
    dsimp only at he
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) = -(∫ y, ρ y * q y)
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) =
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) - (∫ y, ρ y * q y) at he
    linarith only [he]
  have he := c16_weak_divergence_C1 MeasurableSet.univ hw hf hfc (by simp)
  simp only [Measure.restrict_univ] at he
  rw [hpair hf hfc] at he
  dsimp only
  change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ f y (unitVector j)) =
    (∑ j, ∫ y, V j y * fderiv ℝ f y (unitVector j)) - (∫ y, ρ y * f y)
  linarith only [he]

/-- Integrable flux and divergence allow bounded C1 tests with bounded derivative.
Expanding compact cutoffs remove the support restriction. -/
theorem c16_weak_divergence_bounded_C1 {d : ℕ}
    {F : Vec d → Vec d} {g : Vec d → ℝ} (hw : HasWeakDivergence Set.univ F g)
    (hF : ∀ j, Integrable (fun y => F y j)) (hg : Integrable g)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) {B : ℝ}
    (hB : ∀ y, ‖f y‖ ≤ B ∧ ‖fderiv ℝ f y‖ ≤ B) :
    (∫ y, dot (F y) (gradient f y)) = -(∫ y, g y * f y) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0).1
  obtain ⟨χ, hχ, ⟨C, hC⟩, hlocal⟩ :=
    c16_exists_bounded_smooth_cutoffs (f := fun _ : Vec d => (1 : ℝ)) contDiff_const
      (B := 1) (by intro k hk y; interval_cases k <;> simp [iteratedFDeriv_succ_const])
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 0 (by omega) 0)
  have hχv (n : ℕ) (y : Vec d) : ‖χ n y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using hC n 0 (by omega) y
  have hχD (n : ℕ) (y : Vec d) : ‖fderiv ℝ (χ n) y‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using hC n 1 (by omega) y
  let ψ : ℕ → Vec d → ℝ := fun n y => χ n y * f y
  have hψ (n : ℕ) : ContDiff ℝ 1 (ψ n) := ((hχ n).1.of_le (by simp)).mul hf
  have hψc (n : ℕ) : HasCompactSupport (ψ n) := (hχ n).2.mul_right
  have hψv (n : ℕ) (y : Vec d) : ‖ψ n y‖ ≤ C * B := by
    exact (norm_mul_le _ _).trans (mul_le_mul (hχv n y) (hB y).1
      (norm_nonneg _) hC0)
  have hψD (n : ℕ) (y : Vec d) : ‖fderiv ℝ (ψ n) y‖ ≤ 2 * C * B := by
    rw [show ψ n = fun y => χ n y * f y from rfl,
      fderiv_fun_mul ((hχ n).1.differentiable (by simp) y) (hf.differentiable one_ne_zero y)]
    calc
      _ ≤ ‖χ n y • fderiv ℝ f y‖ + ‖f y • fderiv ℝ (χ n) y‖ := norm_add_le _ _
      _ = ‖χ n y‖ * ‖fderiv ℝ f y‖ + ‖f y‖ * ‖fderiv ℝ (χ n) y‖ := by
        rw [norm_smul, norm_smul]
      _ ≤ C * B + B * C := add_le_add
        (mul_le_mul (hχv n y) (hB y).2 (norm_nonneg _) hC0)
        (mul_le_mul (hB y).1 (hχD n y) (norm_nonneg _) hB0)
      _ = 2 * C * B := by ring
  have hcoord {q : Vec d → ℝ} {M : ℝ} (hM : ∀ y, ‖fderiv ℝ q y‖ ≤ M)
      (y : Vec d) (j : Fin d) : |fderiv ℝ q y (unitVector j)| ≤ M := by
    apply le_trans ?_ (hM y)
    simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
      (fderiv ℝ q y).le_opNorm (unitVector j)
  have hprod {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) {M : ℝ}
      (hM : ∀ y, ‖fderiv ℝ q y‖ ≤ M) (j : Fin d) :
      Integrable (fun y => F y j * fderiv ℝ q y (unitVector j)) :=
    (hF j).mul_bdd
      ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hcoord hM y j)
  have hsum {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) {M : ℝ}
      (hM : ∀ y, ‖fderiv ℝ q y‖ ≤ M) :
      (∫ y, dot (F y) (gradient q y)) =
        ∑ j, ∫ y, F y j * fderiv ℝ q y (unitVector j) :=
    integral_finsetSum _ (fun j _ => hprod hq hM j)
  have hlocalψ (y : Vec d) : ∀ᶠ n in Filter.atTop, ψ n =ᶠ[𝓝 y] f := by
    filter_upwards [hlocal y] with n hn
    filter_upwards [hn] with z hz
    dsimp only [ψ]
    rw [hz, one_mul]
  have hlimD (j : Fin d) : Filter.Tendsto
      (fun n => ∫ y, F y j * fderiv ℝ (ψ n) y (unitVector j)) Filter.atTop
      (𝓝 (∫ y, F y j * fderiv ℝ f y (unitVector j))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => |F y j| * (2 * C * B))
      (fun n => (hprod (hψ n) (hψD n) j).aestronglyMeasurable)
      ((hF j).abs.mul_const _) (fun n => Filter.Eventually.of_forall ?_) ?_
    · intro y
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hcoord (hψD n) y j) (abs_nonneg _)
    · refine Filter.Eventually.of_forall fun y => ?_
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hlocalψ y] with n hn
      rw [hn.fderiv_eq]
  have hlimv : Filter.Tendsto (fun n => ∫ y, g y * ψ n y) Filter.atTop
      (𝓝 (∫ y, g y * f y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => |g y| * (C * B))
      (fun n => hg.aestronglyMeasurable.mul (hψ n).continuous.aestronglyMeasurable)
      (hg.abs.mul_const _) (fun n => Filter.Eventually.of_forall ?_) ?_
    · intro y
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hψv n y)
        (abs_nonneg _)
    · refine Filter.Eventually.of_forall fun y => ?_
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hlocalψ y] with n hn
      rw [hn.eq_of_nhds]
  have heq (n : ℕ) : (∑ j, ∫ y, F y j * fderiv ℝ (ψ n) y (unitVector j)) =
      -(∫ y, g y * ψ n y) := by
    have he := c16_weak_divergence_C1 MeasurableSet.univ hw (hψ n) (hψc n) (by simp)
    simpa only [Measure.restrict_univ, hsum (hψ n) (hψD n)] using he
  rw [hsum hf (fun y => (hB y).2)]
  exact tendsto_nhds_unique (tendsto_finsetSum _ (fun j _ => hlimD j))
    (hlimv.neg.congr fun n => (heq n).symm)

/-- The bounded increasing entropy test has precisely the reciprocal weight
needed to control the nonlinear gradient energy. -/
theorem c16_nonlinear_entropy_test {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y) {α : ℝ} (hα : 0 < α) :
    ContDiff ℝ 1 (fun y => 1 - (1 + u y) ^ (-α)) ∧
    (∀ y, 0 ≤ 1 - (1 + u y) ^ (-α) ∧ 1 - (1 + u y) ^ (-α) ≤ 1) ∧
    ∀ y, fderiv ℝ (fun z => 1 - (1 + u z) ^ (-α)) y =
      (α / (1 + u y) ^ (1 + α)) • fderiv ℝ u y := by
  have hpos (y : Vec d) : 0 < 1 + u y := by linarith [hu0 y]
  refine ⟨contDiff_const.sub ((contDiff_const.add hu).rpow_const_of_ne
    (fun y => (hpos y).ne')), ?_, ?_⟩
  · intro y
    have hp := Real.rpow_nonneg (hpos y).le (-α)
    have hle := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hu0 y] : 1 ≤ 1 + u y)
      (by linarith : -α ≤ 0)
    constructor <;> linarith
  · intro y
    have hd := (((hu.differentiable one_ne_zero y).hasFDerivAt.const_add 1).rpow_const
      (p := -α) (Or.inl (hpos y).ne')).const_sub 1
    have hc : -((-α) * (1 + u y) ^ (-α - 1)) = α / (1 + u y) ^ (1 + α) := by
      rw [show -α - 1 = -(1 + α) by ring, Real.rpow_neg (hpos y).le]
      ring
    have he := hd.fderiv
    rw [← neg_smul, hc] at he
    exact he

/-- The quadratic lower-order term in the entropy estimate is controlled by
the mass of the smoothed occupation measure. -/
theorem c16_nonlinear_weight_mass_bound {t α : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α) :
    t ^ 2 / (1 + t) ^ (1 + α) ≤ t := by
  have hp : 0 < 1 + t := by linarith
  have hd : 1 + t ≤ (1 + t) ^ (1 + α) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ 1 + t) (by linarith : (1 : ℝ) ≤ 1 + α)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).2
  nlinarith [mul_le_mul_of_nonneg_left hd ht]

/-- Endpoint and starting-point convolutions have total L1 discrepancy at most
two, uniformly over scale, time, starting point and the supplied probability law. -/
theorem c16_probability_smoothed_endpoint_l1 {d : ℕ} (P : Measure (Path d))
    [IsProbabilityMeasure P] (T : ℝ≥0) (x : Vec d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    let κ := c16NormalizedPolynomialKernel r m
    let ρ : Vec d → ℝ := fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
    Integrable ρ volume ∧ (∫ y, |ρ y|) ≤ 2 := by
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let ν : Measure (Vec d) := Measure.map (fun γ : Path d => γ T) P
  obtain ⟨hpos, hc, hi, hmass⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have heq : (fun y => ∫ γ, κ (γ T - y) ∂P) = fun y => ∫ z, κ (z - y) ∂ν := by
    funext y
    exact (integral_map (measurable_pathPosition T).aemeasurable
      (hc.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable).symm
  have hs := c16_normalized_polynomial_smoothing_mass ν hr m hdm
  have hx : Integrable (fun y => κ (x - y)) := hi.comp_sub_left x
  have hxmass : (∫ y, κ (x - y)) = 1 :=
    (integral_sub_left_eq_self κ volume x).trans hmass
  have hνmass : (∫ y, ∫ z, κ (z - y) ∂ν) = 1 := by simpa using hs.2
  change Integrable (fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)) volume ∧
    (∫ y, |(∫ γ, κ (γ T - y) ∂P) - κ (x - y)|) ≤ 2
  simp_rw [congrFun heq]
  refine ⟨hs.1.sub hx, ?_⟩
  calc
    _ ≤ ∫ y, (∫ z, κ (z - y) ∂ν) + κ (x - y) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
        (hs.1.add hx) (Filter.Eventually.of_forall ?_)
      intro y
      exact (abs_sub _ _).trans_eq (by
        rw [abs_of_nonneg (integral_nonneg fun z => (hpos _).le), abs_of_pos (hpos _)]
        rfl)
    _ = 2 := by rw [integral_add hs.1 hx, hνmass, hxmass]; norm_num

/-- Smoothing a finite measure gives a globally bounded derivative at each fixed
positive scale. This bound is used only to justify the bounded entropy test. -/
theorem c16_normalized_polynomial_smoothing_fderiv_bounded {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖fderiv ℝ
      (fun v => ∫ z, c16NormalizedPolynomialKernel r m (z - v) ∂μ) y‖ ≤ B := by
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hc : ContDiff ℝ 1 (c16NormalizedPolynomialKernel (d := d) r m) :=
    contDiff_const.mul ((c16_polynomial_kernel_contDiff hr m).of_le (by simp))
  have hd := (c16_weighted_smoothing_c1 μ (a := fun _ => 1) measurable_const
    1 K D (by intro z; simp) hc hK hD).2
  simp only [one_mul, one_smul] at hd
  refine ⟨(D : ℝ) * μ.real Set.univ, mul_nonneg D.coe_nonneg measureReal_nonneg, ?_⟩
  intro y
  rw [(hd y).fderiv]
  exact norm_integral_le_of_norm_le_const
    (Filter.Eventually.of_forall fun z => by simpa only [norm_neg] using hD (z - y))

/-- At a fixed scale, an integrable bounded gradient makes the weighted
quadratic energy integrable. No estimate uniform in the scale is asserted here. -/
theorem c16_nonlinear_energy_integrable {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    (hDu : Integrable (fderiv ℝ u)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, ‖fderiv ℝ u y‖ ≤ B) {α : ℝ} (hα : 0 ≤ α) :
    Integrable (fun y => euclideanSq (fun j : Fin d =>
      fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + α)) volume := by
  have hpos (y : Vec d) : 0 < (1 + u y) ^ (1 + α) :=
    Real.rpow_pos_of_pos (by linarith [hu0 y]) _
  have hden (y : Vec d) : 1 ≤ (1 + u y) ^ (1 + α) :=
    Real.one_le_rpow (by linarith [hu0 y]) (by linarith)
  have hc (j : Fin d) : Continuous (fun y => fderiv ℝ u y (unitVector j)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have he : Continuous (fun y => euclideanSq (fun j : Fin d =>
      fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + α)) := by
    apply Continuous.div ?_
      ((continuous_const.add hu.continuous).rpow_const (fun y => Or.inl (by
        change 1 + u y ≠ 0
        linarith [hu0 y])))
      (fun y => (hpos y).ne')
    change Continuous (fun y => ∑ j : Fin d,
      fderiv ℝ u y (unitVector j) * fderiv ℝ u y (unitVector j))
    exact continuous_finsetSum _ (fun j _ => (hc j).mul (hc j))
  apply (hDu.norm.const_mul ((d : ℝ) * B)).mono' he.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun y => ?_
  have hS0 : 0 ≤ euclideanSq (fun j : Fin d => fderiv ℝ u y (unitVector j)) := by
    change 0 ≤ ∑ j : Fin d, fderiv ℝ u y (unitVector j) * fderiv ℝ u y (unitVector j)
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hcoord (j : Fin d) : |fderiv ℝ u y (unitVector j)| ≤ ‖fderiv ℝ u y‖ := by
    simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
      (fderiv ℝ u y).le_opNorm (unitVector j)
  have hS : euclideanSq (fun j : Fin d => fderiv ℝ u y (unitVector j)) ≤
      (d : ℝ) * B * ‖fderiv ℝ u y‖ := by
    calc
      _ ≤ ∑ j : Fin d, B * ‖fderiv ℝ u y‖ := by
        change (∑ j : Fin d, fderiv ℝ u y (unitVector j) *
          fderiv ℝ u y (unitVector j)) ≤ _
        apply Finset.sum_le_sum
        intro j _
        calc
          _ = |fderiv ℝ u y (unitVector j)| * |fderiv ℝ u y (unitVector j)| := by
            rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
          _ ≤ B * ‖fderiv ℝ u y‖ :=
            mul_le_mul ((hcoord j).trans (hB y)) (hcoord j) (abs_nonneg _) hB0
      _ = (d : ℝ) * B * ‖fderiv ℝ u y‖ := by simp; ring
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hS0 (hpos y).le)]
  exact (div_le_self hS0 (hden y)).trans hS

/-- A coordinatewise lower-order flux bound is absorbed by Euclidean ellipticity.
The coefficient in the remaining mass term is independent of smoothing scale. -/
theorem c16_elliptic_flux_coercivity {d : ℕ} (A : Mat d) (v F : Vec d)
    {u c M : ℝ} (hc : 0 < c)
    (hell : c * euclideanSq v ≤ dot v (A.mulVec v))
    (hF : ∀ j, |F j - (1 / 2 : ℝ) * ∑ k, A k j * v k| ≤ M * u) :
    (c / 4) * euclideanSq v - (d : ℝ) * (M ^ 2 / c) * u ^ 2 ≤ dot F v := by
  let E : Vec d := fun j => F j - (1 / 2 : ℝ) * ∑ k, A k j * v k
  have hyoung (j : Fin d) : M * u * |v j| ≤ (c / 4) * (v j * v j) + (M ^ 2 / c) * u ^ 2 := by
    have hcancel : (M ^ 2 / c) * c = M ^ 2 := div_mul_cancel₀ _ hc.ne'
    have habs : |v j| ^ 2 = (v j) ^ 2 := sq_abs _
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : c * ((c / 4) * (v j * v j) + (M ^ 2 / c) * u ^ 2) =
        (c ^ 2 / 4) * (v j * v j) + M ^ 2 * u ^ 2 := by
      rw [mul_add, ← mul_assoc c (M ^ 2 / c), mul_comm c (M ^ 2 / c), hcancel]
      ring
    rw [he]
    nlinarith [sq_nonneg ((c / 2) * |v j| - M * u)]
  have hterm (j : Fin d) : -((c / 4) * (v j * v j) + (M ^ 2 / c) * u ^ 2) ≤ E j * v j := by
    have hprod : -(M * u * |v j|) ≤ E j * v j := by
      have ha := neg_abs_le (E j * v j)
      rw [abs_mul] at ha
      have hb := mul_le_mul_of_nonneg_right (hF j) (abs_nonneg (v j))
      change |E j| * |v j| ≤ M * u * |v j| at hb
      linarith
    linarith [hyoung j]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  have hleft : (∑ j : Fin d, -((c / 4) * (v j * v j) + (M ^ 2 / c) * u ^ 2)) =
      -((c / 4) * euclideanSq v + (d : ℝ) * (M ^ 2 / c) * u ^ 2) := by
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, euclideanSq, dot]
    ring
  rw [hleft] at hsum
  have hprincipal : dot F v = (1 / 2 : ℝ) * dot v (A.mulVec v) + ∑ j, E j * v j := by
    have hsplit : dot F v =
        (1 / 2 : ℝ) * (∑ j, ∑ k, A k j * v k * v j) + ∑ j, E j * v j := by
      dsimp only [dot, E]
      simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.sum_mul]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    rw [hsplit]
    congr 2
    rw [Finset.sum_comm]
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprincipal]
  linarith

/-- The bounded entropy test converts a coercive divergence identity into a
nonlinear energy estimate. All integrability assumptions concern the smoothed
functions; the original occupation measure need not have a density. -/
theorem c16_weak_divergence_nonlinear_energy {d : ℕ}
    {F : Vec d → Vec d} {g u : Vec d → ℝ}
    (hw : HasWeakDivergence Set.univ F g)
    (hF : ∀ j, Integrable (fun y => F y j)) (hg : Integrable g)
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y) (hui : Integrable u)
    (hDu : Integrable (fderiv ℝ u)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, ‖fderiv ℝ u y‖ ≤ B) {a b α : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hα : 0 < α)
    (hco : ∀ y, a * euclideanSq (gradient u y) - b * u y ^ 2 ≤
      dot (F y) (gradient u y)) :
    (∫ y, euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)) ≤
      ((∫ y, |g y|) + α * b * ∫ y, u y) / (α * a) := by
  let φ : Vec d → ℝ := fun y => 1 - (1 + u y) ^ (-α)
  let w : Vec d → ℝ := fun y => (1 + u y) ^ (1 + α)
  let e : Vec d → ℝ := fun y => euclideanSq (gradient u y) / w y
  obtain ⟨hφ, hφv, hφD⟩ := c16_nonlinear_entropy_test hu hu0 hα
  have hwpos (y : Vec d) : 0 < w y :=
    Real.rpow_pos_of_pos (by linarith [hu0 y]) _
  have hw1 (y : Vec d) : 1 ≤ w y :=
    Real.one_le_rpow (by linarith [hu0 y]) (by linarith)
  have hφnorm (y : Vec d) : ‖φ y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hφv y).1]
    exact (hφv y).2
  have hφbound (y : Vec d) : ‖φ y‖ ≤ 1 + α * B ∧
      ‖fderiv ℝ φ y‖ ≤ 1 + α * B := by
    have hαB : 0 ≤ α * B := mul_nonneg hα.le hB0
    constructor
    · exact (hφnorm y).trans (by linarith)
    · rw [hφD y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hα.le (hwpos y).le)]
      exact (mul_le_mul (div_le_self hα.le (hw1 y)) (hB y)
        (norm_nonneg _) hα.le).trans (by linarith)
  have htest := c16_weak_divergence_bounded_C1 hw hF hg hφ hφbound
  have hei : Integrable e :=
    c16_nonlinear_energy_integrable hu hu0 hDu hB0 hB hα.le
  have hpair (y : Vec d) : dot (F y) (gradient φ y) =
      (α / w y) * dot (F y) (gradient u y) := by
    change (∑ j, F y j * fderiv ℝ φ y (unitVector j)) =
      (α / w y) * ∑ j, F y j * fderiv ℝ u y (unitVector j)
    rw [hφD y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_apply, smul_eq_mul]
    ring
  have hpairi : Integrable (fun y => dot (F y) (gradient φ y)) := by
    change Integrable (fun y => ∑ j, F y j * fderiv ℝ φ y (unitVector j))
    apply integrable_finsetSum
    intro j _
    apply (hF j).mul_bdd
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun y => ?_
    apply le_trans ?_ (hφbound y).2
    simpa only [unitVector, Pi.norm_single, norm_one, mul_one] using
      (fderiv ℝ φ y).le_opNorm (unitVector j)
  have hpoint (y : Vec d) : (α * a) * e y ≤
      dot (F y) (gradient φ y) + (α * b) * u y := by
    calc
      (α * a) * e y = (α / w y) * (a * euclideanSq (gradient u y)) := by
        dsimp only [e]
        ring
      _ ≤ (α / w y) * (dot (F y) (gradient u y) + b * u y ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith [hco y]) (div_nonneg hα.le (hwpos y).le)
      _ = dot (F y) (gradient φ y) + (α * b) * (u y ^ 2 / w y) := by
        rw [hpair y]
        ring
      _ ≤ dot (F y) (gradient φ y) + (α * b) * u y :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
          (c16_nonlinear_weight_mass_bound (hu0 y) hα.le) (mul_nonneg hα.le hb))
  have hint := integral_mono (hei.const_mul (α * a))
    (hpairi.add (hui.const_mul (α * b))) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, integral_add hpairi (hui.const_mul (α * b)),
    integral_const_mul, htest] at hint
  have hgtest : -(∫ y, g y * φ y) ≤ ∫ y, |g y| := by
    apply le_trans (neg_le_abs _)
    have hn : ‖∫ y, g y * φ y‖ ≤ ∫ y, |g y| :=
      norm_integral_le_of_norm_le hg.abs (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |g y| * |φ y| ≤ |g y| * 1 := mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using hφnorm y) (abs_nonneg (g y))
          _ = |g y| := mul_one _)
    simpa only [Real.norm_eq_abs] using hn
  apply (le_div_iff₀ (mul_pos hα ha)).2
  change (∫ y, e y) * (α * a) ≤ (∫ y, |g y|) + α * b * ∫ y, u y
  linarith

/-- The actual reduced smoothed flux is integrable, and its difference from
the elliptic principal flux is bounded by a scale-independent multiple of the
smoothed mass. The constant is chosen before the finite measure and scale. -/
theorem c16_reduced_smoothed_flux_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (μ : Measure (Vec d)) [IsFiniteMeasure μ]
      (r : ℝ), 0 < r →
      let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
      let u : Vec d → ℝ := fun y => ∫ z, κ (z - y) ∂μ
      let F : Vec d → Vec d := fun y j =>
        (1 / 2 : ℝ) * (∑ k, fderiv ℝ
          (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k)) -
          ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
      (∀ j, Integrable (fun y => F y j)) ∧
      ∀ y j, |F y j - (1 / 2 : ℝ) *
        ∑ k, reducedCoefficient ω y k j * fderiv ℝ u y (unitVector k)| ≤ M * u y := by
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  let L : ℝ≥0 := Real.toNNReal (Real.exp (2 * Λ₀) * (2 * Λ₀ ^ 2 + Λ₀) * Real.sqrt d)
  let Q : ℝ := (L : ℝ) * (2 * (m : ℝ))
  let M : ℝ := (1 / 2 : ℝ) * (d : ℝ) * Q + |Mb|
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨M, by dsimp only [M]; positivity, ?_⟩
  intro μ _ r hr
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let u : Vec d → ℝ := fun y => ∫ z, κ (z - y) ∂μ
  let H (k j : Fin d) (y : Vec d) := fderiv ℝ
    (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k)
  let V (j : Fin d) (y : Vec d) :=
    ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
  let F : Vec d → Vec d := fun y j => (1 / 2 : ℝ) * ∑ k, H k j y - V j y
  obtain ⟨hpos, hc, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  obtain ⟨K, D, hK, _⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hui : Integrable u := (c16_normalized_polynomial_smoothing_mass μ hr m hdm).1
  have hDui := c16_normalized_polynomial_smoothing_fderiv_integrable μ hr m hdm
  have hκi (y : Vec d) : Integrable (fun z => κ (z - y)) μ :=
    (integrable_const (K : ℝ)).mono'
      ((hc.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hK _))
  have hHc (k j : Fin d) : Continuous (H k j) :=
    ((c16_normalized_weighted_smoothing_contDiff_one μ hr m
      (hA.matrix_elem k j).measurable ⟨|Ma|, abs_nonneg Ma⟩
      (fun z => (hAb z k j).trans (le_abs_self Ma))).continuous_fderiv one_ne_zero).clm_apply
        continuous_const
  have hVc (j : Fin d) : Continuous (V j) :=
    (c16_normalized_weighted_smoothing_contDiff_one μ hr m
      ((measurable_pi_apply j).comp hb) ⟨|Mb|, abs_nonneg Mb⟩
      (fun z => (hbb z j).trans (le_abs_self Mb))).continuous
  have hE (k j : Fin d) (y : Vec d) :
      |H k j y - reducedCoefficient ω y k j * fderiv ℝ u y (unitVector k)| ≤ Q * u y := by
    have he := c16_normalized_smoothing_derivative_commutator μ
      (reducedCoefficient_lipschitz hΛ hω k j) ⟨|Ma|, abs_nonneg Ma⟩
      (fun z => (hAb z k j).trans (le_abs_self Ma)) hr m hdm y k
    change H k j y = _ ∧ _ at he
    dsimp only [u, κ]
    rw [he.1]
    simpa only [add_sub_cancel_left] using he.2
  have hVb (j : Fin d) (y : Vec d) : |V j y| ≤ |Mb| * u y :=
    (c16_bounded_smoothing_flux μ ((measurable_pi_apply j).comp hb)
      ⟨|Mb|, abs_nonneg Mb⟩ (fun z => (hbb z j).trans (le_abs_self Mb))
      hc.continuous.measurable (fun z => (hpos z).le) y (hκi y)).2
  have hHi (k j : Fin d) : Integrable (H k j) := by
    apply ((hDui.norm.const_mul |Ma|).add (hui.const_mul Q)).mono' (hHc k j).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun y => ?_
    have hv : |fderiv ℝ u y (unitVector k)| ≤ ‖fderiv ℝ u y‖ := by
      simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
        (fderiv ℝ u y).le_opNorm (unitVector k)
    have hp : |reducedCoefficient ω y k j * fderiv ℝ u y (unitVector k)| ≤
        |Ma| * ‖fderiv ℝ u y‖ := by
      rw [abs_mul]
      exact mul_le_mul ((hAb y k j).trans (le_abs_self Ma)) hv (abs_nonneg _) (abs_nonneg _)
    have ha := abs_add_le (H k j y - reducedCoefficient ω y k j *
      fderiv ℝ u y (unitVector k)) (reducedCoefficient ω y k j * fderiv ℝ u y (unitVector k))
    rw [sub_add_cancel] at ha
    rw [Real.norm_eq_abs]
    change |H k j y| ≤ |Ma| * ‖fderiv ℝ u y‖ + Q * u y
    exact ha.trans (by linarith [hE k j y])
  have hVi (j : Fin d) : Integrable (V j) :=
    (hui.const_mul |Mb|).mono' (hVc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hVb j y))
  change (∀ j, Integrable (fun y => F y j)) ∧ ∀ y j,
    |F y j - (1 / 2 : ℝ) * ∑ k, reducedCoefficient ω y k j *
      fderiv ℝ u y (unitVector k)| ≤ M * u y
  refine ⟨fun j => ((integrable_finsetSum _ (fun k _ => hHi k j)).const_mul _).sub (hVi j), ?_⟩
  intro y j
  have heq : F y j - (1 / 2 : ℝ) * ∑ k, reducedCoefficient ω y k j *
      fderiv ℝ u y (unitVector k) = (1 / 2 : ℝ) *
      ∑ k, (H k j y - reducedCoefficient ω y k j * fderiv ℝ u y (unitVector k)) - V j y := by
    dsimp only [F]
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |(1 / 2 : ℝ) * ∑ k, (H k j y - reducedCoefficient ω y k j *
        fderiv ℝ u y (unitVector k))| + |V j y| := abs_sub _ _
    _ ≤ (1 / 2 : ℝ) * (∑ k : Fin d, Q * u y) + |Mb| * u y := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hE k j y))
          (by norm_num)) (hVb j y)
    _ = M * u y := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; dsimp only [M]; ring

/-- The smoothed occupation flux has the endpoint discrepancy as its weak
 divergence for the same supplied martingale-problem law. -/
theorem c16_textbook_occupation_hasWeakDivergence {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    let F : Vec d → Vec d := fun y j =>
      (1 / 2 : ℝ) * (∑ k, fderiv ℝ
        (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k)) -
        ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
    let ρ : Vec d → ℝ := fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
    HasWeakDivergence Set.univ F ρ := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let S (k j : Fin d) (y : Vec d) := ∫ z, reducedCoefficient ω z k j * κ (z - y) ∂μ
  let V (j : Fin d) (y : Vec d) :=
    ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
  let H (k j : Fin d) (y : Vec d) := fderiv ℝ (S k j) y (unitVector k)
  let F : Vec d → Vec d := fun y j => (1 / 2 : ℝ) * (∑ k, H k j y) - V j y
  let ρ (y : Vec d) := (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hS (k j : Fin d) : ContDiff ℝ 1 (S k j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m (hA.matrix_elem k j).measurable
      ⟨|Ma|, abs_nonneg Ma⟩ (fun z => (hAb z k j).trans (le_abs_self Ma))
  have hV (j : Fin d) : ContDiff ℝ 1 (V j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m
      ((measurable_pi_apply j).comp hb) ⟨|Mb|, abs_nonneg Mb⟩
      (fun z => (hbb z j).trans (le_abs_self Mb))
  have hH (k j : Fin d) : Continuous (H k j) :=
    ((hS k j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF (j : Fin d) : Continuous (fun y => F y j) :=
    (continuous_const.mul (continuous_finsetSum _ fun k _ => hH k j)).sub (hV j).continuous
  obtain ⟨_, hκ, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hρ : Continuous ρ := by
    apply Continuous.sub ?_ (hκ.continuous.comp (continuous_const.sub continuous_id))
    refine continuous_of_dominated (bound := fun _ : Path d => (K : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · intro y
      exact ((hκ.continuous.measurable.comp
        (((continuous_eval.comp (continuous_id.prodMk continuous_const)).measurable).sub
          measurable_const)).aestronglyMeasurable)
    · intro y
      exact Filter.Eventually.of_forall fun γ => (Real.norm_eq_abs _).trans_le (hK _)
    · exact Filter.Eventually.of_forall fun γ =>
        hκ.continuous.comp (continuous_const.sub continuous_id)
  have hpair {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ y, dot (F y) (gradient q y)) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j) := by
    have hI (k j : Fin d) : Integrable (fun y => H k j y * fderiv ℝ q y (unitVector j)) :=
      ((hH k j).mul ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hIV (j : Fin d) : Integrable (fun y => V j y * fderiv ℝ q y (unitVector j)) :=
      ((hV j).continuous.mul
        ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
          (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hII (k : Fin d) := integrable_finsetSum Finset.univ (fun j _ => hI k j)
    have hIII := integrable_finsetSum Finset.univ (fun k _ => hII k)
    have hIVs := integrable_finsetSum Finset.univ (fun j _ => hIV j)
    have hp (y : Vec d) : dot (F y) (gradient q y) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, V j y * fderiv ℝ q y (unitVector j) := by
      dsimp only [F, dot, gradient, coordinateDerivative]
      simp_rw [sub_mul, mul_assoc, Finset.sum_mul, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hp), integral_sub (hIII.const_mul _) hIVs,
      integral_const_mul, integral_finsetSum _ (fun j _ => hIV j),
      integral_finsetSum _ (fun k _ => hII k)]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finsetSum _ (fun j _ => hI k j)
  have hw : HasWeakDivergence Set.univ F ρ := by
    refine ⟨fun j => (hF j).locallyIntegrable.locallyIntegrableOn _,
      hρ.locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro q hq
    simp only [Measure.restrict_univ]
    rw [hpair (hq.1.of_le (by simp)) hq.2.1]
    have he := c16_textbook_occupation_smoothed_divergence hΛ hω i lam hP
      hr m hdm hq.1 hq.2.1 T
    dsimp only at he
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) = -(∫ y, ρ y * q y)
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) =
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) - (∫ y, ρ y * q y) at he
    linarith only [he]
  exact hw

/-- A scale-independent nonlinear energy bound for the actual finite-horizon
occupation smoothing. The constant precedes the starting point, law and scale. -/
theorem c16_textbook_occupation_uniform_nonlinear_energy {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec d) (P : Measure (Path d)),
      SolvesMartingaleProblem
        (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam)) x P →
      ∀ (r : ℝ), 0 < r → ∀ (T : ℝ≥0),
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r m (z - y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + α)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ C * (1 + (T : ℝ)) := by
  obtain ⟨c, hc, hell⟩ := reducedCoefficient_elliptic hΛ hω
  obtain ⟨M, hM, hflux⟩ := c16_reduced_smoothed_flux_bound hΛ hω i lam m hdm
  let a : ℝ := c / 4
  let b : ℝ := (d : ℝ) * (M ^ 2 / c)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  let D : ℝ := (2 + α * b) / (α * a)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D + (1 - α), by linarith, ?_⟩
  intro x P hP r hr T
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let u : Vec d → ℝ := fun y => ∫ z, κ (z - y) ∂μ
  let F : Vec d → Vec d := fun y j =>
    (1 / 2 : ℝ) * (∑ k, fderiv ℝ
      (fun v => ∫ z, reducedCoefficient ω z k j * κ (z - v) ∂μ) y (unitVector k)) -
      ∫ z, forcedDrift (reducedCoefficient ω) i lam z j * κ (z - y) ∂μ
  let ρ : Vec d → ℝ := fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
  obtain ⟨hu, hui, hDu, hmass⟩ :=
    c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  obtain ⟨B, hB0, hB⟩ := c16_normalized_polynomial_smoothing_fderiv_bounded μ hr m
  obtain ⟨hFi, hFe⟩ := hflux μ r hr
  obtain ⟨hρi, hρbound⟩ := c16_probability_smoothed_endpoint_l1 P T x hr m hdm
  have hw : HasWeakDivergence Set.univ F ρ :=
    c16_textbook_occupation_hasWeakDivergence hΛ hω i lam hP hr m hdm T
  have hco (y : Vec d) : a * euclideanSq (gradient u y) - b * u y ^ 2 ≤
      dot (F y) (gradient u y) :=
    c16_elliptic_flux_coercivity (reducedCoefficient ω y) (gradient u y) (F y)
      hc (hell y (gradient u y)) (hFe y)
  have he := c16_weak_divergence_nonlinear_energy hw hFi hρi hu hu0 hui hDu
    hB0 hB ha hb hα hco
  have hei := c16_nonlinear_energy_integrable hu hu0 hDu hB0 hB hα.le
  refine ⟨hei, ?_⟩
  change (∫ y, euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)) ≤
    (D + (1 - α)) * (1 + (T : ℝ))
  calc
    _ ≤ ((∫ y, |ρ y|) + α * b * ∫ y, u y) / (α * a) := he
    _ ≤ (2 + α * b * (T : ℝ)) / (α * a) := by
      rw [hmass]
      exact div_le_div_of_nonneg_right (add_le_add hρbound (le_refl _)) (mul_pos hα ha).le
    _ ≤ ((2 + α * b) * (1 + (T : ℝ))) / (α * a) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hα ha).le
      nlinarith [T.coe_nonneg]
    _ = D * (1 + (T : ℝ)) := by dsimp only [D]; ring
    _ ≤ (D + (1 - α)) * (1 + (T : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The sublinear entropy used for the local Sobolev estimate is smooth,
nonnegative, and bounded by the original density. -/
theorem c16_sublinear_entropy_properties {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    ContDiff ℝ 1 (fun y => (1 + u y) ^ (1 - α) - 1) ∧
    (∀ y, 0 ≤ (1 + u y) ^ (1 - α) - 1 ∧
      (1 + u y) ^ (1 - α) - 1 ≤ u y) ∧
    ∀ y, fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y =
      ((1 - α) * (1 + u y) ^ (-α)) • fderiv ℝ u y := by
  have hpos (y : Vec d) : 0 < 1 + u y := by linarith [hu0 y]
  refine ⟨((contDiff_const.add hu).rpow_const_of_ne
    (fun y => (hpos y).ne')).sub contDiff_const, ?_, ?_⟩
  · intro y
    have hlo : 1 ≤ (1 + u y) ^ (1 - α) :=
      Real.one_le_rpow (by linarith [hu0 y]) (by linarith)
    have hhi : (1 + u y) ^ (1 - α) ≤ 1 + u y :=
      Real.rpow_le_self_of_one_le (by linarith [hu0 y]) (by linarith)
    constructor <;> linarith
  · intro y
    have hd := (((hu.differentiable one_ne_zero y).hasFDerivAt.const_add 1).rpow_const
      (p := 1 - α) (Or.inl (hpos y).ne')).sub_const 1
    have he := hd.fderiv
    convert he using 1 <;> congr 2 <;> ring

/-- The sublinear entropy inherits the density's integrability and mass bound. -/
theorem c16_sublinear_entropy_integrable {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y) (hui : Integrable u volume)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Integrable (fun y => (1 + u y) ^ (1 - α) - 1) volume ∧
      (∫ y, ((1 + u y) ^ (1 - α) - 1)) ≤ ∫ y, u y := by
  obtain ⟨hc, hb, _⟩ := c16_sublinear_entropy_properties hu hu0 hα hα1
  have hi : Integrable (fun y => (1 + u y) ^ (1 - α) - 1) volume := by
    apply hui.mono' hc.continuous.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hb y).1]
    exact (hb y).2
  refine ⟨hi, ?_⟩
  exact integral_mono hi hui (fun y => (hb y).2)

/-- A compact set admits a compact smooth cutoff taking the value one on it. -/
theorem c16_compact_cutoff {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ ∀ y ∈ K, χ y = 1 := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨χ, hχ, _, hχb, hχ1, hχ0⟩ := exists_cutoff d
  refine ⟨cutoffFn χ R (fun _ => 1), contDiff_cutoffFn hχ contDiff_const R,
    hasCompactSupport_cutoffFn _ hR hχ0, ?_, ?_⟩
  · intro y
    simpa only [cutoffFn, mul_one] using hχb (R⁻¹ • y)
  · intro y hy
    exact cutoffFn_eq _ hR hχ1 (hKR y hy)

/-- The entropy gradient weight is controlled by the energy weight and a
local mass term, using Young's inequality. -/
theorem c16_entropy_gradient_young (g t α : ℝ) (ht : 0 < t) :
    2 * |g| * t ^ (-α) ≤ g ^ 2 / t ^ (1 + α) + t ^ (1 - α) := by
  have hsq : 2 * |g| * t ≤ g ^ 2 + t ^ 2 := by
    have ha := sq_nonneg (|g| - t)
    have habs : |g| ^ 2 = g ^ 2 := sq_abs g
    nlinarith [habs]
  have hy : 2 * |g| ≤ g ^ 2 / t + t := by
    have h := (le_div_iff₀ ht).2 hsq
    calc
      2 * |g| ≤ (g ^ 2 + t ^ 2) / t := h
      _ = g ^ 2 / t + t := by field_simp
  have hw := mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg ht.le (-α))
  rw [show 1 - α = 1 + -α by ring, Real.rpow_add ht, Real.rpow_one,
    Real.rpow_add ht, Real.rpow_one]
  simp only [Real.rpow_neg ht.le]
  have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht α).ne'
  rw [Real.rpow_neg ht.le] at hw
  convert hw using 1 <;> field_simp <;> ring

/-- Each entropy derivative is bounded by the nonlinear energy density plus a
local mass term, with the explicit Euclidean quadratic form. -/
theorem c16_sublinear_entropy_derivative_bound {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (y : Vec d) (j : Fin d) :
    2 * |fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y (unitVector j)| ≤
      (1 - α) * (euclideanSq (gradient u y) / (1 + u y) ^ (1 + α) + (1 + u y)) := by
  have hp : 0 < 1 + u y := by linarith [hu0 y]
  have hw : 0 ≤ (1 + u y) ^ (-α) := Real.rpow_nonneg hp.le _
  have hb : (1 + u y) ^ (1 - α) ≤ 1 + u y :=
    Real.rpow_le_self_of_one_le (by linarith [hu0 y]) (by linarith)
  have hg : (gradient u y j) ^ 2 ≤ euclideanSq (gradient u y) := by
    simpa only [euclideanSq, dot, pow_two] using
      Finset.single_le_sum (fun k _ => mul_self_nonneg (gradient u y k)) (Finset.mem_univ j)
  have hy := c16_entropy_gradient_young (gradient u y j) (1 + u y) α hp
  have hd := (c16_sublinear_entropy_properties hu hu0 hα hα1).2.2 y
  rw [hd]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (by linarith : 0 ≤ 1 - α), abs_of_nonneg hw]
  change 2 * ((1 - α) * (1 + u y) ^ (-α) * |gradient u y j|) ≤ _
  have he : (gradient u y j) ^ 2 / (1 + u y) ^ (1 + α) ≤
      euclideanSq (gradient u y) / (1 + u y) ^ (1 + α) :=
    div_le_div_of_nonneg_right hg (Real.rpow_nonneg hp.le _)
  have hm := mul_le_mul_of_nonneg_left (hy.trans (add_le_add he hb))
    (by linarith : 0 ≤ 1 - α)
  nlinarith only [hm]

/-- Integrating the entropy derivative estimate over a compact set only incurs
the local mass term and the nonlinear energy on that set. -/
theorem c16_sublinear_entropy_derivative_integral_bound {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    {K : Set (Vec d)} (hK : IsCompact K) (j : Fin d) :
    2 * (∫ y in K, |fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y
      (unitVector j)|) ≤
      (1 - α) * ((∫ y in K, euclideanSq (gradient u y) /
        (1 + u y) ^ (1 + α)) + ∫ y in K, (1 + u y)) := by
  let v : Vec d → ℝ := fun z => (1 + u z) ^ (1 - α) - 1
  let e : Vec d → ℝ := fun y => euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)
  have hv : ContDiff ℝ 1 v := (c16_sublinear_entropy_properties hu hu0 hα hα1).1
  have hd : Continuous (fun y => |fderiv ℝ v y (unitVector j)|) :=
    ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).abs
  have he : Continuous e := by
    apply Continuous.div ?_
      ((continuous_const.add hu.continuous).rpow_const (fun y => Or.inl (by
        change 1 + u y ≠ 0
        linarith [hu0 y])))
      (fun y => (Real.rpow_pos_of_pos (by
        change 0 < 1 + u y
        linarith [hu0 y]) _).ne')
    change Continuous (fun y => ∑ k : Fin d,
      fderiv ℝ u y (unitVector k) * fderiv ℝ u y (unitVector k))
    exact continuous_finsetSum _ (fun k _ =>
      ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const))
  have hdi := hd.continuousOn.integrableOn_compact (μ := volume) hK
  have hei := he.continuousOn.integrableOn_compact (μ := volume) hK
  have hui : Integrable (fun y => 1 + u y) (volume.restrict K) :=
    (continuous_const.add hu.continuous).continuousOn.integrableOn_compact hK
  have h := integral_mono (hdi.const_mul 2) ((hei.add hui).const_mul (1 - α))
    (fun y => c16_sublinear_entropy_derivative_bound hu hu0 hα hα1 y j)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_const_mul, integral_add hei hui] at h
  exact h

/-- The compact entropy derivative bound depends only on the total mass and
total nonlinear energy, in addition to the volume of the compact set. -/
theorem c16_sublinear_entropy_derivative_integral_global_bound {d : ℕ} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y) (hui : Integrable u volume)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hei : Integrable (fun y => euclideanSq (gradient u y) /
      (1 + u y) ^ (1 + α)) volume)
    {K : Set (Vec d)} (hK : IsCompact K) (j : Fin d) :
    2 * (∫ y in K, |fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y
      (unitVector j)|) ≤
      (1 - α) * ((∫ y, euclideanSq (gradient u y) /
        (1 + u y) ^ (1 + α)) + ((volume K).toReal + ∫ y, u y)) := by
  have he0 : ∀ y, 0 ≤ euclideanSq (gradient u y) / (1 + u y) ^ (1 + α) := by
    intro y
    apply div_nonneg
    · change 0 ≤ ∑ j : Fin d, gradient u y j * gradient u y j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    · exact Real.rpow_nonneg (by linarith [hu0 y]) _
  have he := setIntegral_le_integral hei (Filter.Eventually.of_forall he0) (s := K)
  have hm := setIntegral_le_integral hui (Filter.Eventually.of_forall hu0) (s := K)
  have hc : Integrable (fun _ : Vec d => (1 : ℝ)) (volume.restrict K) :=
    continuousOn_const.integrableOn_compact hK
  have hmass : (∫ y in K, (1 + u y)) = (volume K).toReal + ∫ y in K, u y := by
    rw [integral_add hc hui.restrict]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply_univ]
  have h := c16_sublinear_entropy_derivative_integral_bound hu hu0 hα hα1 hK j
  rw [hmass] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add he (add_le_add (le_refl _) hm))
    (by linarith))

/-- A compactly supported C¹ cutoff and all its coordinate derivatives have
one common finite bound. -/
theorem c16_compact_c1_cutoff_uniform_bound {d : ℕ} {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |χ y| ≤ B ∧
      ∀ j : Fin d, |fderiv ℝ χ y (unitVector j)| ≤ B := by
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨D, hD⟩ := (hχ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hχc.fderiv ℝ)
  let B : ℝ := |A| + |D|
  refine ⟨B, by dsimp only [B]; positivity, fun y => ⟨?_, fun j => ?_⟩⟩
  · calc
      |χ y| = ‖χ y‖ := (Real.norm_eq_abs _).symm
      _ ≤ A := hA y
      _ ≤ B := by dsimp only [B]; linarith [le_abs_self A, abs_nonneg D]
  · have hj : |fderiv ℝ χ y (unitVector j)| ≤ ‖fderiv ℝ χ y‖ := by
      simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
        (fderiv ℝ χ y).le_opNorm (unitVector j)
    exact hj.trans ((hD y).trans (by dsimp only [B]; linarith [le_abs_self D, abs_nonneg A]))

/-- A cutoff of the sublinear entropy is a compactly supported C¹ function,
and its coordinate derivatives are integrable and satisfy the product rule. -/
theorem c16_cutoff_sublinear_entropy_c1 {d : ℕ} {u χ : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    let v : Vec d → ℝ := fun y => (1 + u y) ^ (1 - α) - 1
    let w : Vec d → ℝ := fun y => χ y * v y
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ Integrable w volume ∧
      (∀ j : Fin d, Integrable (fun y => fderiv ℝ w y (unitVector j)) volume) ∧
      ∀ y j, fderiv ℝ w y (unitVector j) =
        χ y * fderiv ℝ v y (unitVector j) + v y * fderiv ℝ χ y (unitVector j) := by
  dsimp only
  let v : Vec d → ℝ := fun y => (1 + u y) ^ (1 - α) - 1
  let w : Vec d → ℝ := fun y => χ y * v y
  have hv : ContDiff ℝ 1 v := (c16_sublinear_entropy_properties hu hu0 hα hα1).1
  have hw : ContDiff ℝ 1 w := hχ.mul hv
  have hwc : HasCompactSupport w := hχc.mul_right
  refine ⟨hw, hwc, hw.continuous.integrable_of_hasCompactSupport hwc, ?_, ?_⟩
  · intro j
    exact ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hwc.fderiv_apply (𝕜 := ℝ) (unitVector j))
  · intro y j
    rw [fderiv_fun_mul (hχ.differentiable one_ne_zero y) (hv.differentiable one_ne_zero y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl

/-- The cutoff entropy derivative is controlled pointwise by the original
density and the entropy derivative. -/
theorem c16_cutoff_sublinear_entropy_derivative_bound {d : ℕ} {u χ : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    {B : ℝ}
    (hχB : ∀ y, |χ y| ≤ B ∧ ∀ j : Fin d, |fderiv ℝ χ y (unitVector j)| ≤ B)
    (y : Vec d) (j : Fin d) :
    |fderiv ℝ (fun z => χ z * ((1 + u z) ^ (1 - α) - 1)) y (unitVector j)| ≤
      B * (|fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y (unitVector j)| + u y) := by
  have hv := (c16_sublinear_entropy_properties hu hu0 hα hα1).2.1 y
  have hp := (c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα hα1).2.2.2.2 y j
  rw [hp]
  calc
    _ ≤ |χ y| * |fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y (unitVector j)| +
        |(1 + u y) ^ (1 - α) - 1| * |fderiv ℝ χ y (unitVector j)| := by
      simpa only [abs_mul] using abs_add_le
        (χ y * fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y (unitVector j))
        (((1 + u y) ^ (1 - α) - 1) * fderiv ℝ χ y (unitVector j))
    _ ≤ B * |fderiv ℝ (fun z => (1 + u z) ^ (1 - α) - 1) y (unitVector j)| +
        u y * B := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (hχB y).1 (abs_nonneg _)
      · rw [abs_of_nonneg hv.1]
        exact mul_le_mul hv.2 ((hχB y).2 j) (abs_nonneg _) (hu0 y)
    _ = _ := by ring

/-- The cutoff derivative has a global L¹ bound in terms of the original
mass and nonlinear energy, with the constant term restricted to its support. -/
theorem c16_cutoff_sublinear_entropy_derivative_integral_bound {d : ℕ}
    {u χ : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    (hui : Integrable u volume) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hei : Integrable (fun y => euclideanSq (gradient u y) /
      (1 + u y) ^ (1 + α)) volume)
    {B : ℝ} (hB : 0 ≤ B)
    (hχB : ∀ y, |χ y| ≤ B ∧ ∀ j : Fin d, |fderiv ℝ χ y (unitVector j)| ≤ B)
    (j : Fin d) :
    2 * (∫ y, |fderiv ℝ (fun z => χ z * ((1 + u z) ^ (1 - α) - 1)) y
      (unitVector j)|) ≤
      B * ((1 - α) * ((∫ y, euclideanSq (gradient u y) /
        (1 + u y) ^ (1 + α)) + ((volume (tsupport χ)).toReal + ∫ y, u y)) +
        2 * ∫ y, u y) := by
  let v : Vec d → ℝ := fun z => (1 + u z) ^ (1 - α) - 1
  let w : Vec d → ℝ := fun z => χ z * v z
  let K := tsupport χ
  have hK : IsCompact K := hχc
  have hv : ContDiff ℝ 1 v := (c16_sublinear_entropy_properties hu hu0 hα hα1).1
  have hw : ContDiff ℝ 1 w := hχ.mul hv
  have hwc : HasCompactSupport w := hχc.mul_right
  have hwd : Integrable (fun y => |fderiv ℝ w y (unitVector j)|) volume :=
    (((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hwc.fderiv_apply (𝕜 := ℝ) (unitVector j))).abs
  have hvd : Integrable (fun y => |fderiv ℝ v y (unitVector j)|) (volume.restrict K) :=
    (((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs.continuousOn.integrableOn_compact hK)
  have hzero (y : Vec d) (hy : y ∉ K) : |fderiv ℝ w y (unitVector j)| = 0 := by
    have hyw : y ∉ tsupport w := fun h => hy (tsupport_mul_subset_left h)
    simp only [fderiv_of_notMem_tsupport ℝ hyw, ContinuousLinearMap.zero_apply, abs_zero]
  have hrestrict : (∫ y, |fderiv ℝ w y (unitVector j)|) =
      ∫ y in K, |fderiv ℝ w y (unitVector j)| :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hpoint := integral_mono hwd.restrict ((hvd.add hui.restrict).const_mul B)
    (fun y => c16_cutoff_sublinear_entropy_derivative_bound hu hu0 hχ hχc hα hα1 hχB y j)
  simp only [Pi.add_apply] at hpoint
  rw [integral_const_mul, integral_add hvd hui.restrict] at hpoint
  have hmass := setIntegral_le_integral hui (Filter.Eventually.of_forall hu0) (s := K)
  have henergy := c16_sublinear_entropy_derivative_integral_global_bound
    hu hu0 hui hα hα1 hei hK j
  rw [hrestrict]
  have hmul := mul_le_mul_of_nonneg_left hmass hB
  have hmul' := mul_le_mul_of_nonneg_left henergy hB
  nlinarith only [hpoint, hmul, hmul']

/-- The L¹ norm of the cutoff entropy is bounded by the density's mass. -/
theorem c16_cutoff_sublinear_entropy_integral_bound {d : ℕ}
    {u χ : Vec d → ℝ} (hu : ContDiff ℝ 1 u) (hu0 : ∀ y, 0 ≤ u y)
    (hui : Integrable u volume) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    {B : ℝ} (hB : 0 ≤ B) (hχB : ∀ y, |χ y| ≤ B) :
    (∫ y, |χ y * ((1 + u y) ^ (1 - α) - 1)|) ≤ B * ∫ y, u y := by
  have hi := (c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα hα1).2.2.1.abs
  have h := integral_mono hi (hui.const_mul B) (fun y => by
    have hv := (c16_sublinear_entropy_properties hu hu0 hα hα1).2.1 y
    rw [abs_mul, abs_of_nonneg hv.1]
    exact mul_le_mul (hχB y) hv.2 hv.1 hB)
  rw [integral_const_mul] at h
  exact h

/-- Uniform W¹,¹ control of a compact cutoff of the actual smoothed
finite-horizon occupation entropy. -/
theorem c16_textbook_occupation_cutoff_entropy_W11_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      let u := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let v := fun y => χ y * ((1 + u y) ^ (1 - (2 * (d : ℝ))⁻¹) - 1)
      Integrable v (volume : Measure (Vec d)) ∧
      (∀ j : Fin d, Integrable (fun y => fderiv ℝ v y (unitVector j)) volume) ∧
      (∫ y, |v y|) + (∑ j : Fin d, ∫ y, |fderiv ℝ v y (unitVector j)|) ≤ C := by
  let α : ℝ := (2 * (d : ℝ))⁻¹
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < α := by dsimp only [α]; positivity
  have hα1 : α < 1 := by
    dsimp only [α]
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  obtain ⟨E, hE, henergy⟩ :=
    c16_textbook_occupation_uniform_nonlinear_energy hΛ hω i lam m hdm α hα hα1
  obtain ⟨B, hB, hχB⟩ := c16_compact_c1_cutoff_uniform_bound hχ hχc
  let D : ℝ := B * ((1 - α) * (E * (1 + (T : ℝ)) +
    ((volume (tsupport χ)).toReal + (T : ℝ))) + 2 * (T : ℝ))
  let C : ℝ := 1 + |B * (T : ℝ)| + (d : ℝ) * |D|
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro r hr
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ (1 - α) - 1)
  obtain ⟨hu, hui, _, hmass⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have he := henergy x P hP r hr T
  have hprod := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα.le hα1
  refine ⟨hprod.2.2.1, hprod.2.2.2.1, ?_⟩
  have hv := c16_cutoff_sublinear_entropy_integral_bound hu hu0 hui hχ hχc
    hα.le hα1 hB (fun y => (hχB y).1)
  rw [hmass] at hv
  have hv' : (∫ y, |v y|) ≤ |B * (T : ℝ)| := hv.trans (le_abs_self _)
  have hdv (j : Fin d) : (∫ y, |fderiv ℝ v y (unitVector j)|) ≤ |D| := by
    have h := c16_cutoff_sublinear_entropy_derivative_integral_bound
      hu hu0 hui hχ hχc hα.le hα1 he.1 hB hχB j
    rw [hmass] at h
    have he'' : B * ((1 - α) *
        ((∫ y, euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)) +
          ((volume (tsupport χ)).toReal + (T : ℝ))) + 2 * (T : ℝ)) ≤ D := by
      dsimp only [D]
      apply mul_le_mul_of_nonneg_left _ hB
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add he.2 le_rfl)
        (by linarith : 0 ≤ 1 - α)) le_rfl
    have hz : 0 ≤ ∫ y, |fderiv ℝ v y (unitVector j)| := integral_nonneg fun _ => abs_nonneg _
    nlinarith [le_abs_self D]
  have hsum : (∑ j : Fin d, ∫ y, |fderiv ℝ v y (unitVector j)|) ≤ (d : ℝ) * |D| := by
    calc
      _ ≤ ∑ _j : Fin d, |D| := Finset.sum_le_sum fun j _ => hdv j
      _ = (d : ℝ) * |D| := by simp
  dsimp only [C]
  linarith

/-- Sharp Sobolev control of a compactly supported C¹ function by its
coordinate derivative integrals. -/
theorem c16_compact_c1_sobolev_bound {d : ℕ} (hd : 2 ≤ d)
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    eLpNorm f ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^
        ((1 : ℝ) / d))⁻¹) * ENNReal.ofReal
          (∑ j : Fin d, ∫ y, |fderiv ℝ f y (PDE.basisVec j)|) := by
  let w := PDE.W1pFunction.ofContDiff isOpen_univ hf hfc (1 : ℝ≥0∞)
  let G : Vec d → ℝ := fun y => PDE.vecEuclideanNorm (w.grad y)
  let S : Vec d → ℝ := fun y => ∑ j : Fin d, |fderiv ℝ f y (PDE.basisVec j)|
  have hdi (j : Fin d) : Integrable (fun y => |fderiv ℝ f y (PDE.basisVec j)|) volume :=
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) (PDE.basisVec j))).abs
  have hSi : Integrable S volume := integrable_finset_sum _ fun j _ => hdi j
  have hGc : Continuous G := PDE.continuous_vecEuclideanNorm.comp (continuous_pi fun j =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hGS : ∀ y, ‖G y‖ ≤ S y := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _)]
    exact PDE.vecEuclideanNorm_le_sum_abs _
  have hS : eLpNorm S 1 volume = ENNReal.ofReal (∑ j : Fin d, ∫ y,
      |fderiv ℝ f y (PDE.basisVec j)|) := by
    rw [eLpNorm_one_eq_lintegral_enorm hSi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hSi]
    congr 1
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)])]
    exact integral_finset_sum _ fun j _ => hdi j
  have hsharp := PDE.SobolevSharp.sobolev_sharp_one_of_two_le d hd w
  have hh := (eLpNorm_mono_real hGc.aestronglyMeasurable hGS).trans_eq hS
  refine hsharp.trans ?_
  simpa only [mul_comm] using mul_le_mul_left hh
    (ENNReal.ofReal (((d : ℝ) * (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^
      ((1 : ℝ) / d))⁻¹))

/-- The entropy exponent yields a local integrability exponent above one. -/
theorem c16_occupation_sobolev_exponent_gt_one {d : ℕ} (hd : 2 ≤ d) :
    1 < ((1 - (2 * (d : ℝ))⁻¹) * (d : ℝ)) / ((d : ℝ) - 1) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hx : (d : ℝ) * (2 * (d : ℝ))⁻¹ = (1 : ℝ) / 2 := by
    field_simp
  rw [lt_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]
  nlinarith [hx]

/-- The compact cutoff of the actual occupation entropy has a uniform
sharp-Sobolev norm bound. -/
theorem c16_textbook_occupation_cutoff_entropy_sobolev_bound {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      let u := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let v := fun y => χ y * ((1 + u y) ^ (1 - (2 * (d : ℝ))⁻¹) - 1)
      eLpNorm v ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤ C := by
  obtain ⟨A, hA, hbound⟩ :=
    c16_textbook_occupation_cutoff_entropy_W11_bound hd hΛ hω i lam hP m hdm T χ hχ hχc
  let C₀ : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) *
    (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹)
  refine ⟨C₀ * ENNReal.ofReal A, ENNReal.mul_ne_top (by simp [C₀]) (by simp), ?_⟩
  intro r hr
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let α : ℝ := (2 * (d : ℝ))⁻¹
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ (1 - α) - 1)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α < 1 := by
    dsimp [α]
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  obtain ⟨hu, _, _, _⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have hv := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα hα1
  have hW := hbound r hr
  have hmass : 0 ≤ ∫ y, |v y| := integral_nonneg fun _ => abs_nonneg _
  have hsum : (∑ j : Fin d, ∫ y, |fderiv ℝ v y (PDE.basisVec j)|) ≤ A := by
    have h := hW.2.2
    simp only [PDE.basisVec, unitVector] at h ⊢
    linarith
  refine (c16_compact_c1_sobolev_bound hd hv.1 hv.2.1).trans ?_
  simpa only [mul_comm] using mul_le_mul_left (ENNReal.ofReal_le_ofReal hsum) C₀

/-- A compact set admits a smooth compactly supported cutoff equal to one on it. -/
theorem c16_compact_set_smooth_cutoff {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ χ : Vec d → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧
      ∀ y ∈ K, χ y = 1 := by
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump (0 : Vec d) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨(χ : Vec d → ℝ), (χ.contDiff : ContDiff ℝ (⊤ : ℕ∞) (χ : Vec d → ℝ)).of_le
    (by simp), χ.hasCompactSupport, ?_⟩
  intro y hy
  apply χ.one_of_mem_closedBall
  apply mem_closedBall_zero_iff.mpr
  have := hB y hy
  change ‖y‖ ≤ |B| + 1
  linarith [le_abs_self B]

/-- The density is bounded by the inverse power of its entropy plus one. -/
theorem c16_density_le_entropy_inverse_power {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) :
    a ≤ (1 + ((1 + a) ^ β - 1)) ^ β⁻¹ := by
  have heq : ((1 + a) ^ β) ^ β⁻¹ = 1 + a := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + a), mul_inv_cancel₀ hβ.ne', Real.rpow_one]
  have hrewrite : 1 + ((1 + a) ^ β - 1) = (1 + a) ^ β := by ring
  rw [hrewrite, heq]
  linarith


/-- Transfer a local entropy norm estimate to a density norm estimate. -/
theorem c16_local_density_norm_le {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K)
    {u v : Vec d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ y, 0 ≤ u y) {β : ℝ} (hβ : 0 < β)
    (hpoint : ∀ y ∈ K, v y = (1 + u y) ^ β - 1)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {q : ℝ≥0∞}
    (hpq : q * ENNReal.ofReal β⁻¹ = p) :
    eLpNorm u q (volume.restrict K) ≤
      (eLpNorm (fun _ : Vec d => (1 : ℝ)) p (volume.restrict K) +
        eLpNorm v p volume) ^ β⁻¹ := by
  let μ : Measure (Vec d) := volume.restrict K
  let w : Vec d → ℝ := fun y => 1 + v y
  have hw : AEStronglyMeasurable w μ := (continuous_const.add hv).aestronglyMeasurable
  have hlocal : eLpNorm u q μ ≤ eLpNorm (fun y => ‖w y‖ ^ β⁻¹) q μ := by
    apply eLpNorm_mono_ae_real hu.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hu0 y)]
    have hh := c16_density_le_entropy_inverse_power (hu0 y) hβ
    have hw0 : 0 ≤ w y := by
      dsimp [w]; rw [hpoint y hy];
      have := Real.rpow_nonneg (by linarith [hu0 y] : 0 ≤ 1 + u y) β
      linarith
    change u y ≤ ‖w y‖ ^ β⁻¹
    rw [Real.norm_eq_abs, abs_of_nonneg hw0]
    simpa [w, hpoint y hy] using hh
  rw [eLpNorm_norm_rpow w hw (inv_pos.mpr hβ), hpq] at hlocal
  have hsum : eLpNorm w p μ ≤ eLpNorm (fun _ : Vec d => (1 : ℝ)) p μ + eLpNorm v p volume := by
    calc
      _ ≤ eLpNorm (fun _ : Vec d => (1 : ℝ)) p μ + eLpNorm v p μ := by
        simpa [w, Pi.add_def] using (eLpNorm_add_le (f := fun _ : Vec d => (1 : ℝ)) (g := v) hp)
      _ ≤ _ := add_le_add le_rfl (eLpNorm_mono_measure v Measure.restrict_le_self)
  exact hlocal.trans (ENNReal.rpow_le_rpow hsum (inv_nonneg.mpr hβ.le))


/-- The actual smoothed finite-horizon occupation density is locally uniformly
bounded in an exponent strictly larger than one. -/
theorem c16_textbook_occupation_smoothed_local_Lq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      eLpNorm (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y)
        ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
        (ENNReal.ofReal q) (volume.restrict K) ≤ ENNReal.ofReal C := by
  let β : ℝ := 1 - (2 * (d : ℝ))⁻¹
  let pR : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  let q : ℝ := β * pR
  let p : ℝ≥0∞ := ENNReal.ofReal pR
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα0 : 0 ≤ (2 * (d : ℝ))⁻¹ := by positivity
  have hα1 : (2 * (d : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpR : 1 ≤ pR := by
    dsimp [pR]; rw [le_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]; linarith
  have hq : 1 < q := by
    simpa [q, β, pR, mul_div_assoc] using c16_occupation_sobolev_exponent_gt_one hd
  have hp : 1 ≤ p := by
    simpa [p] using ENNReal.ofReal_le_ofReal hpR
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpt : p ≠ ∞ := by simp [p]
  have hpq : ENNReal.ofReal q * ENNReal.ofReal β⁻¹ = p := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q)]
    congr 1
    dsimp [q]
    field_simp
  obtain ⟨χ, hχ, hχc, hχK⟩ := c16_compact_set_smooth_cutoff hK
  obtain ⟨A, hA, hA_bound⟩ :=
    c16_textbook_occupation_cutoff_entropy_sobolev_bound hd hΛ hω i lam hP m hdm T χ hχ hχc
  let N : ℝ≥0∞ := eLpNorm (fun _ : Vec d => (1 : ℝ)) p (volume.restrict K)
  have hN : N ≠ ∞ := by
    apply ne_of_lt
    apply (eLpNorm_const_lt_top_iff hp0 hpt).2
    right
    simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top : volume K < ∞)
  let D : ℝ≥0∞ := (N + A) ^ β⁻¹
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hβ.le)
    (ENNReal.add_ne_top.mpr ⟨hN, hA⟩)
  refine ⟨q, hq, D.toReal + 1, by positivity, ?_⟩
  intro r hr
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ β - 1)
  obtain ⟨hu, _, _, _⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have hv := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα0 hα1
  have hpoint (y : Vec d) (hy : y ∈ K) : v y = (1 + u y) ^ β - 1 := by
    simp [v, hχK y hy]
  have hp_eq : p = (d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1) := by
    simpa [p, pR] using (PDE.SobolevSharp.exponent_eq hd).symm
  have hbound : eLpNorm v p volume ≤ A := by
    rw [hp_eq]
    exact hA_bound r hr
  have htransfer := c16_local_density_norm_le hK hu.continuous hv.1.continuous hu0 hβ hpoint hp hpq
  have hfinal : eLpNorm u (ENNReal.ofReal q) (volume.restrict K) ≤ D := by
    refine htransfer.trans ?_
    exact ENNReal.rpow_le_rpow (add_le_add le_rfl hbound) (inv_nonneg.mpr hβ.le)
  calc
    _ ≤ D := hfinal
    _ = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
    _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)


end EinsteinFull
