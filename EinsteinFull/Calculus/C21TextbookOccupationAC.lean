import EinsteinFull.Calculus.C16ReducedMPExistence
import Mathlib.MeasureTheory.Integral.PeakFunction

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull
open EinsteinRelation

/-- Euclidean quadratic scaling for the coordinate carrier. -/
theorem c21_euclideanSq_smul {d : ℕ} (r : ℝ) (x : Vec d) :
    euclideanSq (r • x) = r ^ 2 * euclideanSq x := by
  simp only [euclideanSq, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The unnormalized polynomial kernel scales with the Euclidean carrier. -/
theorem c21_polynomial_kernel_smul {d : ℕ} (r : ℝ) (m : ℕ) (x : Vec d) :
    c16PolynomialKernel r m (r • x) =
      ((r ^ 2)⁻¹) ^ m * c16PolynomialKernel 1 m x := by
  simp only [c16PolynomialKernel, c21_euclideanSq_smul, one_pow]
  rw [show r ^ 2 + r ^ 2 * euclideanSq x = r ^ 2 * (1 + euclideanSq x) by ring,
    mul_inv_rev, mul_pow]
  ring

/-- Finite-horizon null occupation, for the same law, yields absolute
continuity of the positive-time averaged occupation measure. -/
theorem c21_averaged_occupation_ac_of_finite_null {d : ℕ}
    (P : Measure (Path d))
    (hfinite : ∀ (N : Set (Vec d)), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 → ∀ n : ℕ,
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (n : ℝ))))
        {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} = 0) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  refine Measure.AbsolutelyContinuous.mk fun N hN hnull => ?_
  rw [Measure.map_apply heval hN]
  have htime : Set.Ioi (0 : ℝ) = ⋃ n : ℕ, Set.Ioc 0 (n : ℝ) := by
    symm
    exact Set.iUnion_Ioc_eq_Ioi_self_iff.mpr (fun x _ => exists_nat_ge x)
  have hpath : ∀ᵐ γ ∂P, ∀ n : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (n : ℝ)), γ t.toNNReal ∉ N := by
    apply ae_all_iff.mpr
    intro n
    have hp : ∀ᵐ z ∂P.prod (volume.restrict (Set.Ioc (0 : ℝ) (n : ℝ))),
        z.1 z.2.toNNReal ∉ N :=
      (ae_iff).2 (by simpa using hfinite N hN hnull n)
    exact Measure.ae_ae_of_ae_prod hp
  have hall : ∀ᵐ γ ∂P, ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      γ t.toNNReal ∉ N := by
    filter_upwards [hpath] with γ hγ
    rw [htime, ae_restrict_iUnion_iff]
    exact hγ
  have hprod : ∀ᵐ z ∂P.prod (volume.restrict (Set.Ioi (0 : ℝ))),
      z.1 z.2.toNNReal ∉ N :=
    (Measure.ae_prod_iff_ae_ae (hN.preimage heval).compl).2 hall
  change (P.prod (volume.restrict (Set.Ioi (0 : ℝ))))
    {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} = 0
  simpa only [not_not] using (ae_iff.mp hprod)

/-- The Euclidean quadratic form dominates the coordinate supremum norm. -/
theorem c21_norm_sq_le_euclideanSq {d : ℕ} (w : Vec d) :
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

/-- The polynomial kernel has an inverse-norm tail after multiplying by
its dimension power. -/
theorem c21_polynomial_kernel_tail_bound {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) {w : Vec d} (hw : 1 ≤ ‖w‖) :
    ‖w‖ ^ d * c16PolynomialKernel 1 m w ≤ ‖w‖⁻¹ := by
  have hd : d < 2 * m := by exact_mod_cast hdm
  have hnorm : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  have hq : 0 < 1 + euclideanSq w := by
    have h := c21_norm_sq_le_euclideanSq w
    nlinarith [sq_nonneg ‖w‖]
  have hpow : ‖w‖ ^ (d + 1) ≤ (1 + euclideanSq w) ^ m := by
    calc
      ‖w‖ ^ (d + 1) ≤ ‖w‖ ^ (2 * m) := pow_le_pow_right₀ hw (by omega)
      _ = (‖w‖ ^ 2) ^ m := by rw [pow_mul]
      _ ≤ (1 + euclideanSq w) ^ m :=
        pow_le_pow_left₀ (sq_nonneg _) (by linarith [c21_norm_sq_le_euclideanSq w]) m
  rw [c16PolynomialKernel, one_pow, inv_pow, ← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hq m) hnorm).2
  simpa [pow_succ, mul_comm] using hpow

/-- The normalized unit-scale kernel satisfies the polynomial decay required
for a noncompact approximate identity. -/
theorem c21_normalized_polynomial_kernel_decay {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    Tendsto (fun w : Vec d => ‖w‖ ^ d * c16NormalizedPolynomialKernel 1 m w)
      (Bornology.cobounded (Vec d)) (𝓝 0) := by
  have hm := c16_polynomial_kernel_integral_pos (d := d) zero_lt_one m hdm
  have hn : Tendsto (fun w : Vec d => ‖w‖) (Bornology.cobounded (Vec d)) atTop :=
    tendsto_norm_cobounded_atTop
  have hlim : Tendsto (fun w : Vec d =>
      (∫ z : Vec d, c16PolynomialKernel 1 m z)⁻¹ * ‖w‖⁻¹)
      (Bornology.cobounded (Vec d)) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hn).const_mul
      (∫ z : Vec d, c16PolynomialKernel 1 m z)⁻¹
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with w
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _)
      ((c16_normalized_polynomial_kernel_properties (d := d) zero_lt_one m hdm).1 w).le
  · filter_upwards [hn.eventually_ge_atTop 1] with w hw
    have h := mul_le_mul_of_nonneg_left (c21_polynomial_kernel_tail_bound hdm hw)
      (inv_nonneg.mpr hm.le)
    simpa [c16NormalizedPolynomialKernel, mul_assoc, mul_comm, mul_left_comm] using h

/-- The normalized polynomial kernel has the usual dilation law. -/
theorem c21_normalized_polynomial_kernel_scaling {d : ℕ} {r : ℝ}
    (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (x : Vec d) :
    r ^ d * c16NormalizedPolynomialKernel r m (r • x) =
      c16NormalizedPolynomialKernel 1 m x := by
  have hrpow : 0 < r ^ d := pow_pos hr _
  have hmassr := c16_polynomial_kernel_integral_pos (d := d) hr m hdm
  have hmass1 := c16_polynomial_kernel_integral_pos (d := d) zero_lt_one m hdm
  have hscale : (r ^ d)⁻¹ * (∫ z : Vec d, c16PolynomialKernel r m z) =
      ((r ^ 2)⁻¹) ^ m * (∫ z : Vec d, c16PolynomialKernel 1 m z) := by
    have h := Measure.integral_comp_smul (volume : Measure (Vec d))
      (c16PolynomialKernel (d := d) r m) r
    simp only [Module.finrank_pi, Fintype.card_fin, abs_of_pos (inv_pos.mpr hrpow),
      smul_eq_mul] at h
    rw [show (fun z : Vec d => c16PolynomialKernel r m (r • z)) =
      (fun z => ((r ^ 2)⁻¹) ^ m * c16PolynomialKernel 1 m z) by
        funext z; exact c21_polynomial_kernel_smul r m z, integral_const_mul] at h
    exact h.symm
  have hratio : r ^ d * (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹ *
      ((r ^ 2)⁻¹) ^ m = (∫ z : Vec d, c16PolynomialKernel 1 m z)⁻¹ := by
    let a : ℝ := ((r ^ 2)⁻¹) ^ m
    change (r ^ d)⁻¹ * (∫ z : Vec d, c16PolynomialKernel r m z) =
      a * (∫ z : Vec d, c16PolynomialKernel 1 m z) at hscale
    change r ^ d * (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹ * a =
      (∫ z : Vec d, c16PolynomialKernel 1 m z)⁻¹
    field_simp [hrpow.ne', hmassr.ne', hmass1.ne'] at hscale ⊢
    nlinarith
  rw [c16NormalizedPolynomialKernel, c16NormalizedPolynomialKernel,
    c21_polynomial_kernel_smul]
  calc
    _ = (r ^ d * (∫ z : Vec d, c16PolynomialKernel r m z)⁻¹ *
        ((r ^ 2)⁻¹) ^ m) * c16PolynomialKernel 1 m x := by ring
    _ = _ := by rw [hratio]


/-- The unit-scale polynomial kernel is an approximate identity on integrable
functions at every point of continuity. -/
theorem c21_polynomial_kernel_approximate_identity {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) {g : Vec d → ℝ} {x : Vec d}
    (hg : Integrable g (volume : Measure (Vec d))) (hgc : ContinuousAt g x) :
    Tendsto (fun c : ℝ => ∫ y : Vec d,
      (c ^ d * c16NormalizedPolynomialKernel 1 m (c • (x - y))) * g y)
      atTop (𝓝 (g x)) := by
  have hp := c16_normalized_polynomial_kernel_properties (d := d) zero_lt_one m hdm
  have hdec : Tendsto (fun w : Vec d =>
      ‖w‖ ^ Module.finrank ℝ (Vec d) * c16NormalizedPolynomialKernel 1 m w)
      (Bornology.cobounded (Vec d)) (𝓝 0) := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      (c21_normalized_polynomial_kernel_decay (d := d) (m := m) hdm)
  have h := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := (volume : Measure (Vec d)))
    (φ := c16NormalizedPolynomialKernel (d := d) 1 m) (g := g) (x₀ := x)
    (fun w => (hp.1 w).le) hp.2.2.2 hdec hg hgc
  simpa only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] using h


/-- Normalized kernels converge at every continuity point as their scale
approaches zero from above. -/
theorem c21_polynomial_kernel_approximate_identity_small_scale {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) {g : Vec d → ℝ} {x : Vec d}
    (hg : Integrable g (volume : Measure (Vec d))) (hgc : ContinuousAt g x) :
    Tendsto (fun r : ℝ => ∫ y : Vec d,
      c16NormalizedPolynomialKernel r m (x - y) * g y)
      (𝓝[>] 0) (𝓝 (g x)) := by
  have h := (c21_polynomial_kernel_approximate_identity hdm hg hgc).comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] 0) atTop)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  change (∫ y : Vec d, (r⁻¹ ^ d * c16NormalizedPolynomialKernel 1 m
      (r⁻¹ • (x - y))) * g y) = ∫ y, c16NormalizedPolynomialKernel r m (x - y) * g y
  apply integral_congr_ae
  filter_upwards [] with y
  have hs := c21_normalized_polynomial_kernel_scaling hr m hdm (r⁻¹ • (x - y))
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hs
  rw [← hs, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero d hr.ne')]


/-- Averaging the polynomial approximate identity against any finite measure
preserves the limit for bounded continuous integrable test functions. -/
theorem c21_polynomial_kernel_test_integrals_tendsto {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {g : Vec d → ℝ} (hg : Integrable g (volume : Measure (Vec d)))
    (hgc : Continuous g) {B : ℝ} (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ => ∫ x : Vec d, ∫ y : Vec d,
      c16NormalizedPolynomialKernel r m (x - y) * g y ∂volume ∂μ)
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => B)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hp := c16_normalized_polynomial_kernel_properties (d := d) hr m hdm
    have hm : Continuous (fun p : Vec d × Vec d =>
        c16NormalizedPolynomialKernel r m (p.1 - p.2) * g p.2) :=
      (hp.2.1.continuous.comp (continuous_fst.sub continuous_snd)).mul
        (hgc.comp continuous_snd)
    exact hm.measurable.aestronglyMeasurable.integral_prod_right'
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hp := c16_normalized_polynomial_kernel_properties (d := d) hr m hdm
    filter_upwards [] with x
    have hi : Integrable (fun y : Vec d => B * c16NormalizedPolynomialKernel r m (x - y))
        volume := (hp.2.2.1.comp_sub_left x).const_mul B
    have hbound : ‖∫ y : Vec d, c16NormalizedPolynomialKernel r m (x - y) * g y‖ ≤
        ∫ y : Vec d, B * c16NormalizedPolynomialKernel r m (x - y) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp.1 _).le]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left (hB y) (hp.1 (x - y)).le)
    simpa only [integral_const_mul, integral_sub_left_eq_self, hp.2.2.2, mul_one] using hbound
  · exact integrable_const B
  · filter_upwards [] with x
    exact c21_polynomial_kernel_approximate_identity_small_scale hdm hg (hgc.continuousAt)


/-- The smoothed densities of a finite measure converge weakly against every
bounded continuous integrable test function. -/
theorem c21_polynomial_smoothing_weak_convergence {d m : ℕ}
    (hdm : (d : ℝ) < 2 * (m : ℝ)) (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {g : Vec d → ℝ} (hg : Integrable g (volume : Measure (Vec d)))
    (hgc : Continuous g) {B : ℝ} (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ => ∫ y : Vec d,
      (∫ x : Vec d, c16NormalizedPolynomialKernel r m (x - y) ∂μ) * g y ∂volume)
      (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
  have h := c21_polynomial_kernel_test_integrals_tendsto hdm μ hg hgc hB
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp := c16_normalized_polynomial_kernel_properties (d := d) hr m hdm
  have hm : AEStronglyMeasurable (fun p : Vec d × Vec d =>
      c16NormalizedPolynomialKernel r m (p.1 - p.2)) (μ.prod volume) :=
    (hp.2.1.continuous.comp (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
  have hi : Integrable (fun p : Vec d × Vec d =>
      c16NormalizedPolynomialKernel r m (p.1 - p.2)) (μ.prod volume) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => hp.2.2.1.comp_sub_left x), ?_⟩
    have heq : (fun x : Vec d => ∫ y, ‖c16NormalizedPolynomialKernel r m (x - y)‖) =
        fun _ => (1 : ℝ) := by
      funext x
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (hp.1 _).le]
      rw [integral_sub_left_eq_self, hp.2.2.2]
    rw [heq]
    exact integrable_const _
  have hprod : Integrable (fun p : Vec d × Vec d =>
      c16NormalizedPolynomialKernel r m (p.1 - p.2) * g p.2) (μ.prod volume) :=
    hi.mul_bdd (hgc.comp continuous_snd).measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hB p.2))
  rw [integral_integral_swap (f := fun x y =>
    c16NormalizedPolynomialKernel r m (x - y) * g y) hprod]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [integral_mul_const]


/-- Polynomial smoothing converges weakly to the finite occupation measure
of the supplied textbook martingale law. -/
theorem c21_textbook_occupation_smoothed_weak_limit {d : ℕ}
    {ω : FieldPair d}
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    Tendsto (fun r : ℝ => ∫ y, φ y *
      (∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (∫ y, φ y ∂μ)) := by
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hφ
  simpa only [mul_comm] using
    (c21_polynomial_smoothing_weak_convergence hdm
      (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
      (hφ.integrable_of_hasCompactSupport hc) hφ hB)

end EinsteinFull
