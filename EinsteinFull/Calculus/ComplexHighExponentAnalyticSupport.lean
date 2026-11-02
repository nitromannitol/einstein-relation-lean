import EinsteinFull.Calculus.ComplexHighExponentContinuitySupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville

/-! Entire complex-force dependence of the actual higher-Lp semigroups.

Higher moments first give continuity in the stronger norm. Injective-inclusion
Morera then gives strong holomorphy. Cauchy estimates upgrade this to operator
norm holomorphy using the already proved exponential growth, with no additional
physical estimate or regularity hypothesis.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous complex linear maps commute with the actual two-edge contour integral. -/
theorem map_wedgeIntegral (J : E →L[ℂ] F) {f : ℂ → E} (hf : Continuous f) (z w : ℂ) :
    J (Complex.wedgeIntegral z w f) = Complex.wedgeIntegral z w (fun x => J (f x)) := by
  have hr : Continuous (fun x : ℝ => f ((x : ℂ) + z.im * Complex.I)) :=
    hf.comp (Complex.continuous_ofReal.add continuous_const)
  have hi : Continuous (fun y : ℝ => f ((w.re : ℂ) + y * Complex.I)) :=
    hf.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  simp only [Complex.wedgeIntegral, map_add, map_smul,
    ← J.intervalIntegral_comp_comm (hr.intervalIntegrable (μ := volume) z.re w.re),
    ← J.intervalIntegral_comp_comm (hi.intervalIntegrable (μ := volume) z.im w.im)]

/-- Morera transfers holomorphy through an injective bounded inclusion once
continuity in the stronger norm has been proved. -/
theorem differentiable_of_injective_clm_comp (J : E →L[ℂ] F) (hJ : Function.Injective J)
    {f : ℂ → E} (hf : Continuous f) (h : Differentiable ℂ (fun z => J (f z))) :
    Differentiable ℂ f := by
  have hc : Complex.IsConservativeOn f Set.univ := by
    intro z w _
    apply hJ
    rw [map_neg, map_wedgeIntegral J hf, map_wedgeIntegral J hf]
    exact h.differentiableOn.isConservativeOn z w (Set.subset_univ _)
  exact differentiableOn_univ.mp
    ((Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).mp
      ⟨hc, hf.continuousOn⟩)

/-- The entire strong-norm conclusion follows from the same injective transfer. -/
theorem analyticAt_of_injective_clm_comp (J : E →L[ℂ] F) (hJ : Function.Injective J)
    {f : ℂ → E} (hf : Continuous f) (h : ∀ z, AnalyticAt ℂ (fun z => J (f z)) z)
    (z : ℂ) : AnalyticAt ℂ f z :=
  (differentiable_of_injective_clm_comp J hJ hf
    (fun z => (h z).differentiableAt)).analyticAt z

omit [CompleteSpace E] in
/-- Continuous exponential envelopes reduce dense orbit continuity to the
uniform contraction case, on any parameter space. -/
theorem continuous_family_of_dense_exp_envelope
    {X : Type*} [TopologicalSpace X]
    (B : X → E →L[ℂ] E) (a : X → ℝ) (ha : Continuous a)
    (D : Set E) (hD : Dense D) (hcont : ∀ f ∈ D, Continuous (fun x => B x f))
    (hnorm : ∀ x, ‖B x‖ ≤ Real.exp (a x)) :
    Continuous (fun xf : X × E => B xf.1 xf.2) := by
  let R (x : X) := (Real.exp (-(a x)) : ℂ) • B x
  have hR : Continuous (fun fx : E × X => R fx.2 fx.1) := by
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 hD
    · intro f hf
      exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp ha.neg)).smul
        (hcont f hf)
    · intro x
      apply ContinuousLinearMap.lipschitzWith_of_opNorm_le (f := R x) (K := 1)
      calc
        ‖R x‖ = Real.exp (-(a x)) * ‖B x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-(a x)) * Real.exp (a x) :=
          mul_le_mul_of_nonneg_left (hnorm x) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hc := ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp ha)).comp
    continuous_fst).smul (hR.comp continuous_swap)
  convert hc using 1
  funext xf
  change B xf.1 xf.2 = (Real.exp (a xf.1) : ℂ) • R xf.1 xf.2
  simp only [R, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.ofReal_mul,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_smul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Cauchy's derivative estimate gives an operator-norm increment bound from
strong holomorphy and an actual bound on a larger disc. -/
theorem norm_clm_sub_le_of_differentiable_apply_of_bound
    (B : ℂ → E →L[ℂ] F) (hB : ∀ f, Differentiable ℂ (fun z => B z f))
    {z₀ z : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ w ∈ Metric.closedBall z₀ 2, ‖B w‖ ≤ C)
    (hz : z ∈ Metric.ball z₀ 1) : ‖B z - B z₀‖ ≤ C * ‖z - z₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro f
  have hd (w : ℂ) (hw : w ∈ Metric.ball z₀ 1) :
      ‖deriv (fun u => B u f) w‖ ≤ C * ‖f‖ := by
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (C := C * ‖f‖)
      (by norm_num : (0:ℝ) < 1)
      (hB f).diffContOnCl (fun u hu => ?_)
    · simpa only [div_one] using h
    · apply ((B u).le_opNorm f).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      apply hbound u
      have hdist := dist_triangle u w z₀
      have hwu : dist u w = 1 := Metric.mem_sphere.mp hu
      have hw₀ : dist w z₀ < 1 := Metric.mem_ball.mp hw
      exact Metric.mem_closedBall.mpr (by linarith)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w (_ : w ∈ Metric.ball z₀ 1) => hB f w) hd
    (convex_ball z₀ 1) (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1)) hz
  simpa only [ContinuousLinearMap.sub_apply, mul_assoc, mul_comm ‖f‖ ‖z-z₀‖] using hh

omit [CompleteSpace E] [CompleteSpace F] in
/-- Strongly entire operators bounded by a continuous real envelope are
continuous in operator norm. -/
theorem continuous_clm_of_differentiable_apply_of_envelope
    (B : ℂ → E →L[ℂ] F) (hB : ∀ f, Differentiable ℂ (fun z => B z f))
    (M : ℂ → ℝ) (hM : Continuous M) (hbound : ∀ z, ‖B z‖ ≤ M z) :
    Continuous B := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨R, hR⟩ := (isCompact_closedBall z₀ 2).bddAbove_image hM.continuousOn
  let C := max R 0
  have hC : 0 ≤ C := le_max_right _ _
  have hdisc : ∀ w ∈ Metric.closedBall z₀ 2, ‖B w‖ ≤ C := by
    intro w hw
    exact (hbound w).trans ((hR (Set.mem_image_of_mem M hw)).trans (le_max_left _ _))
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε / (C+1)), lt_min (by norm_num) (div_pos hε (by linarith)), ?_⟩
  intro z hz
  have hsmall : dist z z₀ < 1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hprod : (C+1) * dist z z₀ < ε :=
    (lt_div_iff₀' (show 0 < C+1 by linarith)).mp
      (lt_of_lt_of_le hz (min_le_right _ _))
  calc
    dist (B z) (B z₀) = ‖B z - B z₀‖ := dist_eq_norm _ _
    _ ≤ C * dist z z₀ := by
      simpa only [dist_eq_norm] using
        norm_clm_sub_le_of_differentiable_apply_of_bound B hB hC hdisc hsmall
    _ < ε := lt_of_le_of_lt (by nlinarith [dist_nonneg (x := z) (y := z₀)]) hprod

omit [CompleteSpace E] in
/-- Strong holomorphy and actual operator-norm continuity imply full
operator-norm holomorphy, by evaluation of Morera contour integrals. -/
theorem differentiable_clm_of_apply_of_continuous
    (B : ℂ → E →L[ℂ] F) (hc : Continuous B)
    (hB : ∀ f, Differentiable ℂ (fun z => B z f)) : Differentiable ℂ B := by
  apply differentiableOn_univ.mp
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn isOpen_univ).mp
  refine ⟨?_, hc.continuousOn⟩
  intro z w _
  apply ContinuousLinearMap.ext
  intro f
  have hh := (hB f).differentiableOn.isConservativeOn z w (Set.subset_univ _)
  have hm := map_wedgeIntegral (ContinuousLinearMap.apply ℂ F f) hc z w
  have hn := map_wedgeIntegral (ContinuousLinearMap.apply ℂ F f) hc w z
  change (Complex.wedgeIntegral z w B) f = -(Complex.wedgeIntegral w z B) f
  change (Complex.wedgeIntegral z w B) f = Complex.wedgeIntegral z w (fun x => B x f) at hm
  change (Complex.wedgeIntegral w z B) f = Complex.wedgeIntegral w z (fun x => B x f) at hn
  rw [hm, hn]
  exact hh

omit [CompleteSpace E] in
/-- Locally bounded strong entire dependence is entire in operator norm. -/
theorem analyticAt_clm_of_apply_of_envelope
    (B : ℂ → E →L[ℂ] F) (hB : ∀ f z, AnalyticAt ℂ (fun u => B u f) z)
    (M : ℂ → ℝ) (hM : Continuous M) (hbound : ∀ z, ‖B z‖ ≤ M z) (z : ℂ) :
    AnalyticAt ℂ B z := by
  have hd : ∀ f, Differentiable ℂ (fun u => B u f) :=
    fun f u => (hB f u).differentiableAt
  exact (differentiable_clm_of_apply_of_continuous B
    (continuous_clm_of_differentiable_apply_of_envelope B hd M hM hbound) hd).analyticAt z

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An actual L2-continuous operator restriction with proved higher moments
is jointly continuous in its parameter and its actual Lp datum. -/
theorem continuous_highLp_restriction_of_envelopes [IsProbabilityMeasure μ]
    {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp2 : 2 ≤ p) (hpq : p < q)
    (B : X → Lp ℂ (ENNReal.ofReal p) μ →L[ℂ] Lp ℂ (ENNReal.ofReal p) μ)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hcont : ∀ f, Continuous (fun x => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (B x f)))
    (hnorm : ∀ x, ‖B x‖ ≤ Real.exp (a x))
    (hbound : ∀ f : Lp ℂ (ENNReal.ofReal p) μ,
      MemLp f (ENNReal.ofReal q) μ → ∀ x,
      eLpNorm (B x f) (ENNReal.ofReal q) μ ≤ eLpNorm f (ENNReal.ofReal q) μ *
        ENNReal.ofReal (Real.exp (b x))) :
    Continuous (fun xf : X × Lp ℂ (ENNReal.ofReal p) μ => B xf.1 xf.2) := by
  have hsimple (f : Lp.simpleFunc ℂ (ENNReal.ofReal p) μ) :
      Continuous (fun x => B x f) := by
    have hf : MemLp (f : Lp ℂ (ENNReal.ofReal p) μ) (ENNReal.ofReal q) μ :=
      (memLp_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun f)).mp
        (((Lp.simpleFunc.toSimpleFunc f).memLp_top μ).mono_exponent le_top)
    apply continuous_highLp_of_L2_of_bound hp2 hpq _ (hcont f)
      (fun x => (eLpNorm (f : Lp ℂ (ENNReal.ofReal p) μ) (ENNReal.ofReal q) μ).toReal *
        Real.exp (b x)) (continuous_const.mul (Real.continuous_exp.comp hb))
    intro x
    simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using hbound f hf x
  exact continuous_family_of_dense_exp_envelope B a ha _
    (Lp.simpleFunc.dense (E := ℂ) (μ := μ) ENNReal.ofReal_ne_top)
    (fun f hf => hsimple ⟨f, hf⟩) hnorm

/-- Entire L2 dependence transfers to every actual higher-Lp orbit when genuine
continuous moment envelopes have already been proved. -/
theorem analyticAt_highLp_restriction_of_envelopes [IsProbabilityMeasure μ]
    {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp2 : 2 ≤ p) (hpq : p < q)
    (B : ℂ → Lp ℂ (ENNReal.ofReal p) μ →L[ℂ] Lp ℂ (ENNReal.ofReal p) μ)
    (a b : ℂ → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hA : ∀ f z, AnalyticAt ℂ (fun x => complexLpToL2 μ
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (B x f)) z)
    (hnorm : ∀ z, ‖B z‖ ≤ Real.exp (a z))
    (hbound : ∀ f : Lp ℂ (ENNReal.ofReal p) μ,
      MemLp f (ENNReal.ofReal q) μ → ∀ z,
      eLpNorm (B z f) (ENNReal.ofReal q) μ ≤ eLpNorm f (ENNReal.ofReal q) μ *
        ENNReal.ofReal (Real.exp (b z)))
    (f : Lp ℂ (ENNReal.ofReal p) μ) (z : ℂ) :
    AnalyticAt ℂ (fun x => B x f) z := by
  have hc := continuous_highLp_restriction_of_envelopes hp2 hpq B a b ha hb
    (fun g => continuous_iff_continuousAt.mpr (fun x => (hA g x).continuousAt)) hnorm hbound
  exact analyticAt_of_injective_clm_comp (complexLpToL2CLM μ (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)))
    (complexLpToL2_injective μ (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2))) (hc.comp (continuous_id.prodMk continuous_const))
    (hA f) z

section Physical
variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {F G : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {p : ℝ} (hp2 : 2 ≤ p)

/-- Actual forward higher-Lp orbits are entire in complex force. -/
theorem analyticAt_complexEnvironmentSemigroup_lpRestriction_apply
    (hF : ∀ z, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0)
    (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z => (hF z).lpRestriction hp2 t f) z₀ := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  let K := Real.exp (2 * Λ₀) * Λ₀
  let a (z : ℂ) := (d : ℝ) * K * (‖z‖ * K) ^ 2 * (t : ℝ)
  have ha : Continuous a := by dsimp only [a]; fun_prop
  apply analyticAt_highLp_restriction_of_envelopes hp2 (q := p + 1) (by linarith)
    (fun z => (hF z).lpRestriction hp2 t) a a ha ha
  · intro g z
    have h := ((ContinuousLinearMap.apply ℂ _ (complexLpToL2 (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g)).analyticAt _).comp
      (analyticAt_complexEnvironmentSemigroup hF t z)
    simpa only [(hF _).lpRestriction_apply hp2, Function.comp_def] using! h
  · intro z
    exact (hF z).norm_lpRestriction_le hp2 t
  · intro g hg z
    have hb := ((hF z).highLp_bound (show 2 ≤ p + 1 by linarith)
      (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g) hg t).2
    simpa only [← (hF z).lpRestriction_apply hp2 t g, complexLpToL2_apply] using hb

/-- Actual bilinear-transpose higher-Lp orbits are entire in complex force. -/
theorem analyticAt_complexTransposeSemigroup_lpRestriction_apply
    (hF : ∀ z, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z, IsComplexTransposeSemigroup Q (F z) (G z)) (t : ℝ≥0)
    (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z => (hG z).lpRestriction hp2 (hF z) t f) z₀ := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  let K := Real.exp (2 * Λ₀) * Λ₀
  let a (z : ℂ) := (d : ℝ) * K * (‖z‖ * K * (p - 1)) ^ 2 * (t : ℝ)
  let b (z : ℂ) := (d : ℝ) * K * (‖z‖ * K * (p + 1 - 1)) ^ 2 * (t : ℝ)
  have ha : Continuous a := by dsimp only [a]; fun_prop
  have hb : Continuous b := by dsimp only [b]; fun_prop
  apply analyticAt_highLp_restriction_of_envelopes hp2 (q := p + 1) (by linarith)
    (fun z => (hG z).lpRestriction hp2 (hF z) t) a b ha hb
  · intro g z
    have h := ((ContinuousLinearMap.apply ℂ _ (complexLpToL2 (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g)).analyticAt _).comp
      (analyticAt_complexTransposeSemigroup hF hG t z)
    simpa only [(hG _).lpRestriction_apply hp2 (hF _), Function.comp_def] using! h
  · intro z
    exact (hG z).norm_lpRestriction_le hp2 (hF z) t
  · intro g hg z
    have hb := ((hG z).highLp_bound (hF z) (show 2 ≤ p + 1 by linarith)
      (complexLpToL2 (reducedLaw Q)
        (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) g) hg t).2
    simpa only [← (hG z).lpRestriction_apply hp2 (hF z) t g, complexLpToL2_apply] using hb

/-- The actual forward higher-Lp semigroup is entire in operator norm. -/
theorem analyticAt_complexEnvironmentSemigroup_lpRestriction
    (hF : ∀ z, IsComplexEnvironmentSemigroup Q i z (F z)) (t : ℝ≥0) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z => (hF z).lpRestriction hp2 t) z₀ := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  apply analyticAt_clm_of_apply_of_envelope (fun z => (hF z).lpRestriction hp2 t)
    (fun f z => analyticAt_complexEnvironmentSemigroup_lpRestriction_apply hp2 hF t f z)
    (fun z => Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖z‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)))
  · fun_prop
  · intro z
    exact (hF z).norm_lpRestriction_le hp2 t

/-- The actual bilinear transpose on higher Lp is entire in operator norm. -/
theorem analyticAt_complexTransposeSemigroup_lpRestriction
    (hF : ∀ z, IsComplexEnvironmentSemigroup Q i z (F z))
    (hG : ∀ z, IsComplexTransposeSemigroup Q (F z) (G z)) (t : ℝ≥0) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z => (hG z).lpRestriction hp2 (hF z) t) z₀ := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  apply analyticAt_clm_of_apply_of_envelope (fun z => (hG z).lpRestriction hp2 (hF z) t)
    (fun f z => analyticAt_complexTransposeSemigroup_lpRestriction_apply hp2 hF hG t f z)
    (fun z => Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖z‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p - 1)) ^ 2) * (t : ℝ)))
  · fun_prop
  · intro z
    exact (hG z).norm_lpRestriction_le hp2 (hF z) t

/-- The internally constructed forward evolution is entire on actual higher Lp. -/
theorem analyticAt_forcedComplexEvolution_lpRestriction
    (t : ℝ≥0) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z =>
      (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z).lpRestriction hp2 t) z₀ :=
  analyticAt_complexEnvironmentSemigroup_lpRestriction hp2
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z) t z₀

/-- The internally constructed actual bilinear transpose is entire on higher Lp. -/
theorem analyticAt_forcedComplexEvolution_transpose_lpRestriction
    (t : ℝ≥0) (z₀ : ℂ) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    AnalyticAt ℂ (fun z =>
      (isComplexTransposeSemigroup_complexL2Transpose Q (forcedComplexEvolution Q i z)).lpRestriction hp2
          (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z) t) z₀ :=
  analyticAt_complexTransposeSemigroup_lpRestriction hp2
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q i z)
    (fun z => isComplexTransposeSemigroup_complexL2Transpose Q (forcedComplexEvolution Q i z)) t z₀

end Physical
end EinsteinFull
