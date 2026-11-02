import EinsteinFull.Calculus.CLReducedGrowthMartingale
import EinsteinFull.Calculus.CLTwoSidedAnnealedCovariance

/-!
# Characteristic functions of the reduced diffusion in a constant environment

In a translation invariant environment the reduced coefficient is a constant matrix `A` and the
drift vanishes, so the reduced generator acts on `cos (ξ · y)` and `sin (ξ · y)` as multiplication
by `-½ ξ · A ξ`. Both functions have bounded gradient, so their compensated tests are martingales;
paired with a bounded past-measurable weight, the expectation of the test at time `t` solves
`g' = -κ g` and decays like `exp (-κ (t - s))`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem hasFDerivAt_dot (ξ y : Vec d) : HasFDerivAt (fun z : Vec d => dot ξ z) (dotCLM ξ) y := by
  have h : (fun z : Vec d => dot ξ z) = dotCLM ξ := funext fun z => (dotCLM_apply ξ z).symm
  rw [h]
  exact (dotCLM ξ).hasFDerivAt

theorem dot_unitVector (ξ : Vec d) (j : Fin d) : dot ξ (unitVector j) = ξ j := by
  simp [dot, unitVector, Pi.single_apply]

theorem contDiff_cos_dot (ξ : Vec d) : ContDiff ℝ (⊤ : ℕ∞) fun z => Real.cos (dot ξ z) :=
  Real.contDiff_cos.comp (contDiff_dot ξ)

theorem contDiff_sin_dot (ξ : Vec d) : ContDiff ℝ (⊤ : ℕ∞) fun z => Real.sin (dot ξ z) :=
  Real.contDiff_sin.comp (contDiff_dot ξ)

theorem fderiv_cos_dot_apply (ξ y : Vec d) (j : Fin d) :
    fderiv ℝ (fun z => Real.cos (dot ξ z)) y (unitVector j) = -(ξ j) * Real.sin (dot ξ y) := by
  have h : HasFDerivAt (fun z => Real.cos (dot ξ z)) ((-Real.sin (dot ξ y)) • dotCLM ξ) y :=
    (Real.hasDerivAt_cos _).comp_hasFDerivAt y (hasFDerivAt_dot ξ y)
  rw [h.fderiv]
  simp only [smul_apply, dotCLM_apply, dot_unitVector, smul_eq_mul]
  ring

theorem fderiv_sin_dot_apply (ξ y : Vec d) (j : Fin d) :
    fderiv ℝ (fun z => Real.sin (dot ξ z)) y (unitVector j) = ξ j * Real.cos (dot ξ y) := by
  have h : HasFDerivAt (fun z => Real.sin (dot ξ z)) (Real.cos (dot ξ y) • dotCLM ξ) y :=
    (Real.hasDerivAt_sin _).comp_hasFDerivAt y (hasFDerivAt_dot ξ y)
  rw [h.fderiv]
  simp only [smul_apply, dotCLM_apply, dot_unitVector, smul_eq_mul]
  ring

theorem fderiv_fderiv_cos_dot_apply (ξ y : Vec d) (k l : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun z => Real.cos (dot ξ z)) z (unitVector l)) y
      (unitVector k) = -(ξ l * ξ k) * Real.cos (dot ξ y) := by
  have e : (fun z => fderiv ℝ (fun z => Real.cos (dot ξ z)) z (unitVector l)) =
      fun z => -(ξ l) * Real.sin (dot ξ z) := funext fun z => fderiv_cos_dot_apply ξ z l
  rw [e]
  have h : HasFDerivAt (fun z => -(ξ l) * Real.sin (dot ξ z))
      (-(ξ l) • (Real.cos (dot ξ y) • dotCLM ξ)) y :=
    ((Real.hasDerivAt_sin _).comp_hasFDerivAt y (hasFDerivAt_dot ξ y)).const_mul (-(ξ l))
  rw [h.fderiv]
  simp only [smul_apply, dotCLM_apply, dot_unitVector, smul_eq_mul]
  ring

theorem fderiv_fderiv_sin_dot_apply (ξ y : Vec d) (k l : Fin d) :
    fderiv ℝ (fun z => fderiv ℝ (fun z => Real.sin (dot ξ z)) z (unitVector l)) y
      (unitVector k) = -(ξ l * ξ k) * Real.sin (dot ξ y) := by
  have e : (fun z => fderiv ℝ (fun z => Real.sin (dot ξ z)) z (unitVector l)) =
      fun z => ξ l * Real.cos (dot ξ z) := funext fun z => fderiv_sin_dot_apply ξ z l
  rw [e]
  have h : HasFDerivAt (fun z => ξ l * Real.cos (dot ξ z))
      (ξ l • ((-Real.sin (dot ξ y)) • dotCLM ξ)) y :=
    ((Real.hasDerivAt_cos _).comp_hasFDerivAt y (hasFDerivAt_dot ξ y)).const_mul (ξ l)
  rw [h.fderiv]
  simp only [smul_apply, dotCLM_apply, dot_unitVector, smul_eq_mul]
  ring

theorem abs_fderiv_cos_dot_le (ξ y : Vec d) (j : Fin d) :
    |fderiv ℝ (fun z => Real.cos (dot ξ z)) y (unitVector j)| ≤ ∑ k, |ξ k| := by
  rw [fderiv_cos_dot_apply, abs_mul, abs_neg]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans
    (Finset.single_le_sum (f := fun k => |ξ k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j))

theorem abs_fderiv_sin_dot_le (ξ y : Vec d) (j : Fin d) :
    |fderiv ℝ (fun z => Real.sin (dot ξ z)) y (unitVector j)| ≤ ∑ k, |ξ k| := by
  rw [fderiv_sin_dot_apply, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
    (Finset.single_le_sum (f := fun k => |ξ k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j))

section ConstantField

variable {c : FieldPair d} (hc : ∀ x, translate x c = c)

include hc in
theorem reducedCoefficient_const (y : Vec d) : reducedCoefficient c y = reducedCoefficient c 0 := by
  have h := reducedCoefficient_translate y c 0
  rw [hc, add_zero] at h
  exact h.symm

include hc in
theorem forcedDrift_const (i : Fin d) (y : Vec d) : forcedDrift (reducedCoefficient c) i 0 y = 0 := by
  funext j
  have h0 : ∀ (a : ℝ) (z : Vec d), fderiv ℝ (fun _ : Vec d => a) z = 0 := fun a z => by simp
  have h : ∀ k, (fun z => reducedCoefficient c z k j) = fun _ => reducedCoefficient c 0 k j :=
    fun k => funext fun z => by rw [reducedCoefficient_const hc z]
  simp only [forcedDrift, matrixDivDrift, coordinateDerivative, h, h0, zero_mul, add_zero,
    Pi.zero_apply, zero_apply, Finset.sum_const_zero, mul_zero]

include hc in
theorem reducedGenerator_const (hs : IsSmoothFieldPair c) (i : Fin d) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : Vec d) :
    reducedGenerator i c 0 f y = (1 / 2 : ℝ) * ∑ k, ∑ l, reducedCoefficient c 0 k l *
      fderiv ℝ (fun z => fderiv ℝ f z (unitVector l)) y (unitVector k) := by
  rw [reducedGenerator_eq_svGenerator hs i 0 (contDiff_two_of_top hf)]
  simp only [External.Draft.svGenerator, forcedDrift_const hc, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, reducedCoefficient_const hc y]

theorem quad_sum_eq (A : Mat d) (ξ : Vec d) (C : ℝ) :
    (1 / 2 : ℝ) * ∑ k, ∑ l, A k l * (-(ξ l * ξ k) * C) =
      -((1 / 2 : ℝ) * dot ξ (A.mulVec ξ)) * C := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib, mul_neg]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

include hc in
theorem reducedGenerator_cos_dot (hs : IsSmoothFieldPair c) (i : Fin d) (ξ y : Vec d) :
    reducedGenerator i c 0 (fun z => Real.cos (dot ξ z)) y =
      -((1 / 2 : ℝ) * dot ξ ((reducedCoefficient c 0).mulVec ξ)) * Real.cos (dot ξ y) := by
  rw [reducedGenerator_const hc hs i (contDiff_cos_dot ξ) y]
  simp only [fderiv_fderiv_cos_dot_apply]
  exact quad_sum_eq _ ξ _

include hc in
theorem reducedGenerator_sin_dot (hs : IsSmoothFieldPair c) (i : Fin d) (ξ y : Vec d) :
    reducedGenerator i c 0 (fun z => Real.sin (dot ξ z)) y =
      -((1 / 2 : ℝ) * dot ξ ((reducedCoefficient c 0).mulVec ξ)) * Real.sin (dot ξ y) := by
  rw [reducedGenerator_const hc hs i (contDiff_sin_dot ξ) y]
  simp only [fderiv_fderiv_sin_dot_apply]
  exact quad_sum_eq _ ξ _

end ConstantField

/-- A continuous function with `g r = g s - κ ∫ₛʳ g` for `r ≥ s` decays exponentially. -/
theorem eq_exp_mul_of_integral_eq {g : ℝ → ℝ} (hg : Continuous g) {s κ : ℝ}
    (h : ∀ r, s ≤ r → g r = g s - κ * ∫ u in s..r, g u) (r : ℝ) (hr : s ≤ r) :
    g r = Real.exp (-κ * (r - s)) * g s := by
  let G : ℝ → ℝ := fun x => Real.exp (κ * (x - s)) * g x
  have hφ : ∀ x, HasDerivAt (fun r => g s - κ * ∫ u in s..r, g u) (-(κ * g x)) x := fun x => by
    have h1 := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable s x)
      (hg.stronglyMeasurableAtFilter volume _) hg.continuousAt
    exact (h1.const_mul κ).const_sub (g s)
  have hgd : ∀ x, s ≤ x → HasDerivWithinAt g (-(κ * g x)) (Ici x) x := fun x hx =>
    (hφ x).hasDerivWithinAt.congr (fun y hy => h y (hx.trans hy)) (h x hx)
  have hGd : ∀ x, s ≤ x → HasDerivWithinAt G 0 (Ici x) x := fun x hx => by
    have he : HasDerivAt (fun x => Real.exp (κ * (x - s))) (Real.exp (κ * (x - s)) * κ) x := by
      have h1 := (((hasDerivAt_id x).sub_const s).const_mul κ).exp
      simpa only [id_eq, mul_one] using h1
    have h2 := he.hasDerivWithinAt.mul (hgd x hx)
    convert h2 using 1
    ring
  have hGc : Continuous G :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul hg
  have hconst := constant_of_has_deriv_right_zero hGc.continuousOn
    (fun x hx => hGd x hx.1) r ⟨hr, le_rfl⟩
  simp only [G, sub_self, mul_zero, Real.exp_zero, one_mul] at hconst
  calc g r = Real.exp (-κ * (r - s)) * (Real.exp (κ * (r - s)) * g r) := by
        rw [← mul_assoc, ← Real.exp_add]
        have : -κ * (r - s) + κ * (r - s) = 0 := by ring
        rw [this, Real.exp_zero, one_mul]
    _ = Real.exp (-κ * (r - s)) * g s := by rw [hconst]

/-- Against a bounded weight measurable at time `s`, a martingale has the same expectation at
every later time. -/
theorem integral_mul_martingale_eq {M : ℝ≥0 → Path d → ℝ} {P : Measure (Path d)}
    [IsFiniteMeasure P] (hM : Martingale M (pathFiltration d) P) (hMi : ∀ t, Integrable (M t) P)
    {s t : ℝ≥0} (hst : s ≤ t) {Z : Path d → ℝ} (hZ : StronglyMeasurable[pathFiltration d s] Z)
    {C : ℝ} (hC : ∀ γ, |Z γ| ≤ C) :
    ∫ γ, Z γ * M t γ ∂P = ∫ γ, Z γ * M s γ ∂P := by
  have hZt : Integrable (fun γ => Z γ * M t γ) P :=
    (hMi t).bdd_mul (c := C) (hZ.mono ((pathFiltration d).le s)).aestronglyMeasurable
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hC γ)
  have h1 := condExp_mul_of_stronglyMeasurable_left (m := pathFiltration d s) (μ := P) hZ hZt
    (hMi t)
  rw [← integral_condExp ((pathFiltration d).le s) (f := fun γ => Z γ * M t γ)]
  refine integral_congr_ae (h1.trans ?_)
  filter_upwards [hM.2 s t hst] with γ hγ
  simp only [Pi.mul_apply, hγ]

section Evolution

variable {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω)
  (i : Fin d) {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω 0) 0 P)

include hΛ hω hs hP in
/-- For a bounded eigenfunction `L f = -κ f` with bounded gradient and a bounded weight `Z`
measurable at time `s`, the expectation `E[Z f(γ_t)]` decays like `exp (-κ (t - s))`. -/
theorem integral_mul_eigen_evolution {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {G0 : ℝ}
    (hG0 : ∀ y j, |fderiv ℝ f y (unitVector j)| ≤ G0) (hfb : ∀ y, |f y| ≤ 1) {κ : ℝ}
    (hLf : ∀ y, reducedGenerator i ω 0 f y = -κ * f y) {s : ℝ≥0} {Z : Path d → ℝ}
    (hZ : StronglyMeasurable[pathFiltration d s] Z) {C : ℝ} (hC : ∀ γ, |Z γ| ≤ C) {t : ℝ≥0}
    (hst : s ≤ t) :
    ∫ γ, Z γ * f (γ t) ∂P = Real.exp (-κ * ((t : ℝ) - s)) * ∫ γ, Z γ * f (γ s) ∂P := by
  have : IsProbabilityMeasure P := hP.1
  have hmart := reduced_growth_martingale hΛ hω hs i 0 hP hf hG0 (a := 1) (b := 0)
    (fun y => by simpa only [zero_mul, add_zero] using hfb y) zero_le_one le_rfl
  have hZm : Measurable Z := (hZ.mono ((pathFiltration d).le s)).measurable
  have hfc : Continuous f := hf.continuous
  have hLc : Continuous (reducedGenerator i ω 0 f) := continuous_reducedGenerator_apply hs i 0 hf
  have hZf : ∀ (u : ℝ≥0) (γ : Path d), |Z γ * f (γ u)| ≤ C := fun u γ => by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hfb _)).trans (hC γ)
  have hMi : ∀ t, Integrable (compensatedTest (reducedGenerator i ω 0) f t) P := fun t => by
    refine Integrable.of_bound (continuous_compensatedTest_path hfc hLc t).aestronglyMeasurable
      (2 + |κ| * t) (ae_of_all _ fun γ => ?_)
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (C := |κ|) (f := fun u : ℝ => reducedGenerator i ω 0 f (γ u.toNNReal)) (fun u _ => by
        rw [hLf, Real.norm_eq_abs, abs_mul, abs_neg]
        exact mul_le_of_le_one_right (abs_nonneg _) (hfb _))
    rw [sub_zero, abs_of_nonneg t.coe_nonneg, Real.norm_eq_abs] at hI
    simp only [compensatedTest, Real.norm_eq_abs]
    have h1 := abs_le.1 (hfb (γ t))
    have h2 := abs_le.1 (hfb (γ 0))
    have h3 := abs_le.1 hI
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hb : ∀ u : ℝ≥0, Integrable (fun γ => Z γ * f (γ u)) P := fun u =>
    Integrable.of_bound ((hZm.mul (hfc.measurable.comp
      (continuous_eval_const u).measurable)).aestronglyMeasurable) C
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hZf u γ)
  let g : ℝ → ℝ := fun r => ∫ γ, Z γ * f (γ r.toNNReal) ∂P
  have hgc : Continuous g := by
    refine continuous_of_dominated (bound := fun _ => C) (fun r => (hb _).aestronglyMeasurable)
      (fun r => ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hZf _ γ)
      (integrable_const C) (ae_of_all _ fun γ => ?_)
    exact continuous_const.mul (hfc.comp (γ.continuous.comp continuous_real_toNNReal))
  have hid : ∀ r : ℝ, (s : ℝ) ≤ r → g r = g s - κ * ∫ u in (s : ℝ)..r, g u := by
    intro r hr
    have hr0 : 0 ≤ r := s.coe_nonneg.trans hr
    have hsr : s ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact hr
    have hm := integral_mul_martingale_eq hmart hMi hsr hZ hC
    have hdiff : ∀ γ : Path d, Z γ * compensatedTest (reducedGenerator i ω 0) f r.toNNReal γ -
        Z γ * compensatedTest (reducedGenerator i ω 0) f s γ =
        (Z γ * f (γ r.toNNReal) - Z γ * f (γ s)) +
          κ * ∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal) := by
      intro γ
      have hcont : Continuous fun u : ℝ => reducedGenerator i ω 0 f (γ u.toNNReal) :=
        hLc.comp (γ.continuous.comp continuous_real_toNNReal)
      have hsub := intervalIntegral.integral_interval_sub_left
        (hcont.intervalIntegrable (μ := volume) 0 r)
        (hcont.intervalIntegrable (μ := volume) 0 (s : ℝ))
      have hLi : ∫ u in (s : ℝ)..r, reducedGenerator i ω 0 f (γ u.toNNReal) =
          -κ * ∫ u in (s : ℝ)..r, f (γ u.toNNReal) := by
        simp_rw [hLf]
        exact intervalIntegral.integral_const_mul _ _
      have hZi : ∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal) =
          Z γ * ∫ u in (s : ℝ)..r, f (γ u.toNNReal) := intervalIntegral.integral_const_mul _ _
      simp only [compensatedTest, Real.coe_toNNReal _ hr0]
      rw [hZi]
      have e : (∫ u in (0 : ℝ)..r, reducedGenerator i ω 0 f (γ u.toNNReal)) =
          (∫ u in (0 : ℝ)..(s : ℝ), reducedGenerator i ω 0 f (γ u.toNNReal)) +
            -κ * ∫ u in (s : ℝ)..r, f (γ u.toNNReal) := by
        rw [← hLi, ← hsub]
        ring
      rw [e]
      ring
    have hIc : Continuous fun γ : Path d => ∫ u in (s : ℝ)..r, f (γ u.toNNReal) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (γ : Path d) (u : ℝ) => f (γ u.toNNReal))
        (hfc.comp (continuous_eval.comp (continuous_fst.prodMk
          (continuous_real_toNNReal.comp continuous_snd)))) _ _
    have hIint : Integrable (fun γ => ∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal)) P := by
      have e : (fun γ => ∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal)) =
          fun γ => Z γ * ∫ u in (s : ℝ)..r, f (γ u.toNNReal) :=
        funext fun γ => intervalIntegral.integral_const_mul _ _
      rw [e]
      refine Integrable.of_bound (hZm.mul hIc.measurable).aestronglyMeasurable (C * (r - s))
        (ae_of_all _ fun γ => ?_)
      have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := r)
        (C := 1) (f := fun u : ℝ => f (γ u.toNNReal)) (fun u _ => by
          rw [Real.norm_eq_abs]; exact hfb _)
      rw [abs_of_nonneg (sub_nonneg.2 hr), one_mul] at hI
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hC γ) hI (norm_nonneg _) ((abs_nonneg _).trans (hC γ))
    have hfub : ∫ γ, (∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal)) ∂P = ∫ u in (s : ℝ)..r, g u := by
      have hF : Measurable fun p : Path d × ℝ => Z p.1 * f (p.1 p.2.toNNReal) :=
        (hZm.comp measurable_fst).mul (hfc.measurable.comp (continuous_pathEval d).measurable)
      have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (s : ℝ) r)) := by
        constructor
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
      have hint : Integrable (fun p : Path d × ℝ => Z p.1 * f (p.1 p.2.toNNReal))
          (P.prod (volume.restrict (Set.Ioc (s : ℝ) r))) :=
        Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs]; exact hZf _ _)
      simp only [g]
      rw [intervalIntegral.integral_of_le hr]
      simp_rw [intervalIntegral.integral_of_le hr]
      exact integral_integral_swap hint
    have hMZ : ∀ u, Integrable (fun γ => Z γ * compensatedTest (reducedGenerator i ω 0) f u γ) P :=
      fun u => (hMi u).bdd_mul (c := C) hZm.aestronglyMeasurable
        (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hC γ)
    have h0 : ∫ γ, (Z γ * compensatedTest (reducedGenerator i ω 0) f r.toNNReal γ -
        Z γ * compensatedTest (reducedGenerator i ω 0) f s γ) ∂P = 0 := by
      rw [integral_sub (hMZ _) (hMZ _), hm, sub_self]
    simp_rw [hdiff] at h0
    have hb2 : Integrable (fun γ => Z γ * f (γ r.toNNReal) - Z γ * f (γ s)) P :=
      (hb _).sub (hb _)
    have hb3 : Integrable (fun γ => κ * ∫ u in (s : ℝ)..r, Z γ * f (γ u.toNNReal)) P :=
      hIint.const_mul κ
    rw [integral_add hb2 hb3, integral_sub (hb _) (hb _), integral_const_mul, hfub] at h0
    have hgs : g s = ∫ γ, Z γ * f (γ s) ∂P := by simp only [g, Real.toNNReal_coe]
    rw [hgs]
    simp only [g] at h0 ⊢
    linarith
  have hfin := eq_exp_mul_of_integral_eq hgc hid t (by exact_mod_cast hst)
  simp only [g, Real.toNNReal_coe] at hfin
  exact hfin

end Evolution

end EinsteinFull.Blueprint
