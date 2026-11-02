import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.K11GMPRealizationFields
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import MarkovProcess.Path.OptionalStopping
import MarkovProcess.Trajectory.StoppingLtTop
import EinsteinFull.Calculus.C2SourceWeightedDynkin
import SubdiffusiveProcess.Section10.TorsionExitDynkinExpectation
import SubdiffusiveProcess.Processes.FellerRealizationRestart

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- The selected regular signed physical realization restarts at every finite
canonical stopping time. -/
theorem u5_regular_signed_realization_stopping_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0))) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      ((K x).restrict A).map (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) =
        Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((K x).restrict A) := by
  exact MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift_stoppingTime
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
    ⟨fun _ => 0, continuous_const⟩ K hfdd x T hT

/-- Discounted occupation under the supplied path law is the actual regular resolvent. -/
theorem u5_regular_signed_path_laplace_aux
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    (∫ γ : Path d, (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) =
      u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g x := by
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have hm (t : ℝ) : (∫ γ : Path d, g (γ t.toNNReal) ∂K x) = S t.toNNReal g x := by
    change (∫ γ : Path d, g (pathPosition t.toNNReal γ) ∂K x) = _
    have hmap := integral_map (μ := K x) (measurable_pathPosition t.toNNReal).aemeasurable
      (f := fun y => g y) g.continuous.aestronglyMeasurable
    rw [← hmap]
    change (∫ y, g y ∂(K x).map (pathPosition t.toNNReal)) = _
    rw [Blueprint.k11_endpoint (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
      K hfdd t.toNNReal x]
    exact u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω _ g x
  have heval : Continuous (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))
  have hi : Integrable (fun z : ℝ × Path d => Real.exp (-s * z.1) *
      g (z.2 z.1.toNNReal)) ((volume.restrict (Set.Ioi 0)).prod (K x)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖g‖).comp_fst
      (K x)).mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (g.continuous.comp heval)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖Real.exp (-s * z.1) * g (z.2 z.1.toNNReal)‖ ≤ Real.exp (-s * z.1) * ‖g‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
        (Real.exp_nonneg _)
  have hev : (fun t : ℝ => Real.exp (-s * t) *
      (∫ γ : Path d, g (γ t.toNNReal) ∂K x)) =
      fun t => ev (S.laplaceIntegrand s g t) := by
    funext t
    simp [hm, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev]
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
        (∫ γ : Path d, g (γ t.toNNReal) ∂K x) := by
      rw [← integral_integral_swap hi]
      simp only [integral_const_mul]
    _ = ev (∫ t in Set.Ioi 0, S.laplaceIntegrand s g t) := by
      rw [hev]
      simpa only [Function.comp_def] using (ev.integral_comp_comm (S.integrableOn_laplaceIntegrand hs g))
    _ = ev (S.resolvent ⟨s, hs⟩ g) := by rw [S.resolvent_apply]
    _ = _ := by rw [show S.resolvent ⟨s, hs⟩ = _ from
      u2_regular_c0_semigroup_resolvent hd ω lam Λ hΛ hω ⟨s, hs⟩]; rfl

#print axioms u5_regular_signed_path_laplace_aux

/-- Discounted occupation after a finite stopping time is the resolvent at the stopping position. -/
theorem u5_regular_signed_stopped_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∫ γ in A, (∫ t : ℝ in Set.Ioi 0,
        Real.exp (-s * t) * g (γ (T γ + t.toNNReal))) ∂K x) =
      ∫ γ in A, u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g (γ (T γ)) ∂K x := by
  intro A hA
  have hrestart := u5_regular_signed_realization_stopping_restart
    hd ω lam Λ hΛ hω K hfdd x T hT A hA
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hfn (y : Vec d) : ‖g y‖ ≤ ‖g‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-s * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0
  have hexp : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) := hE.const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hexp (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hfn _) (Real.exp_nonneg _)
  have hΦi (μ : Measure (Path d)) [IsFiniteMeasure μ] : Integrable Φ μ :=
    Integrable.of_bound hΦm.aestronglyMeasurable _ (ae_of_all _ hbd)
  have hswap (y : Vec d) :
      (∫ η, Φ η ∂K y) = u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g y :=
    u5_regular_signed_path_laplace_aux hd ω lam Λ hΛ hω K hfdd y s hs g
  have hshift := MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT
  calc
    _ = ∫ η, Φ η ∂((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) := by
      rw [integral_map hshift.aemeasurable hΦm.aestronglyMeasurable]
      rfl
    _ = ∫ η, Φ η ∂(Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((K x).restrict A)) := by rw [hrestart]
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
      · simp only [Kernel.const_apply, Kernel.comap_apply, hswap]
      · exact hΦi _

#print axioms u5_regular_signed_stopped_path_laplace

#print axioms u5_regular_signed_realization_stopping_restart

/-- Compact-test compensated observables are integrable under any finite path law. -/
theorem u5_regular_compensated_test_integrable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (P : Measure (Path d)) [IsFiniteMeasure P]
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (T : ℝ≥0) :
    Integrable (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T) P := by
  let fB := EinsteinFull.Work.W5.gantertCompactObservable f hf.continuous hc
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have ha := stronglyAdapted_compensatedTest_of_measurable
    (physicalGenerator (firstCoordinateIndex hd) ω lam) f hf.continuous
    (measurable_physicalGenerator _ ω lam f)
  apply Integrable.of_bound ((ha T).mono ((pathFiltration d).le T)).aestronglyMeasurable
    (2 * ‖fB‖ + B * T)
  exact ae_of_all _ fun γ => abs_compensatedTest_le
    (L := physicalGenerator (firstCoordinateIndex hd) ω lam)
    (fun y => fB.norm_coe_le_norm y) hB T γ

#print axioms u5_regular_compensated_test_integrable

/-- A shifted evolution identity extends to time zero by continuity. -/
theorem u5_shifted_evolution_at_zero (F : ℝ≥0 → ℝ) (H : ℝ → ℝ)
    (hcont : Continuous F)
    (hprim : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..r, H s)) (t : ℝ≥0)
    (he : ∀ r : ℝ≥0, 0 < r → F (r + t) - F r =
      (∫ s in (0 : ℝ)..((r : ℝ) + t), H s) - ∫ s in (0 : ℝ)..(r : ℝ), H s) :
    F t - F 0 = ∫ s in (0 : ℝ)..(t : ℝ), H s := by
  have hr : Tendsto (fun r : ℝ≥0 => r) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft := ((hcont.tendsto t).comp (by simpa using hr.add_const t)).sub
    ((hcont.tendsto 0).comp hr)
  have hrR : Tendsto (fun r : ℝ≥0 => (r : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hr
  have hright := ((hprim.tendsto (t : ℝ)).comp (by simpa using hrR.add_const (t : ℝ))).sub
    ((hprim.tendsto 0).comp hrR)
  apply tendsto_nhds_unique hleft
  have hright' : Tendsto (fun r : ℝ≥0 =>
      (∫ s in (0 : ℝ)..((r : ℝ) + t), H s) - ∫ s in (0 : ℝ)..(r : ℝ), H s)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), H s)) := by
    simpa only [Function.comp_def, intervalIntegral.integral_same, sub_zero] using hright
  apply hright'.congr'
  filter_upwards [eventually_mem_nhdsWithin] with r hr
  exact (he r hr).symm

/-- Compact-test kernel orbits are continuous in time at each start. -/
theorem u5_regular_kernel_compactTest_orbit_continuous
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) (x : Vec d) :
    Continuous (fun r : ℝ≥0 => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) := by
  let F := Blueprint.gmpPhysicalCompactC0 f hf hc
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  have h := ev.continuous.comp ((u2RegularC0Semigroup hd ω lam Λ hΛ hω).continuous_orbit F)
  have heq : (fun r : ℝ≥0 => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) =
      fun r => ev (u2RegularC0Semigroup hd ω lam Λ hΛ hω r F) := by
    funext r
    exact u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω r F x
  rw [heq]
  exact h

#print axioms u5_shifted_evolution_at_zero
#print axioms u5_regular_kernel_compactTest_orbit_continuous

/-- Rewrite a shifted orbit integral in terms of its primitive. -/
theorem u5_shifted_orbit_primitive (G : ℝ≥0 → ℝ) (H : ℝ → ℝ)
    (hH : ∀ s : ℝ, H s = G s.toNNReal)
    (hm : Measurable H) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ s, ‖H s‖ ≤ B)
    (r t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), G (r + s.toNNReal)) =
      (∫ s in (0 : ℝ)..((r : ℝ) + t), H s) - ∫ s in (0 : ℝ)..(r : ℝ), H s := by
  rw [← u2_bounded_orbit_primitive_shift H hm B hB hb]
  apply intervalIntegral.integral_congr
  intro s hs
  change G (r + s.toNNReal) = H (s + r)
  rw [hH]
  have hs0 : 0 ≤ s := (Set.uIcc_of_le t.coe_nonneg ▸ hs).1
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal _ hs0,
    Real.coe_toNNReal _ (add_nonneg hs0 r.coe_nonneg)]
  exact add_comm _ _


/-- Shifting a compensated test gives its increment. -/
theorem u5_compensatedTest_shift {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hL : ∀ γ : Path d, ∀ a b : ℝ,
      IntervalIntegrable (fun u => L f (γ u.toNNReal)) volume a b) (s t : ℝ≥0) (γ : Path d) :
    compensatedTest L f t (gmpShiftPath s γ) =
      compensatedTest L f (s + t) γ - compensatedTest L f s γ := by
  let g : ℝ → ℝ := fun u => L f (γ u.toNNReal)
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := hL γ a b
  have hshift : (∫ u in (0 : ℝ)..(t : ℝ), L f (gmpShiftPath s γ u.toNNReal)) =
      ∫ u in (s : ℝ)..((s : ℝ) + t), g u := by
    calc
      _ = ∫ u in (0 : ℝ)..(t : ℝ), g (u + s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : 0 ≤ u := (Set.uIcc_of_le t.coe_nonneg ▸ hu).1
        change L f (γ (s + u.toNNReal)) = L f (γ (u + s).toNNReal)
        congr 2
        apply NNReal.eq
        simp only [NNReal.coe_add, Real.coe_toNNReal _ hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        exact add_comm _ _
      _ = _ := by
        simpa only [zero_add, add_comm (t : ℝ) (s : ℝ)] using
          intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (t : ℝ)) g (s : ℝ)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg 0 s)
    (hg s (s + t))
  simp only [compensatedTest, gmpShiftPath, ContinuousMap.coe_mk, add_zero,
    NNReal.coe_add] at hshift ⊢
  rw [hshift]
  dsimp [g] at hadd
  linarith



#print axioms u5_shifted_orbit_primitive
#print axioms u5_compensatedTest_shift

/-- A bounded measurable observable has integrable path occupation and its
expected occupation equals the integral of the transition orbit. -/
theorem u5_regular_path_occupation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B)
    (x : Vec d) (T : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) (K x) ∧
    (∫ γ, (∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) ∂K x) =
      ∫ u in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω u.toNNReal x := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun p => g (p.1 p.2.toNNReal)
  have hH : Measurable H := by
    apply hg.comp
    exact continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hint : Integrable H ((K x).prod ν) :=
    Integrable.of_bound hH.aestronglyMeasurable B (ae_of_all _ fun p => hB _)
  constructor
  · simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using hint.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
    calc
      _ = ∫ u, ∫ γ, H (γ, u) ∂K x ∂ν := integral_integral_swap hint
      _ = _ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by
          change (∫ γ, g (γ u.toNNReal) ∂K x) =
            ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω u.toNNReal x
          rw [← Blueprint.k11_endpoint _ K hfdd u.toNNReal x]
          exact (integral_map (measurable_pathPosition u.toNNReal).aemeasurable
            hg.aestronglyMeasurable).symm

#print axioms u5_regular_path_occupation


/-- At positive times the signed transition is absolutely continuous with respect
    to the physical reversible measure. -/
theorem u5_regular_signed_kernel_ac_reversible
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (r : ℝ≥0) (hr : 0 < r) (x : Vec d) :
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x ≪
      physicalReversibleMeasure ω hd lam := by
  have hvμ : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd lam := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro Q hQ
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam Q).mp hQ
  exact (u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω r hr x).trans hvμ

#print axioms u5_regular_signed_kernel_ac_reversible

/-- Compact-test shifted Dynkin identity at every start and positive shift. -/
theorem u5_regular_kernel_compactTest_dynkin_positive_shift
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (r t : ℝ≥0) (hr : 0 < r) (x : Vec d) :
    (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + t) x) -
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) =
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + s.toNNReal) x :=
  u2_regular_kernel_compactTest_dynkin_shifted hd ω lam Λ hΛ hω f hf hc r t x
    (u5_regular_signed_kernel_ac_reversible hd ω lam Λ hΛ hω r hr x)

#print axioms u5_regular_kernel_compactTest_dynkin_positive_shift

/-- The generator orbit is measurable and bounded at each fixed start. -/
theorem u5_regular_generator_orbit_fixed_start
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) :
    ∃ B : ℝ, 0 ≤ B ∧
      Measurable (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s.toNNReal x) ∧
      ∀ s : ℝ, ‖∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s.toNNReal x‖ ≤ B := by
  obtain ⟨B, hB, hm, hb⟩ :=
    u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω f hf hc
  refine ⟨B, hB, ?_, ?_⟩
  · have hm' := hm.comp (measurable_id.prodMk
      (measurable_const : Measurable (fun _ : ℝ => x)))
    simpa only [Function.comp_def, id_eq] using hm'
  · intro s
    simpa only [Real.norm_eq_abs] using hb s.toNNReal x

#print axioms u5_regular_generator_orbit_fixed_start

/-- The signed generator orbit has the standard shifted primitive identity. -/
theorem u5_regular_generator_orbit_shift
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (r t : ℝ≥0) (x : Vec d) :
    (∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + s.toNNReal) x) =
    (∫ s in (0 : ℝ)..((r : ℝ) + t), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s.toNNReal x) -
    ∫ s in (0 : ℝ)..(r : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s.toNNReal x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let G : ℝ≥0 → ℝ := fun s => ∫ y,
    physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂P s x
  let H : ℝ → ℝ := fun s => G s.toNNReal
  obtain ⟨B, hB, hHm, hHb⟩ :=
    u5_regular_generator_orbit_fixed_start hd ω lam Λ hΛ hω f hf hc x
  exact u5_shifted_orbit_primitive G H (fun _ => rfl) hHm B hB hHb r t

#print axioms u5_regular_generator_orbit_shift

/-- The signed kernel satisfies Dynkin's identity at every start. -/
theorem u5_regular_kernel_compactTest_dynkin_every_start
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (t : ℝ≥0) (x : Vec d) :
    (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - f x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s.toNNReal x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let H : ℝ → ℝ := fun s => ∫ y,
    physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂P s.toNNReal x
  have hprim : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..r, H s) :=
    u2_regular_generator_orbit_primitive_continuous hd ω lam Λ hΛ hω f hf hc x
  have hcont : Continuous (fun r : ℝ≥0 => ∫ y, f y ∂P r x) :=
    u5_regular_kernel_compactTest_orbit_continuous hd ω lam Λ hΛ hω f hf.continuous hc x
  have he (r : ℝ≥0) (hr : 0 < r) :
      (∫ y, f y ∂P (r + t) x) - (∫ y, f y ∂P r x) =
        (∫ s in (0 : ℝ)..((r : ℝ) + t), H s) - ∫ s in (0 : ℝ)..(r : ℝ), H s :=
    (u5_regular_kernel_compactTest_dynkin_positive_shift hd ω lam Λ hΛ hω f hf hc r t hr x).trans
      (u5_regular_generator_orbit_shift hd ω lam Λ hΛ hω f hf hc r t x)
  have hz : (∫ y, f y ∂P 0 x) = f x := by
    rw [P.kernel_zero, Kernel.id_apply, integral_dirac]
  simpa only [hz] using u5_shifted_evolution_at_zero
    (fun r => ∫ y, f y ∂P r x) H hcont hprim t he

#print axioms u5_regular_kernel_compactTest_dynkin_every_start

/-- The compact-test compensated observable has zero mean at every start. -/
theorem u5_regular_compensated_test_mean_zero
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) (T : ℝ≥0) :
    (∫ γ, compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T γ ∂K x) = 0 := by
  let fB := EinsteinFull.Work.W5.gantertCompactObservable f hf.continuous hc
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  have hg : Measurable g := measurable_physicalGenerator _ ω lam f
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have hBn : ∀ y, ‖g y‖ ≤ B := hB
  have hi (t : ℝ≥0) : Integrable (fun γ : Path d => f (γ t)) (K x) :=
    Integrable.of_bound (hf.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
      ‖fB‖ (ae_of_all _ fun γ => fB.norm_coe_le_norm (γ t))
  have he (t : ℝ≥0) : (∫ γ, f (γ t) ∂K x) =
      ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
    rw [← Blueprint.k11_endpoint _ K hfdd t x]
    exact (integral_map (measurable_pathPosition t).aemeasurable
      hf.continuous.aestronglyMeasurable).symm
  obtain ⟨hgi, hge⟩ := u5_regular_path_occupation hd ω lam Λ hΛ hω K hfdd g hg B hBn x T
  change (∫ γ, (f (γ T) - f (γ 0)) -
    (∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) ∂K x) = _
  have hisub : Integrable (fun γ : Path d => f (γ T) - f (γ 0)) (K x) :=
    (hi T).sub (hi 0)
  rw [integral_sub hisub hgi, integral_sub (hi T) (hi 0), he T, he 0, hge,
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).kernel_zero, Kernel.id_apply, integral_dirac]
  exact sub_eq_zero.mpr (u5_regular_kernel_compactTest_dynkin_every_start hd ω lam Λ hΛ hω f hf hc T x)

#print axioms u5_regular_compensated_test_mean_zero

/-- Restarting at a fixed time conditions the future on the current position. -/
theorem u5_regular_integral_shift_on_past
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ≥0) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E)
    (F : Path d → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ γ, ‖F γ‖ ≤ B) :
    (∫ γ in E, F (gmpShiftPath s γ) ∂K x) =
      ∫ γ in E, ∫ η, F η ∂K (γ s) ∂K x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := (K x).restrict E
  let Q := Kernel.comap K (pathPosition s) (measurable_pathPosition s)
  have hEc : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] E := by
    rw [← pathFiltration_eq_canonical]
    exact hE
  have hs : MarkovProcess.ContinuousPath.shift s = gmpShiftPath (d := d) s := by
    funext γ
    ext t
    rfl
  have hr : μ.map (gmpShiftPath s) = Q ∘ₘ μ := by
    rw [← hs]
    exact MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift
      P (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
      (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
      ⟨fun _ => 0, continuous_const⟩ K hfdd x s E hEc
  have hi : Integrable F (Q ∘ₘ μ) :=
    (integrable_const B).mono' hF.aestronglyMeasurable (ae_of_all _ hB)
  have hm := integral_map (μ := μ) (measurable_gmpShiftPath s).aemeasurable
    hF.aestronglyMeasurable
  rw [hr] at hm
  rw [Measure.comp_eq_comp_const_apply] at hm hi
  rw [Kernel.integral_comp hi] at hm
  simpa only [μ, Q, Kernel.comap_apply, Kernel.const_apply, pathPosition] using hm.symm

#print axioms u5_regular_integral_shift_on_past

/-- Any supplied continuous-path realization with these finite-dimensional laws
solves the physical martingale problem, for every real force. -/
theorem u5_regular_same_FDD_physical_MP_all_real
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ x : Vec d, SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) ω lam) x (K x) := by
  intro x
  refine ⟨inferInstance, Blueprint.k11_starts_at _ K hfdd x, ?_⟩
  intro f hf hc
  let L := physicalGenerator (firstCoordinateIndex hd) ω lam
  have hL : Measurable (L f) := measurable_physicalGenerator _ ω lam f
  have hLi (γ : Path d) (a b : ℝ) :
      IntervalIntegrable (fun u => L f (γ u.toNNReal)) volume a b :=
    sbxS4_intervalIntegrable_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc γ a b
  have hi := u5_regular_compensated_test_integrable hd ω lam Λ hΛ hω (K x) f hf hc
  have ha := stronglyAdapted_compensatedTest_of_measurable L f hf.continuous hL
  refine ⟨fun t => ae_of_all _ fun γ => hLi γ 0 t, hi, ha, ?_⟩
  intro s u hsu
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (pathFiltration d |>.le s) (hi u)
  · intro E hE hfinite
    exact (hi s).integrableOn
  · intro E hE hfinite
    have hF : Measurable (compensatedTest L f (u - s)) :=
      ((ha (u - s)).mono ((pathFiltration d).le (u - s))).measurable
    let fB := EinsteinFull.Work.W5.gantertCompactObservable f hf.continuous hc
    obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
    have hbound (γ : Path d) :
        ‖compensatedTest L f (u - s) γ‖ ≤ 2 * ‖fB‖ + B * ((u - s : ℝ≥0) : ℝ) :=
      abs_compensatedTest_le (L := L) (φ := f) (fun y => fB.norm_coe_le_norm y)
        hB (u - s) γ
    have he := u5_regular_integral_shift_on_past hd ω lam Λ hΛ hω K hfdd x s E hE
      (compensatedTest L f (u - s)) hF _ hbound
    simp_rw [u5_compensatedTest_shift L f hLi s (u - s), add_tsub_cancel_of_le hsu] at he
    have hz (y : Vec d) : (∫ γ, compensatedTest L f (u - s) γ ∂K y) = 0 :=
      u5_regular_compensated_test_mean_zero hd ω lam Λ hΛ hω K hfdd f hf hc y (u - s)
    simp_rw [hz] at he
    rw [integral_zero, integral_sub (hi u).integrableOn (hi s).integrableOn] at he
    exact (sub_eq_zero.mp he).symm
  · exact (ha s).aestronglyMeasurable

#print axioms u5_regular_same_FDD_physical_MP_all_real

/-- The resolvent compensated observable has zero mean from every start. -/
theorem u5_regular_resolvent_compensated_mean_zero
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (t : ℝ≥0) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    (∫ γ, compensatedTest (fun _ y => s * R y - g y) R t γ ∂K x) = 0 := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let hF := u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω
  let S := hF.c0Semigroup
  have hS : S = u2RegularC0Semigroup hd ω lam Λ hΛ hω :=
    u2RegularC0KernelSemigroup_c0Semigroup hd ω lam Λ hΛ hω
  have hR : S.resolvent ⟨s, hs⟩ g = u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g := by
    rw [hS, u2_regular_c0_semigroup_resolvent]
  let f : S.generatorDomain := ⟨S.resolvent ⟨s, hs⟩ g, S.resolvent_mem_generatorDomain ⟨s, hs⟩ g⟩
  have hgen : S.generator f = s • (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) - g := by
    dsimp [f]
    rw [S.generator_resolvent, hR]
  have h := SubdiffusiveProcess.Section10.integral_eval_sub_eq_integral_integral_generator_realization
    P (u2_regular_kernel_conservative hd ω lam Λ hΛ hω) hF K hfdd f t x
  rw [hgen] at h
  have hi (u : ℝ≥0) : Integrable (fun γ : Path d => (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ u)) (K x) :=
    Integrable.of_bound (((u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g).continuous).comp
      (continuous_eval_const u)).aestronglyMeasurable _
      (ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm
        (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g).toBCF (γ u))
  have he : (∫ γ, (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ 0) ∂K x) =
      (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) x := by
    have hm := integral_map (μ := K x) (measurable_pathPosition 0).aemeasurable
      (f := fun y => (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) y)
      (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g).continuous.aestronglyMeasurable
    rw [Blueprint.k11_endpoint P K hfdd 0 x, P.kernel_zero, Kernel.id_apply, integral_dirac] at hm
    exact hm.symm
  let q : ZeroAtInftyContinuousMap (Vec d) ℝ := s • (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) - g
  have hqi := (u5_regular_path_occupation hd ω lam Λ hΛ hω K hfdd q q.continuous.measurable ‖q‖
    (fun y => BoundedContinuousFunction.norm_coe_le_norm q.toBCF y) x t).1
  change (∫ γ, ((u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ t) -
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ 0)) -
    (∫ u in (0 : ℝ)..(t : ℝ), q (γ u.toNNReal)) ∂K x) = 0
  have hsub := integral_sub ((hi t).sub (hi 0)) hqi
  change (∫ γ, ((u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ t) -
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g) (γ 0)) -
    (∫ u in (0 : ℝ)..(t : ℝ), q (γ u.toNNReal)) ∂K x) = _ at hsub
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [integral_sub (hi t) (hi 0), he]
  apply sub_eq_zero.mpr
  simpa only [f, hR, ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, q] using h

#print axioms u5_regular_resolvent_compensated_mean_zero

/-- The actual C₀ resolvent has the martingale increment identity on every past event. -/
theorem u5_regular_signed_resolvent_martingale_events
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    ∀ (a b : ℝ≥0), a ≤ b → ∀ A : Set (Path d),
      MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d) a] A →
      (∫ γ in A, (R (γ b) - R (γ a) -
        ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ),
          (s * R (γ u.toNNReal) - g (γ u.toNNReal))) ∂K x) = 0 := by
  dsimp only
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let q : ZeroAtInftyContinuousMap (Vec d) ℝ := s • R - g
  let L : (Vec d → ℝ) → Vec d → ℝ := fun _ => q
  intro a b hab A hA
  have hLi (γ : Path d) (c e : ℝ) :
      IntervalIntegrable (fun u => L R (γ u.toNNReal)) volume c e :=
    (q.continuous.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable c e
  have ha := stronglyAdapted_compensatedTest_of_measurable L R R.continuous q.continuous.measurable
  have hF : Measurable (compensatedTest L R (b - a)) :=
    ((ha (b - a)).mono ((pathFiltration d).le (b - a))).measurable
  have hbound (γ : Path d) :
      ‖compensatedTest L R (b - a) γ‖ ≤ 2 * ‖R‖ + ‖q‖ * ((b - a : ℝ≥0) : ℝ) :=
    abs_compensatedTest_le (L := L) (φ := R)
      (fun y => BoundedContinuousFunction.norm_coe_le_norm R.toBCF y)
      (fun y => BoundedContinuousFunction.norm_coe_le_norm q.toBCF y) (b - a) γ
  have hA' : MeasurableSet[pathFiltration d a] A := by
    rw [pathFiltration_eq_canonical]
    exact hA
  have he := u5_regular_integral_shift_on_past hd ω lam Λ hΛ hω K hfdd x a A hA'
    (compensatedTest L R (b - a)) hF _ hbound
  have hz (y : Vec d) : (∫ γ, compensatedTest L R (b - a) γ ∂K y) = 0 :=
    u5_regular_resolvent_compensated_mean_zero hd ω lam Λ hΛ hω K hfdd y s hs g (b - a)
  simp_rw [hz, integral_zero] at he
  simp_rw [u5_compensatedTest_shift L R hLi a (b - a), add_tsub_cancel_of_le hab] at he
  have hadd (γ : Path d) := intervalIntegral.integral_add_adjacent_intervals
    (hLi γ 0 a) (hLi γ a b)
  have heq (γ : Path d) : compensatedTest L R b γ - compensatedTest L R a γ =
      R (γ b) - R (γ a) - ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ),
        (s * R (γ u.toNNReal) - g (γ u.toNNReal)) := by
    rw [← intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from NNReal.coe_le_coe.mpr hab)]
    simp only [compensatedTest, L, q, ZeroAtInftyContinuousMap.coe_sub,
      ZeroAtInftyContinuousMap.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hadd ⊢
    linarith [hadd γ]
  simpa only [heq] using he

#print axioms u5_regular_signed_resolvent_martingale_events


/-- The resolvent compensated increment has zero mean after any finite stopping time. -/
theorem u5_regular_signed_stopped_resolvent_martingale_events
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0))) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    ∀ (b : ℝ≥0) (A : Set (Path d)), MeasurableSet[hT.measurableSpace] A →
      (∫ γ in A, (R (γ (T γ + b)) - R (γ (T γ)) -
        ∫ u : ℝ in Set.Ioc (0 : ℝ) (b : ℝ),
          (s * R (γ (T γ + u.toNNReal)) - g (γ (T γ + u.toNNReal)))) ∂K x) = 0 := by
  dsimp only
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let q : ZeroAtInftyContinuousMap (Vec d) ℝ := s • R - g
  let L : (Vec d → ℝ) → Vec d → ℝ := fun _ => q
  intro b A hA
  let Φ := compensatedTest L R b
  have ha := stronglyAdapted_compensatedTest_of_measurable L R R.continuous q.continuous.measurable
  have hΦm : Measurable Φ := ((ha b).mono ((pathFiltration d).le b)).measurable
  have hbound (γ : Path d) : ‖Φ γ‖ ≤ 2 * ‖R‖ + ‖q‖ * (b : ℝ) :=
    abs_compensatedTest_le (L := L) (φ := R)
      (fun y => BoundedContinuousFunction.norm_coe_le_norm R.toBCF y)
      (fun y => BoundedContinuousFunction.norm_coe_le_norm q.toBCF y) b γ
  have hΦi (μ : Measure (Path d)) [IsFiniteMeasure μ] : Integrable Φ μ :=
    Integrable.of_bound hΦm.aestronglyMeasurable _ (ae_of_all _ hbound)
  have hz (y : Vec d) : (∫ γ, Φ γ ∂K y) = 0 :=
    u5_regular_resolvent_compensated_mean_zero hd ω lam Λ hΛ hω K hfdd y s hs g b
  have hrestart := u5_regular_signed_realization_stopping_restart
    hd ω lam Λ hΛ hω K hfdd x T hT A hA
  have hshift := MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT
  have he : (∫ γ in A, Φ (MarkovProcess.ContinuousPath.shift (T γ) γ) ∂K x) = 0 := by
    rw [← integral_map hshift.aemeasurable hΦm.aestronglyMeasurable, hrestart,
      Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hΦi _)]
    simp only [Kernel.const_apply, Kernel.comap_apply, hz, integral_zero]
  convert he using 1
  apply integral_congr_ae
  filter_upwards with γ
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (b : ℝ) from NNReal.coe_nonneg b)]
  simp only [Φ, compensatedTest, L, q, ZeroAtInftyContinuousMap.coe_sub,
    ZeroAtInftyContinuousMap.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    MarkovProcess.ContinuousPath.shift_apply, add_zero]
  rfl

#print axioms u5_regular_signed_stopped_resolvent_martingale_events

/-- Compact-test physical compensated paths are continuous and uniformly bounded
on each bounded time interval. -/
theorem u5_regular_physical_compensated_continuous_bounded
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (H : ℝ≥0) :
    (∀ γ : Path d, Continuous (fun t : ℝ≥0 =>
      compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f t γ)) ∧
    ∃ C : ℝ, ∀ (t : ℝ≥0), t ≤ H → ∀ γ : Path d,
      ‖compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f t γ‖ ≤ C := by
  let L := physicalGenerator (firstCoordinateIndex hd) ω lam
  let fB := EinsteinFull.Work.W5.gantertCompactObservable f hf.continuous hc
  obtain ⟨B, hB0, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  constructor
  · intro γ
    exact continuous_compensatedTest_time_of_bounded L f hf.continuous
      (measurable_physicalGenerator _ ω lam f) (fun y => by simpa only [Real.norm_eq_abs] using hB y) γ
  · refine ⟨2 * ‖fB‖ + B * (H : ℝ), fun t ht γ => ?_⟩
    exact (abs_compensatedTest_le (L := L) (φ := f)
      (fun y => fB.norm_coe_le_norm y) hB t γ).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht) hB0) _)

#print axioms u5_regular_physical_compensated_continuous_bounded

/-- The physical compensated observable has zero mean at every bounded finite
canonical stopping time. -/
theorem u5_regular_physical_compensated_stopping_mean_zero
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (H : ℝ≥0) (hTH : ∀ γ, T γ ≤ H) :
    (∫ γ, compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f (T γ) γ ∂K x) = 0 := by
  have hM := (u5_regular_same_FDD_physical_MP_all_real hd ω lam Λ hΛ hω K hfdd x).2.2 f hf hc
  have hcont := u5_regular_physical_compensated_continuous_bounded hd ω lam Λ hΛ hω f hf hc
  have hm : Martingale (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x) := by
    rw [← pathFiltration_eq_canonical]
    exact hM.2.2
  have he := MarkovProcess.integral_stoppedValue_eq_of_locallyBounded hm
    (fun v => (hcont v).2) (fun γ v => ((hcont v).1 γ).continuousWithinAt) hT hTH
  simpa only [compensatedTest, NNReal.coe_zero, intervalIntegral.integral_same, sub_self, sub_zero, integral_zero] using he

#print axioms u5_regular_physical_compensated_stopping_mean_zero

/-- Optional sampling of the actual physical compensated martingale on a
canonical stopping-time event. -/
theorem u5_regular_signed_physical_optional_sampling
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (T S : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (hS : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (S γ : WithTop ℝ≥0)))
    (H : ℝ≥0) (hTS : ∀ γ, T γ ≤ S γ) (hSH : ∀ γ, S γ ≤ H) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∫ γ in A, (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f (S γ) γ -
        compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f (T γ) γ) ∂K x) = 0 := by
  classical
  intro A hA
  let U : Path d → ℝ≥0 := fun γ => if γ ∈ A then S γ else T γ
  have hU : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (U γ : WithTop ℝ≥0)) := by
    intro t
    have ha := ((hT.measurableSet A).mp hA).2 t
    have hac := ((hT.measurableSet Aᶜ).mp hA.compl).2 t
    have hs := hS t
    have heq : {γ | (U γ : WithTop ℝ≥0) ≤ t} =
        (A ∩ {γ | (T γ : WithTop ℝ≥0) ≤ t} ∩
          {γ | (S γ : WithTop ℝ≥0) ≤ t}) ∪
        (Aᶜ ∩ {γ | (T γ : WithTop ℝ≥0) ≤ t}) := by
      ext γ
      by_cases hγ : γ ∈ A
      · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff, hγ, not_true_eq_false, false_and, or_false, true_and,
          U]
        exact ⟨fun hs => ⟨(WithTop.coe_le_coe.mpr (hTS γ)).trans hs, hs⟩, And.right⟩
      · simp [U, hγ]
    rw [heq]
    exact (ha.inter hs).union hac
  have hUH (γ : Path d) : U γ ≤ H := by
    dsimp [U]
    split_ifs with hγ
    · exact hSH γ
    · exact (hTS γ).trans (hSH γ)
  let L := physicalGenerator (firstCoordinateIndex hd) ω lam
  let M := compensatedTest L f
  have hbound := (u5_regular_physical_compensated_continuous_bounded hd ω lam Λ hΛ hω f hf hc H).2
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have hLm : Measurable (L f) := measurable_physicalGenerator _ ω lam f
  have hjoint := c2_compensatedTest_joint_measurable hf.continuous.measurable hLm
    (fun y => by simpa only [Real.norm_eq_abs] using hB y)
  have hi (V : Path d → ℝ≥0)
      (hV : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
        (fun γ => (V γ : WithTop ℝ≥0))) (hVH : ∀ γ, V γ ≤ H) :
      Integrable (fun γ => M (V γ) γ) (K x) := by
    have hVm := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime V hV
    have hj := hjoint.comp ((NNReal.continuous_coe.measurable.comp hVm).prodMk measurable_id)
    have hj' : Measurable (fun γ => M (V γ) γ) := by
      simpa [M, Function.comp_def] using hj
    apply Integrable.of_bound hj'.aestronglyMeasurable C
    exact ae_of_all _ (fun γ => hC (V γ) (hVH γ) γ)
  have hTi := hi T hT (fun γ => (hTS γ).trans (hSH γ))
  have hSi := hi S hS hSH
  have hAm : MeasurableSet A := hT.measurableSpace_le A hA
  have hUzero := u5_regular_physical_compensated_stopping_mean_zero hd ω lam Λ hΛ hω K hfdd x f hf hc U hU H hUH
  have hTzero := u5_regular_physical_compensated_stopping_mean_zero hd ω lam Λ hΛ hω K hfdd x f hf hc T hT H (fun γ => (hTS γ).trans (hSH γ))
  have heq : (fun γ => M (U γ) γ) =
      fun γ => A.indicator (fun γ => M (S γ) γ - M (T γ) γ) γ + M (T γ) γ := by
    funext γ
    by_cases hγ : γ ∈ A <;> simp [U, hγ, Set.indicator_of_mem, Set.indicator_of_notMem]
  change (∫ γ, M (U γ) γ ∂K x) = 0 at hUzero
  change (∫ γ, M (T γ) γ ∂K x) = 0 at hTzero
  have hdiff : Integrable (fun γ => M (S γ) γ - M (T γ) γ) (K x) := hSi.sub hTi
  have hadd := integral_add (hdiff.indicator hAm) hTi
  change (∫ γ, A.indicator (fun γ => M (S γ) γ - M (T γ) γ) γ + M (T γ) γ ∂K x) = _ at hadd
  rw [heq, hadd, hTzero, add_zero, integral_indicator hAm] at hUzero
  exact hUzero

#print axioms u5_regular_signed_physical_optional_sampling

/-- Equality of integrals on a sub-sigma-algebra persists after multiplication
by an integrable measurable weight. -/
theorem u5_integral_mul_of_setIntegral_eq {α : Type*} [m₀ : MeasurableSpace α] {m : MeasurableSpace α}
    {μ : Measure[m₀] α} [IsFiniteMeasure μ] (hm : m ≤ m₀)
    {f g w : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : StronglyMeasurable[m] w) (hwf : Integrable (w * f) μ)
    (hwg : Integrable (w * g) μ)
    (he : ∀ A : Set α, MeasurableSet[m] A → ∫ x in A, f x ∂μ = ∫ x in A, g x ∂μ) :
    (∫ x, w x * f x ∂μ) = ∫ x, w x * g x ∂μ := by
  have hc : μ[f | m] =ᵐ[μ] μ[g | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) (m := m) (m₀ := m₀)
      (f := g) (g := μ[f | m]) hm hg
      (fun _ _ _ => integrable_condExp.integrableOn)
    · intro A hA _
      rw [setIntegral_condExp hm hf hA, he A hA]
    · exact stronglyMeasurable_condExp.aestronglyMeasurable
  have hcf := condExp_mul_of_stronglyMeasurable_left hw hwf hf
  have hcg := condExp_mul_of_stronglyMeasurable_left hw hwg hg
  calc
    _ = ∫ x, (μ[w * f | m]) x ∂μ := (integral_condExp hm).symm
    _ = ∫ x, w x * (μ[f | m]) x ∂μ := integral_congr_ae hcf
    _ = ∫ x, w x * (μ[g | m]) x ∂μ := integral_congr_ae (hc.mono fun x hx => by simp [hx])
    _ = ∫ x, (μ[w * g | m]) x ∂μ := (integral_congr_ae hcg).symm
    _ = _ := integral_condExp hm

#print axioms u5_integral_mul_of_setIntegral_eq

/-- Discounting preserves the stopped Laplace restart identity. -/
theorem u5_regular_signed_discounted_stopped_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) :
    (∫ γ, Real.exp (-s * (T γ : ℝ)) *
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (γ (T γ + t.toNNReal))) ∂K x) =
    ∫ γ, Real.exp (-s * (T γ : ℝ)) *
      u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g (γ (T γ)) ∂K x := by
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let shift : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
  let f : Path d → ℝ := fun γ => Φ (shift γ)
  let r : Path d → ℝ := fun γ => R (γ (T γ))
  let w : Path d → ℝ := fun γ => Real.exp (-s * (T γ : ℝ))
  have ht : Measurable[hT.measurableSpace] T := by
    simpa only [Function.comp_def, WithTop.untopD_coe] using (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
  have hw : StronglyMeasurable[hT.measurableSpace] w := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))).stronglyMeasurable
  have hwm : AEStronglyMeasurable w (K x) :=
    (hw.mono hT.measurableSpace_le).aestronglyMeasurable
  have hwb : ∀ᵐ γ ∂K x, ‖w γ‖ ≤ 1 := ae_of_all _ fun γ => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg _))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hf : Integrable f (K x) := by
    apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT)).aestronglyMeasurable _
    exact ae_of_all _ fun γ => hbd (shift γ)
  have hr : Integrable r (K x) := by
    apply Integrable.of_bound (R.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable ‖R‖
    exact ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _
  have hwf : Integrable (w * f) (K x) := hf.bdd_mul hwm hwb
  have hwr : Integrable (w * r) (K x) := hr.bdd_mul hwm hwb
  have he (A : Set (Path d)) (hA : MeasurableSet[hT.measurableSpace] A) :
      (∫ γ in A, f γ ∂K x) = ∫ γ in A, r γ ∂K x := by
    simpa only [f, r, Φ, shift, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_stopped_path_laplace hd ω lam Λ hΛ hω K hfdd x T hT g s hs A hA
  exact u5_integral_mul_of_setIntegral_eq hT.measurableSpace_le hf hr hw hwf hwr he

#print axioms u5_regular_signed_discounted_stopped_path_laplace

/-- Split an integrable half-line integral at a nonnegative time and translate the tail. -/
theorem u5_integral_Ioi_split_translate (f : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hf : IntegrableOn f (Set.Ioi 0)) :
    (∫ t : ℝ in Set.Ioc (0 : ℝ) a, f t) +
      (∫ t : ℝ in Set.Ioi 0, f (a + t)) = ∫ t : ℝ in Set.Ioi 0, f t := by
  have ht := (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f (Set.Ioi a)
  have hp : (fun t : ℝ => a + t) ⁻¹' Set.Ioi a = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [hp] at ht
  rw [ht, ← intervalIntegral.integral_of_le ha]
  exact intervalIntegral.integral_interval_add_Ioi hf (hf.mono_set (Set.Ioi_subset_Ioi ha))

#print axioms u5_integral_Ioi_split_translate

/-- A discounted continuous path occupation splits at any finite time. -/
theorem u5_discounted_path_integral_split {d : ℕ} (γ : Path d)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) (a : ℝ≥0) :
    (∫ u : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) +
      Real.exp (-s * (a : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ (a + u.toNNReal))) =
    ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal) := by
  let f : ℝ → ℝ := fun u => Real.exp (-s * u) * g (γ u.toNNReal)
  have hE : IntegrableOn (fun u : ℝ => ‖g‖ * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hf : IntegrableOn f (Set.Ioi 0) := by
    apply hE.mono' (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (g.continuous.comp (γ.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable)
    exact ae_of_all _ fun u => by
      change ‖Real.exp (-s * u) * g (γ u.toNNReal)‖ ≤ ‖g‖ * Real.exp (-s * u)
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
      exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
        (Real.exp_nonneg _)
  have htail : (∫ u : ℝ in Set.Ioi 0, f ((a : ℝ) + u)) =
      Real.exp (-s * (a : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ (a + u.toNNReal))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [Set.mem_Ioi] at hu
    dsimp only [f]
    rw [show -s * ((a : ℝ) + u) = -s * (a : ℝ) + -s * u by ring, Real.exp_add,
      Real.toNNReal_add (NNReal.coe_nonneg a) hu.le, Real.toNNReal_coe]
    ring
  have he := u5_integral_Ioi_split_translate f (a : ℝ) (NNReal.coe_nonneg a) hf
  rw [htail] at he
  exact he

#print axioms u5_discounted_path_integral_split

theorem u5_regular_signed_bounded_stopped_discounted_resolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (H : ℝ≥0) (hTH : ∀ γ, T γ ≤ H) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    (∫ γ, (Real.exp (-s * (T γ : ℝ)) * R (γ (T γ)) +
      ∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x := by
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let shift : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
  let f : Path d → ℝ := fun γ => Φ (shift γ)
  let r : Path d → ℝ := fun γ => R (γ (T γ))
  let w : Path d → ℝ := fun γ => Real.exp (-s * (T γ : ℝ))
  have ht : Measurable[hT.measurableSpace] T := by
    simpa only [Function.comp_def, WithTop.untopD_coe] using (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
  have hw : StronglyMeasurable[hT.measurableSpace] w := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))).stronglyMeasurable
  have hwm : AEStronglyMeasurable w (K x) :=
    (hw.mono hT.measurableSpace_le).aestronglyMeasurable
  have hwb : ∀ᵐ γ ∂K x, ‖w γ‖ ≤ 1 + (H : ℝ) := ae_of_all _ fun γ => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    have hH : 0 ≤ (H : ℝ) := (NNReal.coe_nonneg (T γ)).trans (NNReal.coe_le_coe.mpr (hTH γ))
    have hx := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg (T γ)))
    linarith
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hΦ : Integrable Φ (K x) := by
    apply Integrable.of_bound hΦm.aestronglyMeasurable _
    exact ae_of_all _ hbd
  have hf : Integrable f (K x) := by
    apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT)).aestronglyMeasurable _
    exact ae_of_all _ fun γ => hbd (shift γ)
  have hr : Integrable r (K x) := by
    apply Integrable.of_bound (R.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable ‖R‖
    exact ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _
  have hwf : Integrable (w * f) (K x) := hf.bdd_mul hwm hwb
  have hwr : Integrable (w * r) (K x) := hr.bdd_mul hwm hwb
  have he : (∫ γ, (w * f) γ ∂K x) = ∫ γ, (w * r) γ ∂K x := by
    simpa only [w, f, r, Φ, shift, Pi.mul_apply, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_discounted_stopped_path_laplace hd ω lam Λ hΛ hω K hfdd x T hT g s hs
  have hpath : (∫ γ, Φ γ ∂K x) = R x := by
    exact u5_regular_signed_path_laplace_aux hd ω lam Λ hΛ hω K hfdd x s hs g
  change (∫ γ, (w * r) γ + (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
    Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x
  calc
    _ = ∫ γ, (Φ γ + (w * r) γ) - (w * f) γ ∂K x := by
      apply integral_congr_ae
      filter_upwards with γ
      have hp := u5_discounted_path_integral_split γ g s hs (T γ)
      change (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) + (w * f) γ = Φ γ at hp
      linarith
    _ = (∫ γ, Φ γ ∂K x) + (∫ γ, (w * r) γ ∂K x) -
        (∫ γ, (w * f) γ ∂K x) := by
      have hi := integral_sub (hΦ.add hwr) hwf
      simp only [Pi.add_apply] at hi
      rw [integral_add hΦ hwr] at hi
      exact hi
    _ = R x := by rw [he, hpath]; ring

#print axioms u5_regular_signed_bounded_stopped_discounted_resolvent

/-- The discounted resolvent identity holds at every finite stopping time. -/
theorem u5_regular_signed_finite_stopped_discounted_resolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    (∫ γ, (Real.exp (-s * (T γ : ℝ)) * R (γ (T γ)) +
      ∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x := by
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let shift : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
  let f : Path d → ℝ := fun γ => Φ (shift γ)
  let r : Path d → ℝ := fun γ => R (γ (T γ))
  let w : Path d → ℝ := fun γ => Real.exp (-s * (T γ : ℝ))
  have ht : Measurable[hT.measurableSpace] T := by
    simpa only [Function.comp_def, WithTop.untopD_coe] using (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
  have hw : StronglyMeasurable[hT.measurableSpace] w := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))).stronglyMeasurable
  have hwm : AEStronglyMeasurable w (K x) :=
    (hw.mono hT.measurableSpace_le).aestronglyMeasurable
  have hwb : ∀ᵐ γ ∂K x, ‖w γ‖ ≤ 1 := ae_of_all _ fun γ => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg (T γ)))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hΦ : Integrable Φ (K x) := by
    apply Integrable.of_bound hΦm.aestronglyMeasurable _
    exact ae_of_all _ hbd
  have hf : Integrable f (K x) := by
    apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT)).aestronglyMeasurable _
    exact ae_of_all _ fun γ => hbd (shift γ)
  have hr : Integrable r (K x) := by
    apply Integrable.of_bound (R.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable ‖R‖
    exact ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _
  have hwf : Integrable (w * f) (K x) := hf.bdd_mul hwm hwb
  have hwr : Integrable (w * r) (K x) := hr.bdd_mul hwm hwb
  have he : (∫ γ, (w * f) γ ∂K x) = ∫ γ, (w * r) γ ∂K x := by
    simpa only [w, f, r, Φ, shift, Pi.mul_apply, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_discounted_stopped_path_laplace hd ω lam Λ hΛ hω K hfdd x T hT g s hs
  have hpath : (∫ γ, Φ γ ∂K x) = R x := by
    exact u5_regular_signed_path_laplace_aux hd ω lam Λ hΛ hω K hfdd x s hs g
  change (∫ γ, (w * r) γ + (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
    Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x
  calc
    _ = ∫ γ, (Φ γ + (w * r) γ) - (w * f) γ ∂K x := by
      apply integral_congr_ae
      filter_upwards with γ
      have hp := u5_discounted_path_integral_split γ g s hs (T γ)
      change (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) + (w * f) γ = Φ γ at hp
      linarith
    _ = (∫ γ, Φ γ ∂K x) + (∫ γ, (w * r) γ ∂K x) -
        (∫ γ, (w * f) γ ∂K x) := by
      have hi := integral_sub (hΦ.add hwr) hwf
      simp only [Pi.add_apply] at hi
      rw [integral_add hΦ hwr] at hi
      exact hi
    _ = R x := by rw [he, hpath]; ring


#print axioms u5_regular_signed_finite_stopped_discounted_resolvent

/-- The discounted restart identity on a stopping-time event. -/
theorem u5_regular_signed_discounted_stopped_path_laplace_on_event
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s)
    (A : Set (Path d)) (hA : MeasurableSet[hT.measurableSpace] A) :
    (∫ γ in A, Real.exp (-s * (T γ : ℝ)) *
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (γ (T γ + t.toNNReal))) ∂K x) =
    ∫ γ in A, Real.exp (-s * (T γ : ℝ)) *
      u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g (γ (T γ)) ∂K x := by
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let shift : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
  let f : Path d → ℝ := fun γ => Φ (shift γ)
  let r : Path d → ℝ := fun γ => R (γ (T γ))
  let w : Path d → ℝ := fun γ => Real.exp (-s * (T γ : ℝ))
  have ht : Measurable[hT.measurableSpace] T := by
    simpa only [Function.comp_def, WithTop.untopD_coe] using (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
  have hw : StronglyMeasurable[hT.measurableSpace] w := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))).stronglyMeasurable
  have hwm : AEStronglyMeasurable w (K x) :=
    (hw.mono hT.measurableSpace_le).aestronglyMeasurable
  have hwb : ∀ᵐ γ ∂K x, ‖w γ‖ ≤ 1 := ae_of_all _ fun γ => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg _))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hf : Integrable f (K x) := by
    apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT)).aestronglyMeasurable _
    exact ae_of_all _ fun γ => hbd (shift γ)
  have hr : Integrable r (K x) := by
    apply Integrable.of_bound (R.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable ‖R‖
    exact ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _
  have hwf : Integrable (w * f) (K x) := hf.bdd_mul hwm hwb
  have hwr : Integrable (w * r) (K x) := hr.bdd_mul hwm hwb
  have he (A : Set (Path d)) (hA : MeasurableSet[hT.measurableSpace] A) :
      (∫ γ in A, f γ ∂K x) = ∫ γ in A, r γ ∂K x := by
    simpa only [f, r, Φ, shift, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_stopped_path_laplace hd ω lam Λ hΛ hω K hfdd x T hT g s hs A hA
  have hA0 : MeasurableSet A := hT.measurableSpace_le A hA
  have hwi : StronglyMeasurable[hT.measurableSpace] (A.indicator w) := hw.indicator hA
  have hind (v : Path d → ℝ) : A.indicator w * v = A.indicator (w * v) := by
    funext γ
    exact (Set.indicator_mul_left A w v).symm
  have hwif : Integrable (A.indicator w * f) (K x) := by
    rw [hind]
    exact hwf.indicator hA0
  have hwir : Integrable (A.indicator w * r) (K x) := by
    rw [hind]
    exact hwr.indicator hA0
  have hi := u5_integral_mul_of_setIntegral_eq hT.measurableSpace_le hf hr hwi hwif hwir he
  change (∫ γ, (A.indicator w * f) γ ∂K x) = ∫ γ, (A.indicator w * r) γ ∂K x at hi
  rw [hind, hind, integral_indicator hA0, integral_indicator hA0] at hi
  simpa only [w, f, r, Φ, shift, Pi.mul_apply,
    MarkovProcess.ContinuousPath.shift_apply] using hi

#print axioms u5_regular_signed_discounted_stopped_path_laplace_on_event

/-- The discounted resolvent obeys Dynkin's identity between finite stopping times. -/
theorem u5_regular_signed_two_stopping_discounted_Dynkin
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (S T : Path d → ℝ≥0)
    (hS : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (S γ : WithTop ℝ≥0)))
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    (hST : ∀ γ, S γ ≤ T γ) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    ∀ A : Set (Path d), MeasurableSet[hS.measurableSpace] A →
      (∫ γ in A, (Real.exp (-s * (T γ : ℝ)) * R (γ (T γ)) -
        Real.exp (-s * (S γ : ℝ)) * R (γ (S γ)) +
        ∫ u : ℝ in Set.Ioc (S γ : ℝ) (T γ : ℝ),
          Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = 0 := by
  dsimp only
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let f : (Path d → ℝ≥0) → Path d → ℝ := fun V γ =>
    Real.exp (-s * (V γ : ℝ)) * Φ (MarkovProcess.ContinuousPath.shift (V γ) γ)
  let r : (Path d → ℝ≥0) → Path d → ℝ := fun V γ =>
    Real.exp (-s * (V γ : ℝ)) * R (γ (V γ))
  intro A hA
  have hAT : MeasurableSet[hT.measurableSpace] A :=
    hS.measurableSpace_mono hT (fun γ => WithTop.coe_le_coe.mpr (hST γ)) A hA
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => ‖g‖ * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hi (V : Path d → ℝ≥0)
      (hV : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
        (fun γ => (V γ : WithTop ℝ≥0))) : Integrable (f V) (K x) ∧ Integrable (r V) (K x) := by
    have hVm := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime V hV
    have hwm : AEStronglyMeasurable (fun γ => Real.exp (-s * (V γ : ℝ))) (K x) :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul
        (NNReal.continuous_coe.measurable.comp hVm))).aestronglyMeasurable
    have hwb : ∀ᵐ γ ∂K x, ‖Real.exp (-s * (V γ : ℝ))‖ ≤ 1 := ae_of_all _ fun γ => by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg _))
    have hf : Integrable (fun γ => Φ (MarkovProcess.ContinuousPath.shift (V γ) γ)) (K x) := by
      apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime V hV)).aestronglyMeasurable _
      exact ae_of_all _ fun γ => hbd _
    have hr : Integrable (fun γ => R (γ (V γ))) (K x) := by
      apply Integrable.of_bound (R.continuous.measurable.comp
        (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel V hV)).aestronglyMeasurable ‖R‖
      exact ae_of_all _ fun γ => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _
    exact ⟨hf.bdd_mul hwm hwb, hr.bdd_mul hwm hwb⟩
  have hES : (∫ γ in A, f S γ ∂K x) = ∫ γ in A, r S γ ∂K x := by
    simpa only [f, r, Φ, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_discounted_stopped_path_laplace_on_event hd ω lam Λ hΛ hω K hfdd x S hS g s hs A hA
  have hET : (∫ γ in A, f T γ ∂K x) = ∫ γ in A, r T γ ∂K x := by
    simpa only [f, r, Φ, MarkovProcess.ContinuousPath.shift_apply] using
      u5_regular_signed_discounted_stopped_path_laplace_on_event hd ω lam Λ hΛ hω K hfdd x T hT g s hs A hAT
  have hpoint (γ : Path d) :
      (∫ u : ℝ in Set.Ioc (S γ : ℝ) (T γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) =
        f S γ - f T γ := by
    let q : ℝ → ℝ := fun u => Real.exp (-s * u) * g (γ u.toNNReal)
    have hq : Continuous q := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (g.continuous.comp (γ.continuous.comp continuous_real_toNNReal))
    have hs0 : (0 : ℝ) ≤ S γ := NNReal.coe_nonneg _
    have hst : (S γ : ℝ) ≤ T γ := NNReal.coe_le_coe.mpr (hST γ)
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hq.intervalIntegrable 0 (S γ)) (hq.intervalIntegrable (S γ) (T γ))
    rw [intervalIntegral.integral_of_le hs0, intervalIntegral.integral_of_le hst,
      intervalIntegral.integral_of_le (hs0.trans hst)] at hadd
    have hps := u5_discounted_path_integral_split γ g s hs (S γ)
    have hpt := u5_discounted_path_integral_split γ g s hs (T γ)
    change (∫ u in Set.Ioc (0 : ℝ) (S γ : ℝ), q u) + f S γ = Φ γ at hps
    change (∫ u in Set.Ioc (0 : ℝ) (T γ : ℝ), q u) + f T γ = Φ γ at hpt
    linarith
  change (∫ γ in A, r T γ - r S γ +
    (∫ u : ℝ in Set.Ioc (S γ : ℝ) (T γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = 0
  calc
    _ = ∫ γ in A, (r T γ - r S γ) + (f S γ - f T γ) ∂K x := by
      apply integral_congr_ae
      exact ae_of_all _ fun γ => by dsimp only; rw [hpoint γ]
    _ = ((∫ γ in A, r T γ ∂K x) - ∫ γ in A, r S γ ∂K x) +
        ((∫ γ in A, f S γ ∂K x) - ∫ γ in A, f T γ ∂K x) := by
      have hadd := integral_add (μ := (K x).restrict A) ((hi T hT).2.integrableOn.sub (hi S hS).2.integrableOn)
        ((hi S hS).1.integrableOn.sub (hi T hT).1.integrableOn)
      simp only [Pi.sub_apply] at hadd
      rw [integral_sub (hi T hT).2.integrableOn (hi S hS).2.integrableOn,
        integral_sub (hi S hS).1.integrableOn (hi T hT).1.integrableOn] at hadd
      exact hadd
    _ = 0 := by rw [hES, hET]; ring

#print axioms u5_regular_signed_two_stopping_discounted_Dynkin

/-- A possibly infinite stopping time truncated at a finite horizon is finite and
remains a stopping time for the same canonical filtration. -/
theorem u5_extended_stopping_time_truncate {d : ℕ}
    (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (a : ℝ≥0) :
    IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => ((WithTop.untopD 0 (min (T γ) (a : WithTop ℝ≥0)) : ℝ≥0) : WithTop ℝ≥0)) := by
  have heq : (fun γ => ((WithTop.untopD 0 (min (T γ) (a : WithTop ℝ≥0)) : ℝ≥0) : WithTop ℝ≥0)) =
      (fun γ => min (T γ) (a : WithTop ℝ≥0)) := by
    funext γ
    cases h : T γ with
    | top => rw [min_eq_right (le_top : (a : WithTop ℝ≥0) ≤ ⊤), WithTop.untopD_coe]
    | coe t =>
      rcases le_total t a with hta | hat
      · rw [min_eq_left (WithTop.coe_le_coe.mpr hta), WithTop.untopD_coe]
      · rw [min_eq_right (WithTop.coe_le_coe.mpr hat), WithTop.untopD_coe]
  rw [heq]
  exact hT.min_const a

#print axioms u5_extended_stopping_time_truncate

/-- The occupation domain for a finite extended time is the usual interval. -/
theorem u5_extended_occupation_domain_coe (a : ℝ≥0) :
    {u : ℝ | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ (a : WithTop ℝ≥0)} =
      Set.Ioc 0 (a : ℝ) := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]

/-- At infinity the occupation domain is the full positive half-line. -/
theorem u5_extended_occupation_domain_top :
    {u : ℝ | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ ⊤} = Set.Ioi 0 := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi, le_top, and_true]

#print axioms u5_extended_occupation_domain_coe
#print axioms u5_extended_occupation_domain_top

/-- Exponential discount sends any uniformly bounded sequence to zero. -/
theorem u5_exp_discount_bounded_tendsto_zero (s : ℝ) (hs : 0 < s)
    (v : ℕ → ℝ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) :
    Tendsto (fun n : ℕ => Real.exp (-s * (n : ℝ)) * v n) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => Real.exp (-s * (n : ℝ)) * C) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have ht := Real.tendsto_exp_atBot.comp (hn.const_mul_atTop_of_neg (neg_lt_zero.mpr hs))
    simpa using ht.mul_const C
  apply squeeze_zero_norm (fun n => ?_) he
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hv n) (Real.exp_nonneg _)

#print axioms u5_exp_discount_bounded_tendsto_zero

/-- Integer truncations eventually leave any finite time unchanged. -/
theorem u5_extended_time_truncate_eventually (t : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop,
      (WithTop.untopD 0 (min (t : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0) = t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have ht : t ≤ (n : ℝ≥0) := NNReal.coe_le_coe.mpr
    ((le_of_lt hN).trans (Nat.cast_le.mpr hn))
  rw [min_eq_left (WithTop.coe_le_coe.mpr ht), WithTop.untopD_coe]

#print axioms u5_extended_time_truncate_eventually

/-- Finite discounted path occupations converge to the full occupation. -/
theorem u5_discounted_path_occupation_tendsto {d : ℕ} (γ : Path d)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
      Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal))) := by
  let v : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    Real.exp (-s * u) * g (γ ((n : ℝ≥0) + u.toNNReal))
  have hE : IntegrableOn (fun u : ℝ => ‖g‖ * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hv : ∀ n, ‖v n‖ ≤ ∫ u in Set.Ioi (0 : ℝ), ‖g‖ * Real.exp (-s * u) := by
    intro n
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun u => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have hz := u5_exp_discount_bounded_tendsto_zero s hs v _ hv
  have hc : Tendsto (fun _ : ℕ => ∫ u : ℝ in Set.Ioi 0,
      Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal))) := tendsto_const_nhds
  have hlim := hc.sub hz
  have heq : (fun n : ℕ => ∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
      Real.exp (-s * u) * g (γ u.toNNReal)) =
      (fun n : ℕ => (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal)) -
        Real.exp (-s * (n : ℝ)) * v n) := by
    funext n
    have h := u5_discounted_path_integral_split γ g s hs (n : ℝ≥0)
    change (∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) +
      Real.exp (-s * (n : ℝ)) * v n = _ at h
    linarith
  rw [heq]
  simpa using hlim

#print axioms u5_discounted_path_occupation_tendsto

/-- The finite truncated discounted expression converges at every path and every
extended time, including infinity. -/
theorem u5_extended_discounted_expression_tendsto {d : ℕ} (γ : Path d)
    (g R : ZeroAtInftyContinuousMap (Vec d) ℝ) (s : ℝ) (hs : 0 < s)
    (t : WithTop ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let a : ℝ≥0 := WithTop.untopD 0 (min t ((n : ℝ≥0) : WithTop ℝ≥0))
      Real.exp (-s * (a : ℝ)) * R (γ a) +
        ∫ u : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 ((if h : t = ⊤ then 0 else Real.exp (-s * (t.untop h : ℝ)) * R (γ (t.untop h))) +
        ∫ u : ℝ in {u | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ t},
          Real.exp (-s * u) * g (γ u.toNNReal))) := by
  cases t with
  | top =>
    have hz := u5_exp_discount_bounded_tendsto_zero s hs (fun n => R (γ (n : ℝ≥0))) ‖R‖
      (fun n => BoundedContinuousFunction.norm_coe_le_norm R.toBCF _)
    have ho := u5_discounted_path_occupation_tendsto γ g s hs
    simpa only [min_eq_right le_top, WithTop.untopD_coe, dif_pos rfl, dite_true,
      u5_extended_occupation_domain_top, zero_add, NNReal.coe_natCast] using hz.add ho
  | coe a =>
    have he := u5_extended_time_truncate_eventually a
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [hn]
    simp only [WithTop.coe_ne_top, dite_false, WithTop.untop_coe,
      u5_extended_occupation_domain_coe]

#print axioms u5_extended_discounted_expression_tendsto

/-- The supplied realization satisfies the discounted resolvent identity at
possibly infinite stopping times, with zero terminal value at infinity. -/
theorem u5_regular_signed_extended_stopped_discounted_resolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T) :
    let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
    (∫ γ, ((if h : T γ = ⊤ then 0 else
        Real.exp (-s * ((T γ).untop h : ℝ)) * R (γ ((T γ).untop h))) +
      ∫ u : ℝ in {u | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ T γ},
        Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x := by
  dsimp only
  let R := u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g
  let A : ℕ → Path d → ℝ≥0 := fun n γ =>
    WithTop.untopD 0 (min (T γ) ((n : ℝ≥0) : WithTop ℝ≥0))
  let Φ : Path d → ℝ := fun γ => ∫ u : ℝ in Set.Ioi 0,
    Real.exp (-s * u) * g (γ u.toNNReal)
  let B : ℝ := ∫ u : ℝ in Set.Ioi 0, ‖g‖ * Real.exp (-s * u)
  let w : ℕ → Path d → ℝ := fun n γ => Real.exp (-s * (A n γ : ℝ))
  let r : ℕ → Path d → ℝ := fun n γ => w n γ * R (γ (A n γ))
  let f : ℕ → Path d → ℝ := fun n γ =>
    w n γ * Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ)
  let F : ℕ → Path d → ℝ := fun n γ => r n γ +
    ∫ u : ℝ in Set.Ioc (0 : ℝ) (A n γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)
  have hA (n : ℕ) : IsStoppingTime
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (A n γ : WithTop ℝ≥0)) :=
    u5_extended_stopping_time_truncate T hT (n : ℝ≥0)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hg : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (g.continuous.measurable.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hg.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun u : ℝ => ‖g‖ * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul ‖g‖
  have hΦb (γ : Path d) : ‖Φ γ‖ ≤ B := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun u => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
      (Real.exp_nonneg _)
  have heq (n : ℕ) : F n = fun γ => Φ γ + r n γ - f n γ := by
    funext γ
    have h := u5_discounted_path_integral_split γ g s hs (A n γ)
    change (∫ u : ℝ in Set.Ioc (0 : ℝ) (A n γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) + f n γ = Φ γ at h
    dsimp only [F]
    linarith
  have hwm (n : ℕ) : Measurable (w n) := by
    have ham := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime (A n) (hA n)
    exact Real.continuous_exp.measurable.comp (measurable_const.mul
      (NNReal.continuous_coe.measurable.comp ham))
  have hrm (n : ℕ) : Measurable (r n) := (hwm n).mul
    (R.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel (A n) (hA n)))
  have hfm (n : ℕ) : Measurable (f n) := (hwm n).mul
    (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime (A n) (hA n)))
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (K x) := by
    rw [heq n]
    exact ((hΦm.add (hrm n)).sub (hfm n)).aestronglyMeasurable
  have hw (n : ℕ) (γ : Path d) : ‖w n γ‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg _))
  have hbound (n : ℕ) (γ : Path d) : ‖F n γ‖ ≤ B + ‖R‖ + B := by
    have hr : ‖r n γ‖ ≤ ‖R‖ := by
      dsimp only [r]
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖R (γ (A n γ))‖ := mul_le_mul_of_nonneg_right (hw n γ) (norm_nonneg _)
        _ ≤ ‖R‖ := by simpa using BoundedContinuousFunction.norm_coe_le_norm R.toBCF (γ (A n γ))
    have hf : ‖f n γ‖ ≤ B := by
      dsimp only [f]
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ)‖ :=
          mul_le_mul_of_nonneg_right (hw n γ) (norm_nonneg _)
        _ ≤ B := by simpa using hΦb (MarkovProcess.ContinuousPath.shift (A n γ) γ)
    rw [heq n]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add (hΦb γ) hr) hf))
  have hlim := tendsto_integral_of_dominated_convergence (μ := K x) (fun _ => B + ‖R‖ + B)
    hFm (integrable_const _) (fun n => ae_of_all _ (hbound n))
    (ae_of_all _ fun γ => u5_extended_discounted_expression_tendsto γ g R s hs (T γ))
  have hfinite (n : ℕ) : (∫ γ, F n γ ∂K x) = R x := by
    simpa only [F, r, w, R] using
      u5_regular_signed_finite_stopped_discounted_resolvent hd ω lam Λ hΛ hω K hfdd x s hs g (A n) (hA n)
  have hc : Tendsto (fun n : ℕ => ∫ γ, F n γ ∂K x) atTop (𝓝 (R x)) := by
    simpa only [hfinite] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => R x) atTop (𝓝 (R x)))
  exact tendsto_nhds_unique hlim hc

#print axioms u5_regular_signed_extended_stopped_discounted_resolvent

/-- Restart the supplied realization on a stopped event on which the extended
stopping time is finite. -/
theorem u5_regular_signed_extended_stopping_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (x : Vec d) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∀ γ ∈ A, T γ < ⊤) →
      ((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((K x).restrict A) (fun γ => K (γ ((T γ).untopD 0))) := by
  intro A hA hfinite
  let D := MarkovProcess.StoppingTime.stoppingTimeSlice A T
  let Y : Path d → Vec d := fun γ => γ ((T γ).untopD 0)
  have hY : Measurable Y :=
    MarkovProcess.ContinuousPath.measurable_eval_untopD_stoppingTime T hT
  let κ := Kernel.comap K Y hY
  have hslice : ∀ n : ℕ,
      ((K x).restrict (D n)).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      κ ∘ₘ ((K x).restrict (D n)) := by
    intro n
    let S := MarkovProcess.StoppingTime.truncTime T (n : ℝ≥0)
    have hS := MarkovProcess.StoppingTime.isStoppingTime_truncTime hT (n : ℝ≥0)
    have hD : MeasurableSet (D n) :=
      MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice' hT hA n
    have hDS : MeasurableSet[hS.measurableSpace] (D n) := by
      rw [MarkovProcess.StoppingTime.measurableSpace_truncTime hT (n : ℝ≥0)]
      exact MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice hT hA n
    have hmain := u5_regular_signed_realization_stopping_restart hd ω lam Λ hΛ hω
      K hfdd x S hS (D n) hDS
    have hL : ((K x).restrict (D n)).map
        (fun γ => MarkovProcess.ContinuousPath.shift (S γ) γ) =
        ((K x).restrict (D n)).map
          (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) := by
      refine Measure.map_congr ((ae_restrict_iff' hD).mpr (ae_of_all _ fun γ hγ => ?_))
      exact congrArg (fun t => MarkovProcess.ContinuousPath.shift t γ)
        (MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice hγ)
    have hR : Kernel.comap K (fun γ => γ (S γ))
        (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel S hS) ∘ₘ
        ((K x).restrict (D n)) = κ ∘ₘ ((K x).restrict (D n)) := by
      refine Measure.comp_congr ((ae_restrict_iff' hD).mpr (ae_of_all _ fun γ hγ => ?_))
      simp only [κ, Y, Kernel.comap_apply]
      change K (γ (MarkovProcess.StoppingTime.truncTime T (n : ℝ≥0) γ)) = _
      rw [MarkovProcess.StoppingTime.truncTime_eq_untopD_of_mem_stoppingTimeSlice hγ]
    rw [← hL, hmain, hR]
  have hunion : (⋃ n, D n) = A := by
    rw [MarkovProcess.StoppingTime.iUnion_stoppingTimeSlice]
    exact Set.inter_eq_left.mpr hfinite
  have h := MarkovProcess.StoppingTime.map_restrict_iUnion_eq_comp_of_forall
    (K x) κ (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ)
    (MarkovProcess.ContinuousPath.measurable_shift_untopD_stoppingTime T hT) D
    (fun n => MarkovProcess.StoppingTime.measurableSet_stoppingTimeSlice' hT hA n)
    (MarkovProcess.StoppingTime.pairwise_disjoint_stoppingTimeSlice A) hslice
  rw [hunion] at h
  simpa only [κ, Y, Kernel.coe_comap, Function.comp_def] using h

#print axioms u5_regular_signed_extended_stopping_restart

private theorem u5_supplied_gmp_continuous_transition_integral
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : BoundedContinuousFunction (Vec d) ℝ) (x : Vec d) :
    Continuous (fun t : ℝ≥0 => ∫ y, f y ∂r.transitionKernel t x) := by
  let := r.pathLaw_isMarkovKernel
  have hmap (t : ℝ≥0) :
      (∫ y, f y ∂r.transitionKernel t x) = ∫ γ, f (pathPosition t γ) ∂r.pathLaw x := by
    rw [← r.pathLaw_endpoint t x]
    exact integral_map (measurable_pathPosition t).aemeasurable
      f.continuous.aestronglyMeasurable
  simp_rw [hmap]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t
    exact (f.continuous.measurable.comp (measurable_pathPosition t)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun γ => f.norm_coe_le_norm (pathPosition t γ)
  · exact integrable_const _
  · exact ae_of_all _ fun γ => f.continuous.comp γ.continuous

/-- Positive-time almost-everywhere agreement of C₀ actions extends to every
starting point, using the supplied realization's continuous paths and density. -/
theorem u5_supplied_gmp_transition_eq_of_ae_C0_action
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (hae : ∀ t : ℝ≥0, 0 < t → ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂r.transitionKernel t x) =
          ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t x) :
    ∀ t : ℝ≥0, r.transitionKernel t = (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t := by
  intro t
  by_cases ht : t = 0
  · subst t
    rw [r.transitionKernel_zero, (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω).kernel_zero]
  apply Kernel.ext
  intro x
  let := r.transitionKernel_isMarkovKernel t
  let : IsMarkovKernel ((u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t) :=
    ⟨fun y => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t y⟩⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let f₀ : ZeroAtInftyContinuousMap (Vec d) ℝ := f
  let g := (u2RegularC0Semigroup hd ω lam Λ hΛ hω) t f₀
  have hshift (s : ℝ≥0) (hs : 0 < s) :
      (∫ y, f₀ y ∂r.transitionKernel (s + t) x) =
        ∫ y, g y ∂r.transitionKernel s x := by
    let := r.transitionKernel_isMarkovKernel s
    let := r.transitionKernel_isMarkovKernel (s + t)
    have hAC : r.transitionKernel s x ≪ (volume : Measure (Vec d)) := by
      rw [r.transitionKernel_eq_heatKernel s hs x]
      exact withDensity_absolutelyContinuous _ _
    rw [r.transitionKernel_add]
    change (∫ y, f₀.toBCF y ∂(r.transitionKernel t ∘ₖ r.transitionKernel s) x) = _
    rw [Kernel.integral_comp (f₀.toBCF.integrable _)]
    apply integral_congr_ae
    filter_upwards [hAC.ae_eq (hae t (pos_iff_ne_zero.mpr ht) f₀)] with y hy
    exact hy.trans (u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f₀ y)
  have hleft : Tendsto (fun s : ℝ≥0 => ∫ y, f₀ y ∂r.transitionKernel (s + t) x)
      (𝓝[Set.Ioi 0] 0) (𝓝 (∫ y, f₀ y ∂r.transitionKernel t x)) := by
    have hc : Continuous (fun s : ℝ≥0 => ∫ y, f₀ y ∂r.transitionKernel (s + t) x) :=
      (u5_supplied_gmp_continuous_transition_integral hd ω lam Λ hΛ hω h0 h1 r f₀.toBCF x).comp
        (continuous_id.add continuous_const)
    simpa only [zero_add] using (hc.tendsto (0 : ℝ≥0)).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun s : ℝ≥0 => ∫ y, g y ∂r.transitionKernel s x)
      (𝓝[Set.Ioi 0] 0) (𝓝 (g x)) := by
    have hc := (u5_supplied_gmp_continuous_transition_integral hd ω lam Λ hΛ hω h0 h1 r g.toBCF x).tendsto (0 : ℝ≥0)
    have hz : (∫ y, g y ∂r.transitionKernel 0 x) = g x := by
      rw [r.transitionKernel_zero, Kernel.id_apply, integral_dirac]
    rw [← hz]
    exact hc.mono_left nhdsWithin_le_nhds
  have hevent : (fun s : ℝ≥0 => ∫ y, f₀ y ∂r.transitionKernel (s + t) x) =ᶠ[
      𝓝[Set.Ioi 0] 0] (fun s => ∫ y, g y ∂r.transitionKernel s x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hshift s hs
  exact (tendsto_nhds_unique (hleft.congr' hevent) hright).trans
    (u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f₀ x).symm

#print axioms u5_supplied_gmp_transition_eq_of_ae_C0_action

/-- A supplied realization with the canonical transition kernels has continuous
C₀ transition actions at every starting point. -/
theorem u5_supplied_gmp_feller
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (heq : ∀ t : ℝ≥0, r.transitionKernel t = (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t) :
    ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ, ∀ t : ℝ≥0,
      Continuous (fun x => ∫ y, f y ∂r.transitionKernel t x) := by
  intro f t
  simp_rw [heq t, u2RegularC0KernelSemigroup_integral]
  exact ((u2RegularC0Semigroup hd ω lam Λ hΛ hω) t f).continuous

#print axioms u5_supplied_gmp_feller

end EinsteinFull
