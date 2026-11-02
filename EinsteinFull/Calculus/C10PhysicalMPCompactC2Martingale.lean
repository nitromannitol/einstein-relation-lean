import EinsteinFull.Calculus.C10PhysicalMPRightContinuous
import EinsteinFull.Calculus.S4PhysicalWellPosedSupport
import PDEFoundation.PDE.HarmonicKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
/-!
# Compact C² martingale tests

Smooth compact tests of an arbitrary physical martingale-problem solution extend to compact
C² tests in the literal right-continuous path filtration. Genuine mollifications converge
through two derivatives, and common compact support supplies deterministic domination.

The mollification construction reuses the checked helpers from
`C9PhysicalMPCompactC2Dynkin` at commit `a69a4f86`, copied here to avoid a peer work-in-progress
import.
-/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Convolution Pointwise
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinFull.Work.W5
/-- Dominated pointwise limits preserve the literal martingale predicate. -/
private theorem martingale_of_dominated_pointwise_limit
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 m} {M : ℕ → ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F P)
    (hlim : ∀ t γ, Tendsto (fun n => M n t γ) atTop (𝓝 (N t γ)))
    (hb : ∀ t, ∃ C : ℝ, ∀ n γ, ‖M n t γ‖ ≤ C) : Martingale N F P := by
  have had : StronglyAdapted F N := fun t =>
    stronglyMeasurable_of_tendsto atTop (fun n => (hM n).stronglyMeasurable t)
      (tendsto_pi_nhds.mpr (hlim t))
  have hNb (t : ℝ≥0) : ∃ C : ℝ, ∀ γ, ‖N t γ‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb t
    exact ⟨C, fun γ => le_of_tendsto ((hlim t γ).norm)
      (Eventually.of_forall fun n => hC n γ)⟩
  have hNi (t : ℝ≥0) : Integrable (N t) P := by
    obtain ⟨C, hC⟩ := hNb t
    exact Integrable.of_bound ((had t).mono (F.le t)).aestronglyMeasurable C
      (ae_of_all _ hC)
  have hInt (t : ℝ≥0) (B : Set Ω) :
      Tendsto (fun n => ∫ γ in B, M n t γ ∂P) atTop (𝓝 (∫ γ in B, N t γ ∂P)) := by
    obtain ⟨C, hC⟩ := hb t
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => ((hM n).integrable t).aestronglyMeasurable.restrict
    · exact integrable_const C
    · exact fun n => ae_of_all _ (hC n)
    · exact ae_of_all _ (hlim t)
  refine ⟨had, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hNi t)
    (fun _ _ _ => (hNi s).integrableOn) (fun B hB _ => ?_)
    (had s).aestronglyMeasurable
  exact tendsto_nhds_unique (hInt s B)
    (by simpa only [fun n => (hM n).setIntegral_eq hst hB] using hInt t B)

private def dynkinConvolution {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : Vec d → ℝ) (g : Vec d → E) : Vec d → E :=
  k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

/-- Differentiating a compact test under convolution differentiates the test. -/
private theorem fderiv_compact_convolution
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Vec d → ℝ} {g : Vec d → E}
    (hk : LocallyIntegrable k volume) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fderiv ℝ g) := by
  have hb : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).precompR (Vec d) =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a A
    rfl
  funext y
  have h := (hc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) hk hg y).fderiv
  rw [hb] at h
  exact h

private def dynkinMollifierScale (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem dynkinMollifierScale_pos (n : ℕ) : 0 < dynkinMollifierScale n := by
  unfold dynkinMollifierScale
  positivity

private theorem dynkinMollifierScale_tendsto :
    Tendsto dynkinMollifierScale atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall dynkinMollifierScale_pos⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Approximation applies to scalar tests and their derivative-valued fields. -/
private theorem dynkin_mollifier_tendstoLocallyUniformly
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {G : Vec d → E} (hG : Continuous G) :
    TendstoLocallyUniformly
      (fun n => PDE.harmonicKernelScaled (dynkinMollifierScale n)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) G atTop := by
  have hs : Tendsto
      (fun n => Function.support (PDE.harmonicKernelScaled (d := d) (dynkinMollifierScale n)))
      atTop (𝓝 (0 : Vec d)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro S hS
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
    filter_upwards [(dynkinMollifierScale_tendsto.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hε)] with n hn
    intro y hy
    apply hεS
    have hy' := PDE.euclideanBall_subset_supBall (dynkinMollifierScale_pos n)
      (PDE.harmonicKernelScaled_tsupport_subset (dynkinMollifierScale_pos n)
        (subset_tsupport _ hy))
    exact Metric.ball_subset_ball hn.le hy'
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  have hc : Tendsto
      (fun p : ℕ × Vec d =>
        (PDE.harmonicKernelScaled (dynkinMollifierScale p.1)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) p.2)
      (atTop ×ˢ 𝓝 x) (𝓝 (G x)) :=
    convolution_tendsto_right
      (Eventually.of_forall fun p => PDE.harmonicKernelScaled_nonneg (dynkinMollifierScale_pos p.1))
      (Eventually.of_forall fun p => PDE.harmonicKernelScaled_integral_eq_one
        (dynkinMollifierScale_pos p.1))
      (hs.comp tendsto_fst)
      (Eventually.of_forall fun _ => hG.aestronglyMeasurable)
      ((hG.tendsto x).comp tendsto_snd) tendsto_snd
  exact (((hG.tendsto x).comp tendsto_snd).prodMk_nhds hc).mono_right
    (nhds_le_uniformity (G x))

private def dynkinMollification {d : ℕ} (f : Vec d → ℝ) (n : ℕ) : Vec d → ℝ :=
  PDE.harmonicKernelScaled (dynkinMollifierScale n)
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

private theorem dynkinMollification_smooth {d : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dynkinMollification f n) :=
  (PDE.harmonicKernelScaled_hasCompactSupport (dynkinMollifierScale_pos n)).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (PDE.harmonicKernelScaled_smooth _) hf.locallyIntegrable

private theorem dynkinMollification_compact {d : ℕ} {f : Vec d → ℝ}
    (hc : HasCompactSupport f) (n : ℕ) : HasCompactSupport (dynkinMollification f n) :=
  (PDE.harmonicKernelScaled_hasCompactSupport (dynkinMollifierScale_pos n)).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hc

private theorem dynkinMollification_fderiv {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hc : HasCompactSupport f) (n : ℕ) :
    fderiv ℝ (dynkinMollification f n) =
      PDE.harmonicKernelScaled (dynkinMollifierScale n)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fderiv ℝ f) :=
  fderiv_compact_convolution (PDE.harmonicKernelScaled_smooth _).continuous.locallyIntegrable
    (hf.of_le (by norm_num)) hc

private theorem dynkinMollification_fderiv_fderiv {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hc : HasCompactSupport f) (n : ℕ) :
    fderiv ℝ (fderiv ℝ (dynkinMollification f n)) =
      dynkinConvolution (PDE.harmonicKernelScaled (dynkinMollifierScale n))
        (fderiv ℝ (fderiv ℝ f)) := by
  rw [dynkinMollification_fderiv hf hc]
  exact fderiv_compact_convolution (PDE.harmonicKernelScaled_smooth _).continuous.locallyIntegrable
    (hf.fderiv_right (m := 1) (by norm_num)) (hc.fderiv ℝ)

/-- The actual mollified tests converge together with their first two total derivatives. -/
private theorem dynkinMollification_c2_convergence {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hc : HasCompactSupport f) :
    TendstoLocallyUniformly (dynkinMollification f) f atTop ∧
    TendstoLocallyUniformly (fun n => fderiv ℝ (dynkinMollification f n))
      (fderiv ℝ f) atTop ∧
    TendstoLocallyUniformly (fun n => fderiv ℝ (fderiv ℝ (dynkinMollification f n)))
      (fderiv ℝ (fderiv ℝ f)) atTop := by
  refine ⟨dynkin_mollifier_tendstoLocallyUniformly hf.continuous, ?_, ?_⟩
  · simp_rw [dynkinMollification_fderiv hf hc]
    exact dynkin_mollifier_tendstoLocallyUniformly (hf.continuous_fderiv (by norm_num))
  · simp_rw [dynkinMollification_fderiv_fderiv hf hc]
    exact dynkin_mollifier_tendstoLocallyUniformly
      ((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num))

/-- Every approximation is supported in a single compact enlargement. -/
private theorem dynkinMollification_common_support {d : ℕ} {f : Vec d → ℝ}
    (hc : HasCompactSupport f) :
    ∃ K : Set (Vec d), IsCompact K ∧ tsupport f ⊆ K ∧
      ∀ n, tsupport (dynkinMollification f n) ⊆ K := by
  let K := tsupport f + Metric.closedBall (0 : Vec d) 1
  have hK : IsCompact K := hc.isCompact.add (isCompact_closedBall 0 1)
  refine ⟨K, hK, ?_, ?_⟩
  · intro y hy
    exact ⟨y, hy, 0, by simp, by simp⟩
  · intro n
    apply closure_minimal ?_ hK.isClosed
    refine (support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ)).trans
      (add_subset_add subset_closure ?_)
    intro y hy
    have hb := PDE.euclideanBall_subset_supBall (dynkinMollifierScale_pos n)
      (PDE.harmonicKernelScaled_tsupport_subset (dynkinMollifierScale_pos n)
        (subset_tsupport _ hy))
    have hs : dynkinMollifierScale n ≤ 1 := by
      unfold dynkinMollifierScale
      apply (div_le_one (by positivity)).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact Metric.ball_subset_closedBall (hb.trans_le hs)


private theorem physicalGenerator_c2_jet {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (hs : IsSmoothFieldPair ω) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (y : Vec d) :
    physicalGenerator i ω lam f y =
      (1 / 2 : ℝ) * ∑ j, ∑ k, ω.1 y j k *
        fderiv ℝ (fderiv ℝ f) y (unitVector j) (unitVector k) +
      ∑ j, EinsteinFull.physicalDrift ω i lam y j * fderiv ℝ f y (unitVector j) := by
  have he (j k : Fin d) :
      fderiv ℝ (fun z => fderiv ℝ f z (unitVector k)) y (unitVector j) =
        fderiv ℝ (fderiv ℝ f) y (unitVector j) (unitVector k) := by
    rw [fderiv_clm_apply
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y)
      (differentiableAt_const (unitVector k))]
    rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
    rfl
  rw [EinsteinFull.physicalGenerator_eq_svGenerator hs i lam hf y]
  unfold External.Draft.svGenerator
  simp_rw [he]

private theorem continuous_physicalDrift {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (hs : IsSmoothFieldPair ω) (lam : ℝ) (j : Fin d) :
    Continuous (fun y => EinsteinFull.physicalDrift ω i lam y j) := by
  exact ((reduce ω).2.continuous.inv₀ (fun y => (clockDensity_pos ω y).ne')).mul
    (EinsteinFull.continuous_forcedDrift_apply hs i lam j)

private theorem continuous_physicalGenerator_c2 {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (hs : IsSmoothFieldPair ω) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) : Continuous (physicalGenerator i ω lam f) := by
  have he := funext (EinsteinFull.physicalGenerator_eq_svGenerator hs i lam hf)
  rw [he]
  exact EinsteinFull.continuous_svGenerator _ _ (fun j k => (hs.1 j k).continuous)
    (continuous_physicalDrift i ω hs lam) hf

/-- C2 convergence controls the actual differential operator, with fixed smooth coefficients. -/
private theorem dynkinMollification_generator_convergence {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (hs : IsSmoothFieldPair ω) (lam : ℝ) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hc : HasCompactSupport f) :
    TendstoLocallyUniformly (fun n => physicalGenerator i ω lam (dynkinMollification f n))
      (physicalGenerator i ω lam f) atTop := by
  obtain ⟨_, hD, hH⟩ := dynkinMollification_c2_convergence hf hc
  rw [tendstoLocallyUniformly_iff_forall_tendsto] at hD hH ⊢
  intro y
  have hDj : Tendsto (fun p : ℕ × Vec d => fderiv ℝ (dynkinMollification f p.1) p.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (fderiv ℝ f y)) :=
    (((hf.continuous_fderiv (by norm_num)).tendsto y).comp tendsto_snd).congr_uniformity
      (hD y)
  have hHj : Tendsto
      (fun p : ℕ × Vec d => fderiv ℝ (fderiv ℝ (dynkinMollification f p.1)) p.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (fderiv ℝ (fderiv ℝ f) y)) :=
    ((((hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).tendsto y).comp
      tendsto_snd).congr_uniformity (hH y)
  have hLj : Tendsto
      (fun p : ℕ × Vec d => physicalGenerator i ω lam (dynkinMollification f p.1) p.2)
      (atTop ×ˢ 𝓝 y) (𝓝 (physicalGenerator i ω lam f y)) := by
    simp_rw [physicalGenerator_c2_jet i ω hs lam
      ((dynkinMollification_smooth hf.continuous _).of_le (by norm_num)),
      physicalGenerator_c2_jet i ω hs lam hf]
    apply Tendsto.add
    · apply Tendsto.const_mul
      apply tendsto_finsetSum
      intro j _
      apply tendsto_finsetSum
      intro k _
      exact (((hs.1 j k).continuous.tendsto y).comp tendsto_snd).mul
        (((ContinuousLinearMap.apply ℝ ℝ (unitVector k)).continuous.tendsto _).comp
          (((ContinuousLinearMap.apply ℝ (Vec d →L[ℝ] ℝ) (unitVector j)).continuous.tendsto _).comp hHj))
    · apply tendsto_finsetSum
      intro j _
      exact (((continuous_physicalDrift i ω hs lam j).tendsto y).comp tendsto_snd).mul
        (((ContinuousLinearMap.apply ℝ ℝ (unitVector j)).continuous.tendsto _).comp hDj)
  exact ((((continuous_physicalGenerator_c2 i ω hs lam hf).tendsto y).comp tendsto_snd).prodMk_nhds
    hLj).mono_right (nhds_le_uniformity _)

/-- A common compact support upgrades locally uniform convergence to global convergence. -/
private theorem uniformly_of_common_compact_support {d : ℕ} {F : ℕ → Vec d → ℝ}
    {f : Vec d → ℝ} {K : Set (Vec d)} (hK : IsCompact K)
    (hF : ∀ n, Function.support (F n) ⊆ K) (hf : Function.support f ⊆ K)
    (hlim : TendstoLocallyUniformly F f atTop) : TendstoUniformly F f atTop := by
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (hlim.tendstoLocallyUniformlyOn (s := K))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) ε hε] with n hn
  intro y
  by_cases hy : y ∈ K
  · exact hn y hy
  · have hf0 : f y = 0 := Function.notMem_support.mp (fun hy' => hy (hf hy'))
    have hF0 : F n y = 0 := Function.notMem_support.mp (fun hy' => hy (hF n hy'))
    simpa only [hf0, hF0, dist_self] using hε

/-- All members of a uniformly convergent compact continuous sequence share a bound. -/
private theorem uniformly_convergent_compact_bound {d : ℕ} {F : ℕ → Vec d → ℝ}
    {f : Vec d → ℝ} (hFc : ∀ n, Continuous (F n))
    (hFk : ∀ n, HasCompactSupport (F n)) (hfc : Continuous f) (hfk : HasCompactSupport f)
    (hlim : TendstoUniformly F f atTop) : ∃ C : ℝ, ∀ n y, ‖F n y‖ ≤ C := by
  obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfk
  choose B hB using fun n => (hFc n).bounded_above_of_compact_support (hFk n)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformly_iff.mp hlim) 1 zero_lt_one)
  refine ⟨max (C + 1) (∑ n ∈ Finset.range N, max (B n) 0), fun n y => ?_⟩
  by_cases hn : N ≤ n
  · apply le_trans _ (le_max_left _ _)
    calc
      ‖F n y‖ ≤ ‖f y‖ + ‖F n y - f y‖ := norm_le_insert' _ _
      _ ≤ C + 1 := add_le_add (hC y) (by
        simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn y).le)
  · apply le_trans _ (le_max_right _ _)
    exact (hB n y).trans ((le_max_left (B n) 0).trans
      (Finset.single_le_sum (fun k _ => le_max_right (B k) 0)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))))

/-- Every compact C² compensated test of a physical martingale-problem solution is a
martingale for the right-continuous path filtration. -/
theorem physical_mp_compact_c2_rightCont_martingale :
∀ {d : ℕ} (i : Fin d) (ω : FieldPair d) (hSmooth : IsSmoothFieldPair ω)
  (lam : ℝ) (x : Vec d) (P : Measure (Path d)),
  SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
  ∀ (f : Vec d → ℝ), ContDiff ℝ (2 : ℕ∞) f → HasCompactSupport f →
  Martingale (fun (t : ℝ≥0) (γ : Path d) =>
    compensatedTest (physicalGenerator i ω lam) f t γ)
    (pathFiltration d).rightCont P := by
  intro d i ω hSmooth lam x P hP f hf hc
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨K, hK, hfK, hFK⟩ := dynkinMollification_common_support hc
  have hfc := dynkinMollification_c2_convergence hf hc
  have hfu : TendstoUniformly (dynkinMollification f) f atTop :=
    uniformly_of_common_compact_support hK
      (fun n => subset_tsupport _ |>.trans (hFK n)) (subset_tsupport _ |>.trans hfK) hfc.1
  have hLu : TendstoUniformly
      (fun n => physicalGenerator i ω lam (dynkinMollification f n))
      (physicalGenerator i ω lam f) atTop :=
    uniformly_of_common_compact_support hK
      (fun n => (gantert_physicalGenerator_support_subset i ω lam _).trans (hFK n))
      ((gantert_physicalGenerator_support_subset i ω lam f).trans hfK)
      (dynkinMollification_generator_convergence i ω hSmooth lam hf hc)
  obtain ⟨C, hC⟩ := uniformly_convergent_compact_bound
    (fun n => (dynkinMollification_smooth hf.continuous n).continuous)
    (dynkinMollification_compact hc) hf.continuous hc hfu
  obtain ⟨B, hB⟩ := uniformly_convergent_compact_bound
    (fun n => (gantert_contDiff_physicalGenerator i ω hSmooth lam
      (dynkinMollification_smooth hf.continuous n)).continuous)
    (fun n => gantert_hasCompactSupport_physicalGenerator i ω lam
      (dynkinMollification_compact hc n))
    (continuous_physicalGenerator_c2 i ω hSmooth lam hf)
    (gantert_hasCompactSupport_physicalGenerator i ω lam hc) hLu
  apply martingale_of_dominated_pointwise_limit
    (fun n => physical_mp_compact_smooth_rightCont_martingale i ω hSmooth lam x P hP
      (dynkinMollification f n) (dynkinMollification_smooth hf.continuous n)
      (dynkinMollification_compact hc n))
  · intro t γ
    have hi : Tendsto
        (fun n => ∫ s in (0 : ℝ)..(t : ℝ),
          physicalGenerator i ω lam (dynkinMollification f n) (γ s.toNNReal))
        atTop (𝓝 (∫ s in (0 : ℝ)..(t : ℝ),
          physicalGenerator i ω lam f (γ s.toNNReal))) := by
      apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
        (Eventually.of_forall fun n => ?_)
        ((hLu.comp (fun s : ℝ => γ s.toNNReal)).tendstoUniformlyOn)
      exact ((gantert_contDiff_physicalGenerator i ω hSmooth lam
        (dynkinMollification_smooth hf.continuous n)).continuous.comp
          (γ.continuous.comp continuous_real_toNNReal)).continuousOn
    exact ((hfu.tendsto_at (γ t)).sub (hfu.tendsto_at (γ 0))).sub hi
  · intro t
    refine ⟨2 * C + B * t, fun n γ => ?_⟩
    rw [Real.norm_eq_abs]
    exact EinsteinFull.abs_compensatedTest_le
      (fun y => (Real.norm_eq_abs _).symm ▸ hC n y)
      (fun y => (Real.norm_eq_abs _).symm ▸ hB n y) t γ
end EinsteinFull.Blueprint
