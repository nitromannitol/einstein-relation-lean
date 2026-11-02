import EinsteinFull.Calculus.SunaS1KilledExitContinuity
import EinsteinFull.Work.W1.GMPKilledContinuitySupport
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import EinsteinFull.Calculus.SunaS1KilledResolventIdentification
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS2KilledPointwise
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastKernel
import EinsteinFull.Calculus.SunaS6GMPEnvironment
import EinsteinFull.Calculus.U4RegularKernelSmoothing
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Topology.UniformSpace.UniformApproximation

open MeasureTheory Filter ProbabilityTheory EinsteinRelation.Diffusion
open scoped NNReal ENNReal Topology
open EinsteinRelation EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open EinsteinFull.Blueprint

namespace EinsteinFull

/-- A positive-time supplied full transition smooths a bounded killed endpoint test. -/
theorem s6_supplied_full_after_killed_continuous
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) (hs : 0 < s)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    Continuous (fun x => ∫ y, (∫ z, f z ∂gmpKilledEndpointKernel G U hU t y)
      ∂G.transitionKernel s x) := by
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  have hm : Measurable (fun y => ∫ z, f z ∂gmpKilledEndpointKernel G U hU t y) :=
    (f.continuous.stronglyMeasurable.integral_kernel
      (κ := gmpKilledEndpointKernel G U hU t)).measurable
  have hb (y : Vec d) :
      |∫ z, f z ∂gmpKilledEndpointKernel G U hU t y| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_gmpKilledEndpointKernel_le G U hU t y f ‖f‖ (norm_nonneg _)
        (fun z => f.norm_coe_le_norm z)
  rw [s6_supplied_gmp_transition_eq_canonical_unconditional hd ω lam L hL hω h0 h1 G s]
  exact u4_regular_signed_kernel_strongFeller hd ω lam L hL hω s hs _ hm ‖f‖ hb

/-- The killed semigroup differs from the full-then-killed average by at most
its bounded test norm times the probability of an early exit. -/
theorem s6_killed_full_approx_error_le_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) (x : Vec d)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    |(∫ z, f z ∂gmpKilledEndpointKernel G U hU (s + t) x) -
      ∫ y, (∫ z, f z ∂gmpKilledEndpointKernel G U hU t y)
        ∂G.transitionKernel s x| ≤
      ‖f‖ * ((G.pathLaw x) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal := by
  let := G.pathLaw_isMarkovKernel
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  let g : Vec d → ℝ := fun y => ∫ z, f z ∂gmpKilledEndpointKernel G U hU t y
  have hg : Measurable g :=
    (f.continuous.stronglyMeasurable.integral_kernel
      (κ := gmpKilledEndpointKernel G U hU t)).measurable
  have hb (y : Vec d) : ‖g y‖ ≤ ‖f‖ :=
    norm_integral_gmpKilledEndpointKernel_le G U hU t y f ‖f‖ (norm_nonneg _)
      (fun z => f.norm_coe_le_norm z)
  have hs : MeasurableSet {γ : Path d | (s : ℝ≥0∞) < localityExitTime U γ} :=
    measurableSet_lt measurable_const (measurable_localityExitTime U hU)
  have hi : Integrable (fun γ : Path d => g (γ s)) (G.pathLaw x) :=
    Integrable.of_bound (hg.comp (measurable_pathPosition s)).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall fun γ => hb (γ s))
  have he := norm_integral_sub_setIntegral_le
    (μ := G.pathLaw x) (f := fun γ : Path d => g (γ s))
    (Filter.Eventually.of_forall fun γ => hb (γ s)) hs hi
  rw [integral_gmpKilledEndpointKernel_add G U hU s t x f f.continuous ‖f‖
    (fun z => by simpa only [← Real.norm_eq_abs] using f.norm_coe_le_norm z)]
  change |(∫ y, g y ∂gmpKilledEndpointKernel G U hU s x) -
    ∫ y, g y ∂G.transitionKernel s x| ≤ _
  rw [integral_gmpKilledEndpointKernel G U hU s x g hg, ← G.pathLaw_endpoint s x,
    integral_map (measurable_pathPosition s).aemeasurable hg.aestronglyMeasurable,
    integral_indicator hs]
  simpa only [Real.norm_eq_abs, abs_sub_comm, Set.compl_ofPred, not_lt, Measure.real, mul_comm, pathPosition]
    using he

/-- Locally uniform killed/full approximation yields continuity of the actual killed test. -/
theorem s6_supplied_killed_endpoint_continuousOn_of_local_approx
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (happrox : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      ∀ᶠ y in 𝓝[U] x,
        |(∫ z, f z ∂gmpKilledEndpointKernel G U hU t y) -
          ∫ z, (∫ w, f w ∂gmpKilledEndpointKernel G U hU (t - s) z)
            ∂G.transitionKernel s y| < ε) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U := by
  apply continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  intro x hx v hv
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_uniformity_dist.mp hv
  obtain ⟨s, hs, _, hnear⟩ := happrox x hx ε hε
  refine ⟨_, hnear, _, (s6_supplied_full_after_killed_continuous hd L hL ω hω lam h0 h1
    G U hU s (t - s) hs f).continuousWithinAt, ?_⟩
  intro y hy
  apply hεv
  simpa only [Real.dist_eq, Set.mem_setOf_eq, abs_sub_comm] using hy

/-- Local uniform control of early exit gives continuity of the killed endpoint test. -/
theorem s6_supplied_killed_endpoint_continuousOn_of_local_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (hexit : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      ∀ᶠ y in 𝓝[U] x,
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U := by
  apply s6_supplied_killed_endpoint_continuousOn_of_local_approx hd L hL ω hω lam h0 h1 G U hU t f
  intro x hx ε hε
  have hb : 0 < ‖f‖ + 1 := by positivity
  obtain ⟨s, hs, hst, hnear⟩ := hexit x hx (ε / (‖f‖ + 1)) (div_pos hε hb)
  refine ⟨s, hs, hst, ?_⟩
  filter_upwards [hnear] with y hy
  have he := s6_killed_full_approx_error_le_exit hd L hL ω hω lam h0 h1
    G U hU s (t - s) y f
  rw [add_tsub_cancel_of_le hst.le] at he
  have hp : 0 ≤ ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal :=
    ENNReal.toReal_nonneg
  have hdiv : ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal *
      (‖f‖ + 1) < ε := (lt_div_iff₀ hb).mp hy
  nlinarith [norm_nonneg f]

/-- A uniform exit estimate on a Euclidean neighborhood supplies the local
approximation hypothesis at any positive time. -/
theorem s6_local_exit_of_uniform_estimate
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (t : ℝ≥0) (ht : 0 < t)
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      ∀ᶠ y in 𝓝[U] x,
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε := by
  intro x hx ε hε
  obtain ⟨δ, ρ, hδ, hρ, hbound⟩ := hlocal x hx ε hε
  let s : ℝ≥0 := min (t / 2) (Real.toNNReal (δ / 2))
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min (by positivity) (Real.toNNReal_pos.mpr (by linarith))
  have hst : s < t := by
    have h := min_le_left (t / 2) (Real.toNNReal (δ / 2))
    dsimp only [s]
    linarith
  have hsδ : (s : ℝ) < δ := by
    have h : (s : ℝ) ≤ (Real.toNNReal (δ / 2) : ℝ) := by
      exact_mod_cast (min_le_right (t / 2) (Real.toNNReal (δ / 2)))
    rw [Real.coe_toNNReal _ (by linarith : 0 ≤ δ / 2)] at h
    linarith
  have hnorm : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hnear : ∀ᶠ y in 𝓝 x, euclideanNorm (y - x) < ρ := by
    have hc : ContinuousAt (fun y : Vec d => euclideanNorm (y - x)) x :=
      (hnorm.comp (continuous_id.sub continuous_const)).continuousAt
    have hρzero : ∀ᶠ z : ℝ in 𝓝 (0 : ℝ), z < ρ := Iio_mem_nhds hρ
    have hρn : ∀ᶠ z : ℝ in 𝓝 ((fun y : Vec d => euclideanNorm (y - x)) x), z < ρ := by
      simpa [euclideanNorm, euclideanSq, dot] using hρzero
    exact hc.eventually hρn
  refine ⟨s, hs, hst, ?_⟩
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with y hy
  exact hbound y hy s hsδ

/-- A geometric local exit estimate yields positive-time continuity of killed tests. -/
theorem s6_supplied_killed_endpoint_continuousOn_of_uniform_estimate
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U :=
  s6_supplied_killed_endpoint_continuousOn_of_local_exit hd L hL ω hω lam h0 h1
    G U hU t f (s6_local_exit_of_uniform_estimate hd L hL ω hω lam h0 h1 G U t ht hlocal)

/-- At time zero, killed endpoint tests are continuous inside the domain. -/
theorem s6_supplied_killed_endpoint_continuousOn_zero
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (f : BoundedContinuousFunction (Vec d) ℝ) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU 0 x) U := by
  apply f.continuous.continuousOn.congr
  intro x hx
  change (∫ y, f y ∂gmpKilledEndpointKernel G U hU 0 x) = f x
  rw [gmpKilledEndpointKernel_zero G U hU x, Set.indicator_of_mem hx, integral_dirac]

/-- Geometric local exit control gives killed-test continuity at every time. -/
theorem s6_supplied_killed_endpoint_continuousOn_of_uniform_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U := by
  by_cases ht : 0 < t
  · exact s6_supplied_killed_endpoint_continuousOn_of_uniform_estimate hd L hL ω hω
      lam h0 h1 G U hU t ht f hlocal
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) (bot_le : 0 ≤ t)
    subst t
    exact s6_supplied_killed_endpoint_continuousOn_zero hd L hL ω hω lam h0 h1 G U hU f

/-- Almost-everywhere equality of continuous killed endpoint tests extends to every
starting point in the open domain. -/
theorem s6_supplied_killed_endpoint_eq_of_ae_continuous
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (he : ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x))
    (hc : ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) U ∧
      ContinuousOn (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) U) :
    ∀ x ∈ U, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  intro x hx
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  let := isFiniteKernel_gmpKilledEndpointKernel G' U hU t
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (he f)) hU
    (hc f).1 (hc f).2 hx


/-- Locally uniform short-time exit control upgrades almost-everywhere equality
of killed endpoint tests to equality of killed endpoint laws at every interior start. -/
theorem s6_supplied_killed_endpoint_eq_of_ae_local_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (he : ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x))
    (hexit : 0 < t → ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      ∀ᶠ y in 𝓝[U] x,
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε)
    (hexit' : 0 < t → ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      ∀ᶠ y in 𝓝[U] x,
        ((G'.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ∀ x ∈ U, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  apply s6_supplied_killed_endpoint_eq_of_ae_continuous hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU t he
  intro f
  by_cases ht : 0 < t
  · exact ⟨s6_supplied_killed_endpoint_continuousOn_of_local_exit hd L hL ω hω lam h0 h1
      G U hU t f (hexit ht),
      s6_supplied_killed_endpoint_continuousOn_of_local_exit hd L hL ω' hω' lam h0 h1
        G' U hU t f (hexit' ht)⟩
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) (bot_le : 0 ≤ t)
    subst t
    exact ⟨s6_supplied_killed_endpoint_continuousOn_zero hd L hL ω hω lam h0 h1 G U hU f,
      s6_supplied_killed_endpoint_continuousOn_zero hd L hL ω' hω' lam h0 h1 G' U hU f⟩

/-- A geometric exit estimate for each environment supplies the every-start comparison. -/
theorem s6_supplied_killed_endpoint_eq_of_ae_uniform_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (he : ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x))
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε)
    (hlocal' : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G'.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ∀ x ∈ U, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  apply s6_supplied_killed_endpoint_eq_of_ae_continuous hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU t he
  intro f
  exact ⟨s6_supplied_killed_endpoint_continuousOn_of_uniform_exit hd L hL ω hω
      lam h0 h1 G U hU t f hlocal,
    s6_supplied_killed_endpoint_continuousOn_of_uniform_exit hd L hL ω' hω'
      lam h0 h1 G' U hU t f hlocal'⟩


/-- At time zero the supplied killed endpoint tests agree for all starting points. -/
theorem s6_supplied_killed_endpoint_eq_zero_time
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    (∫ y, f y ∂gmpKilledEndpointKernel G U hU 0 x) =
      ∫ y, f y ∂gmpKilledEndpointKernel G' U hU 0 x := by
  rw [gmpKilledEndpointKernel_zero G U hU x, gmpKilledEndpointKernel_zero G' U hU x]


/-- Supplied killed endpoint tests agree at any start outside the domain. -/
theorem s6_supplied_killed_endpoint_eq_of_notMem
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (x : Vec d) (hx : x ∉ U)
    (f : BoundedContinuousFunction (Vec d) ℝ) :
    (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =
      ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x := by
  rw [gmpKilledEndpointKernel_eq_zero_of_notMem G U hU t x hx,
    gmpKilledEndpointKernel_eq_zero_of_notMem G' U hU t x hx]


/-- An almost-everywhere interior comparison extends across the killed exterior. -/
theorem s6_supplied_killed_endpoint_ae_eq_of_interior
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : BoundedContinuousFunction (Vec d) ℝ)
    (hinterior : (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume.restrict U]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x)) :
    (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) := by
  filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hinterior] with x hx
  by_cases hxU : x ∈ U
  · exact hx hxU
  · exact s6_supplied_killed_endpoint_eq_of_notMem G G' U hU t x hxU f


/-- The almost-everywhere killed endpoint comparison holds at time zero. -/
theorem s6_supplied_killed_endpoint_ae_eq_zero_time
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω ω' : FieldPair d}
    {hω : IsRegular L ω} {hω' : IsRegular L ω'} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) :
    ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU 0 x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU 0 x) := by
  intro f
  exact Filter.Eventually.of_forall (fun x =>
    s6_supplied_killed_endpoint_eq_zero_time G G' U hU x f)

/-- Finite-measure comparisons extend to all bounded continuous endpoint tests. -/
theorem s6_supplied_killed_endpoint_ae_eq_of_finite_sets
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (hfinite : ∀ s : Set (Vec d), MeasurableSet s → s ⊆ U →
      physicalReversibleMeasure ω hd lam s ≠ ∞ →
      (fun x => gmpKilledEndpointKernel G U hU t x s) =ᵐ[volume]
        (fun x => gmpKilledEndpointKernel G' U hU t x s)) :
    ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) := by
  let μ := physicalReversibleMeasure ω hd lam
  let : IsLocallyFiniteMeasure μ :=
    densityWeightedMeasure_locallyFinite _ (physicalReversibleDensity_continuous ω hd lam)
  have hsets (s : Set (Vec d)) (hs : MeasurableSet s) :
      (fun x => gmpKilledEndpointKernel G U hU t x s) =ᵐ[volume]
        (fun x => gmpKilledEndpointKernel G' U hU t x s) := by
    let a : ℕ → Set (Vec d) := fun n => (U ∩ s) ∩ spanningSets μ n
    have ha (n : ℕ) : MeasurableSet (a n) :=
      (hU.measurableSet.inter hs).inter (measurableSet_spanningSets μ n)
    have hmono : Monotone a := fun i j hij =>
      Set.inter_subset_inter_right _ (monotone_spanningSets μ hij)
    have hcover : ⋃ n, a n = U ∩ s := by
      simp only [a, ← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
    have heach (n : ℕ) :
        (fun x => gmpKilledEndpointKernel G U hU t x (a n)) =ᵐ[volume]
          (fun x => gmpKilledEndpointKernel G' U hU t x (a n)) :=
      hfinite (a n) (ha n) (fun _ hy => hy.1.1)
        ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
    filter_upwards [ae_all_iff.mpr heach] with x hx
    have hinter : gmpKilledEndpointKernel G U hU t x (U ∩ s) =
        gmpKilledEndpointKernel G' U hU t x (U ∩ s) := by
      rw [← hcover, hmono.measure_iUnion, hmono.measure_iUnion]
      exact iSup_congr hx
    rw [Measure.measure_inter_eq_of_ae (gmpKilledEndpointKernel_ae_mem G U hU t x),
      Measure.measure_inter_eq_of_ae (gmpKilledEndpointKernel_ae_mem G' U hU t x)] at hinter
    exact hinter
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet (Vec d))
  have hC : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hgen : (by infer_instance : MeasurableSpace (Vec d)) = MeasurableSpace.generateFrom C := by
    change _ = MeasurableSpace.generateFrom
      (generateSetAlgebra (MeasurableSpace.countableGeneratingSet (Vec d)))
    rw [generateFrom_generateSetAlgebra_eq, MeasurableSpace.generateFrom_countableGeneratingSet]
  have hCmeas {s : Set (Vec d)} (hs : s ∈ C) : MeasurableSet s := by
    induction hs using generateSetAlgebra_induction with
    | base a ha => exact MeasurableSpace.measurableSet_countableGeneratingSet ha
    | empty => exact MeasurableSet.empty
    | compl a _ ha => exact ha.compl
    | union a b _ _ ha hb => exact ha.union hb
  have hall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ s ∈ C,
      gmpKilledEndpointKernel G U hU t x s = gmpKilledEndpointKernel G' U hU t x s :=
    (eventually_countable_ball hC).mpr (fun s hs => hsets s (hCmeas hs))
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  have hkernel : gmpKilledEndpointKernel G U hU t =ᵐ[volume]
      gmpKilledEndpointKernel G' U hU t := by
    filter_upwards [hall, hsets Set.univ MeasurableSet.univ] with x hx hxuniv
    exact ext_of_generate_finite C hgen
      isSetAlgebra_generateSetAlgebra.isSetRing.isSetSemiring.isPiSystem hx hxuniv
  intro f
  filter_upwards [hkernel] with x hx
  rw [hx]

/-- The supplied killed unit resolvent is the physical variational resolvent. -/
theorem s6_supplied_killed_unit_resolvent_eq
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (gmpKilledInteriorSemigroup G U hU).resolvent ⟨(1 : ℝ), Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)⟩ f =
      physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω zero_lt_one f := by
  apply Subtype.ext
  have h := (s1_killed_Laplace_eq_interior_resolvent hd L hL ω hω lam h0 h1
    G U hU 1 zero_lt_one f.val).symm.trans
      (s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent hd L hL ω hω lam h0 h1
        G U hU 1 zero_lt_one f.val)
  have hp : physicalZeroBoundaryProjection U hd ω lam L hω f.val = f.val :=
    (physicalZeroBoundaryL2 U hd ω lam L hω).starProjection_mem_subspace_eq_self f
  have hgraph := physicalZeroBoundaryResolventGraph_toLp U hd ω lam L 1 hL hω
    zero_lt_one (f.val : Vec d → ℝ) (Lp.memLp f.val)
  rw [Lp.toLp_coeFn] at hgraph
  simpa only [hp, physicalZeroBoundaryInteriorResolvent_coe,
    physicalZeroBoundaryResolventL2, ContinuousLinearMap.comp_apply,
    hgraph, gmpKilledInteriorResolvent] using h

/-- The actual supplied killed evolution agrees with the physical interior evolution. -/
theorem s6_supplied_killed_interior_evolution_eq
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) :
    ∀ (t : ℝ≥0) (f : physicalZeroBoundaryL2 U hd ω lam L hω),
      gmpKilledInteriorSemigroup G U hU t f =
        physicalZeroBoundaryEvolution U hd ω lam L hL hω t f := by
  intro t f
  let S := gmpKilledInteriorSemigroup G U hU
  let T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (physicalZeroBoundaryL2 U hd ω lam L hω) := {
    operator := physicalZeroBoundaryEvolution U hd ω lam L hL hω
    operator_zero := physicalZeroBoundaryEvolution_zero U hd ω lam L hL hω
    operator_add := physicalZeroBoundaryEvolution_add U hd ω lam L hL hω
    opNorm_le_one := norm_physicalZeroBoundaryEvolution_le U hd ω lam L hL hω
    continuous_orbit := continuous_physicalZeroBoundaryEvolution_apply U hd ω lam L hL hω }
  let μ : MarkovProcess.Semigroup.PositiveShift := ⟨(1 : ℝ), Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)⟩
  have hR (g : physicalZeroBoundaryL2 U hd ω lam L hω) :
      S.resolvent μ g = physicalZeroBoundaryInteriorResolvent U hd ω lam L 1 hL hω
        zero_lt_one g := s6_supplied_killed_unit_resolvent_eq hd L hL ω hω lam h0 h1 G U hU g
  have hforward (z : S.generatorDomain) :
      Tendsto (fun r : ℝ≥0 => (r : ℝ)⁻¹ • (T r z.val - z.val))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (S.generator z)) := by
    let g := z.val - S.generator z
    have hz : S.resolvent μ g = z.val := by
      simpa only [g, μ, one_smul] using S.resolvent_smul_sub_generator ⟨(1 : ℝ), Set.mem_Ioi.mpr (show (0 : ℝ) < 1 from zero_lt_one)⟩ z
    have hg : S.generator z = z.val - g := by simp only [g, sub_sub_cancel]
    rw [hg, ← hz, hR]
    exact tendsto_physicalZeroBoundaryEvolution_slope_resolvent U hd ω lam L hL hω g
  have hdom : S.generatorDomain = T.generatorDomain := by
    ext z
    constructor
    · intro hz
      exact T.mem_generatorDomain_of_tendsto (hforward ⟨z, hz⟩)
    · intro hz
      have hp := (tendsto_physicalZeroBoundaryEvolution_slope_iff
        U hd ω lam L hL hω z (T.generator ⟨z, hz⟩)).mp (T.tendsto_generator' ⟨z, hz⟩)
      have he := (isPhysicalZeroBoundaryGeneratorPair_iff_resolvent
        U hd ω lam L hL hω z (T.generator ⟨z, hz⟩)).mp hp
      rw [← hR] at he
      exact he ▸ S.resolvent_mem_generatorDomain μ (z - T.generator ⟨z, hz⟩)
  have heq : S = T := S.ext_of_generator T hdom (fun z hzS hzT =>
    (T.generator_eq_of_tendsto ⟨z, hzT⟩ (hforward ⟨z, hzS⟩)).symm)
  exact congrArg (fun A => A t f) heq

/-- Interior evolution identification gives the finite-set comparison required by
`s6_supplied_killed_endpoint_ae_eq_of_finite_sets`. -/
theorem s6_supplied_killed_endpoint_finite_sets_of_evolution
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0)
    (hG : ∀ f : physicalZeroBoundaryL2 U hd ω lam L hω,
      gmpKilledInteriorSemigroup G U hU t f =
        physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)
    (hG' : ∀ f : physicalZeroBoundaryL2 U hd ω' lam L hω',
      gmpKilledInteriorSemigroup G' U hU t f =
        physicalZeroBoundaryEvolution U hd ω' lam L hL hω' t f) :
    ∀ s : Set (Vec d), MeasurableSet s → s ⊆ U →
      physicalReversibleMeasure ω hd lam s ≠ ∞ →
      (fun x => gmpKilledEndpointKernel G U hU t x s) =ᵐ[volume]
        (fun x => gmpKilledEndpointKernel G' U hU t x s) := by
  classical
  intro s hs hsU hfin
  have hm : physicalReversibleMeasure ω hd lam s = physicalReversibleMeasure ω' hd lam s := by
    have h := congrArg (fun μ : Measure (Vec d) => μ s)
      (physicalReversibleMeasure_restrict_eq_of_physical_eqOn U hU.measurableSet ω ω' hag hd lam)
    simpa only [Measure.restrict_apply hs, Set.inter_eq_left.mpr hsU] using h
  let f : Vec d → ℝ := s.indicator (fun _ => (1 : ℝ))
  have hf : MemLp f 2 (physicalReversibleMeasure ω hd lam) :=
    memLp_indicator_const 2 hs 1 (Or.inr hfin)
  have hf' : MemLp f 2 (physicalReversibleMeasure ω' hd lam) :=
    memLp_indicator_const 2 hs 1 (Or.inr (hm ▸ hfin))
  have hsupp : ∀ y ∉ U, f y = 0 := fun y hy =>
    Set.indicator_of_notMem (fun hys => hy (hsU hys)) _
  let f₁ : physicalZeroBoundaryL2 U hd ω lam L hω := ⟨hf.toLp f,
    (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω _).mpr (by
      filter_upwards [hf.coeFn_toLp] with y hy hyU
      exact hy.trans (hsupp y hyU))⟩
  let f₂ : physicalZeroBoundaryL2 U hd ω' lam L hω' := ⟨hf'.toLp f,
    (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω' lam L hω' _).mpr (by
      filter_upwards [hf'.coeFn_toLp] with y hy hyU
      exact hy.trans (hsupp y hyU))⟩
  have hvol {η : FieldPair d} {p : Vec d → Prop} :
      (∀ᵐ y ∂physicalReversibleMeasure η hd lam, p y) ↔ ∀ᵐ y ∂(volume : Measure (Vec d)), p y :=
    ae_withDensity_iff_volume_of_continuous_pos (physicalReversibleDensity η hd lam)
      (physicalReversibleDensity_continuous η hd lam) (physicalReversibleDensity_pos η hd lam) _
  have hf₁ : f₁.val =ᵐ[volume] f := hvol.mp hf.coeFn_toLp
  have hf₂ : f₂.val =ᵐ[volume] f := hvol.mp hf'.coeFn_toLp
  have hfg : f₁.val =ᵐ[volume] f₂.val := hf₁.trans hf₂.symm
  have h₁ : (gmpKilledInteriorSemigroup G U hU t f₁).val =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) := by
    apply hvol.mp
    filter_upwards [gmpKilledL2_ae_eq G U hU t f₁.val,
      ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hf.coeFn_toLp] with x hx hy
    exact hx.trans (integral_congr_ae hy)
  have h₂ : (gmpKilledInteriorSemigroup G' U hU t f₂).val =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) := by
    apply hvol.mp
    filter_upwards [gmpKilledL2_ae_eq G' U hU t f₂.val,
      ae_ae_gmpKilledEndpointKernel_of_ae G' U hU t hf'.coeFn_toLp] with x hx hy
    exact hx.trans (integral_congr_ae hy)
  have hevol : (gmpKilledInteriorSemigroup G U hU t f₁).val =ᵐ[volume]
      (gmpKilledInteriorSemigroup G' U hU t f₂).val := by
    rw [hG f₁, hG' f₂]
    exact physicalZeroBoundaryEvolution_ae_eq_of_physical_eqOn U hU.measurableSet hd
      ω ω' hag lam L L hL hL hω hω' t f₁ f₂ hfg
  have h := h₁.symm.trans (hevol.trans h₂)
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  let := isFiniteKernel_gmpKilledEndpointKernel G' U hU t
  filter_upwards [h] with x hx
  have hx' : (gmpKilledEndpointKernel G U hU t x s).toReal =
      (gmpKilledEndpointKernel G' U hU t x s).toReal := by
    simpa only [f, integral_indicator hs, integral_const, smul_eq_mul, mul_one,
      Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hx
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hx'

/-- Identifying both actual killed evolutions gives local endpoint comparison. -/
theorem s6_supplied_killed_endpoint_ae_eq_of_evolution
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0)
    (hG : ∀ f : physicalZeroBoundaryL2 U hd ω lam L hω,
      gmpKilledInteriorSemigroup G U hU t f =
        physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)
    (hG' : ∀ f : physicalZeroBoundaryL2 U hd ω' lam L hω',
      gmpKilledInteriorSemigroup G' U hU t f =
        physicalZeroBoundaryEvolution U hd ω' lam L hL hω' t f) :
    ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) := by
  exact s6_supplied_killed_endpoint_ae_eq_of_finite_sets hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU t
    (s6_supplied_killed_endpoint_finite_sets_of_evolution hd L hL ω ω' hω hω'
      lam h0 h1 G G' U hU hag t hG hG')

/-- Local evolution and uniform exit estimates give every-interior-start equality. -/
theorem s6_supplied_killed_endpoint_eq_of_evolution_uniform_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0)
    (hG : ∀ f : physicalZeroBoundaryL2 U hd ω lam L hω,
      gmpKilledInteriorSemigroup G U hU t f =
        physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)
    (hG' : ∀ f : physicalZeroBoundaryL2 U hd ω' lam L hω',
      gmpKilledInteriorSemigroup G' U hU t f =
        physicalZeroBoundaryEvolution U hd ω' lam L hL hω' t f)
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε)
    (hlocal' : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G'.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ∀ x ∈ U, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  apply s6_supplied_killed_endpoint_eq_of_ae_uniform_exit hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU t
  · exact s6_supplied_killed_endpoint_ae_eq_of_evolution hd L hL ω ω' hω hω'
      lam h0 h1 G G' U hU hag t hG hG'
  · exact hlocal
  · exact hlocal'

/-- Agreement of both coefficients on the open set gives almost-everywhere
agreement of the supplied killed endpoint integrals. -/
theorem s6_supplied_killed_endpoint_ae_eq_of_local_coefficients
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0) :
    ∀ f : BoundedContinuousFunction (Vec d) ℝ,
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =ᵐ[volume]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G' U hU t x) :=
  s6_supplied_killed_endpoint_ae_eq_of_evolution hd L hL ω ω' hω hω' lam h0 h1
    G G' U hU hag t (s6_supplied_killed_interior_evolution_eq hd L hL ω hω lam h0 h1 G U hU t)
    (s6_supplied_killed_interior_evolution_eq hd L hL ω' hω' lam h0 h1 G' U hU t)

/-- Local coefficient agreement and uniform exit control identify killed laws at every start. -/
theorem s6_supplied_killed_endpoint_eq_of_local_coefficients_uniform_exit
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0)
    (hlocal : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε)
    (hlocal' : ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      ∀ y : Vec d, euclideanNorm (y - x) < ρ → ∀ s : ℝ≥0, (s : ℝ) < δ →
        ((G'.pathLaw y) {γ | localityExitTime U γ ≤ (s : ℝ≥0∞)}).toReal < ε) :
    ∀ x : Vec d, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  intro x
  by_cases hx : x ∈ U
  · exact s6_supplied_killed_endpoint_eq_of_ae_uniform_exit hd L hL ω ω' hω hω'
      lam h0 h1 G G' U hU t
      (s6_supplied_killed_endpoint_ae_eq_of_local_coefficients hd L hL ω ω' hω hω'
        lam h0 h1 G G' U hU hag t) hlocal hlocal' x hx
  · rw [gmpKilledEndpointKernel_eq_zero_of_notMem G U hU t x hx,
      gmpKilledEndpointKernel_eq_zero_of_notMem G' U hU t x hx]

theorem s6_supplied_killed_endpoint_eq_of_local_coefficients
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0) :
    ∀ x : Vec d, gmpKilledEndpointKernel G U hU t x =
      gmpKilledEndpointKernel G' U hU t x := by
  apply s6_supplied_killed_endpoint_eq_of_local_coefficients_uniform_exit
    hd L hL ω ω' hω hω' lam h0 h1 G G' U hU hag t
  · exact fun x hx ε hε =>
      s1_supplied_killed_exit_probability_locally_uniform hd L hL ω hω lam h0 h1
        G U hU x hx ε hε
  · exact fun x hx ε hε =>
      s1_supplied_killed_exit_probability_locally_uniform hd L hL ω' hω' lam h0 h1
        G' U hU x hx ε hε


/-- Equality of killed kernels gives the strict-survival marginals used by S7. -/
theorem s6_supplied_killed_marginals_of_endpoint_eq
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hk : ∀ (t : ℝ≥0) (x : Vec d), x ∈ U →
      gmpKilledEndpointKernel G U hU t x = gmpKilledEndpointKernel G' U hU t x) :
    ∀ (t : ℝ≥0) (x : Vec d), x ∈ U → ∀ A : Set (Vec d), MeasurableSet A →
      (G.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      (G'.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
  intro t x hx A hA
  have heval (R : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1) :
      gmpKilledEndpointKernel R U hU t x A =
        (R.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
    rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t) hA,
      Measure.restrict_apply (hA.preimage (measurable_pathPosition t))]
    congr 1
    ext γ
    exact and_comm
  have heval' : gmpKilledEndpointKernel G' U hU t x A =
      (G'.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
    rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t) hA,
      Measure.restrict_apply (hA.preimage (measurable_pathPosition t))]
    congr 1
    ext γ
    exact and_comm
  rw [← heval G, ← heval']
  exact congrArg (fun μ => μ A) (hk t x hx)

/-- Local coefficients give the strict-survival marginals required by S7. -/
theorem s6_supplied_killed_marginals_of_local_coefficients
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω ω' : FieldPair d)
    (hω : IsRegular L ω) (hω' : IsRegular L ω') (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd L hL ω' hω' lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hag : ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) :
    ∀ (t : ℝ≥0) (x : Vec d), x ∈ U → ∀ A : Set (Vec d), MeasurableSet A →
      (G.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} =
      (G'.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ ∧ γ t ∈ A} := by
  apply s6_supplied_killed_marginals_of_endpoint_eq hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU
  intro t x _
  exact s6_supplied_killed_endpoint_eq_of_local_coefficients hd L hL ω ω' hω hω'
    lam h0 h1 G G' U hU hag t x



/-- Physical coefficient agreement on a halfspace identifies the supplied
reduced killed endpoint kernels at every starting point. -/
theorem s6_reduced_halfspace_killed_endpoint_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (lam a : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0 h1)
    (hag : ∀ y : Vec d, y (Regeneration.Renewal.forceCoord hd) ≤ a →
      ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) (t : ℝ≥0) :
    ∀ x : Vec d,
      gmpKilledEndpointKernel G {z | z (Regeneration.Renewal.forceCoord hd) < a}
        (isOpen_lt (continuous_apply _) continuous_const) t x =
      gmpKilledEndpointKernel G' {z | z (Regeneration.Renewal.forceCoord hd) < a}
        (isOpen_lt (continuous_apply _) continuous_const) t x := by
  let U : Set (Vec d) := {z | z (Regeneration.Renewal.forceCoord hd) < a}
  have hU : IsOpen U := isOpen_lt (continuous_apply _) continuous_const
  apply s6_supplied_killed_endpoint_eq_of_local_coefficients hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0 h1 G G' U hU
  exact zeroPotentialReducedPair_eqOn_of_physical_eqOn U ω ω'
    (fun y hy => hag y (le_of_lt hy))

/-- The corresponding halfspace killed laws agree on strict-survival endpoint events. -/
theorem s6_reduced_halfspace_killed_marginals_eq
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (lam a : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0 h1)
    (G' : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
      (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0 h1)
    (hag : ∀ y : Vec d, y (Regeneration.Renewal.forceCoord hd) ≤ a →
      ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) :
    ∀ (t : ℝ≥0) (x : Vec d), x (Regeneration.Renewal.forceCoord hd) < a →
      ∀ A : Set (Vec d), MeasurableSet A →
      (G.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime
        {z | z (Regeneration.Renewal.forceCoord hd) < a} γ ∧ γ t ∈ A} =
      (G'.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime
        {z | z (Regeneration.Renewal.forceCoord hd) < a} γ ∧ γ t ∈ A} := by
  let U : Set (Vec d) := {z | z (Regeneration.Renewal.forceCoord hd) < a}
  have hU : IsOpen U := isOpen_lt (continuous_apply _) continuous_const
  apply s6_supplied_killed_marginals_of_local_coefficients hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound hΛ₀) _ _ hω hω' lam h0 h1 G G' U hU
  exact zeroPotentialReducedPair_eqOn_of_physical_eqOn U ω ω'
    (fun y hy => hag y (le_of_lt hy))

end EinsteinFull
