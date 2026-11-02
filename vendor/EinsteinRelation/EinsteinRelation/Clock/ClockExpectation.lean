import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Clock.PhysicalClock
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Expected physical clock and its long-time rate

`paper/main.tex`, lines 1185–1186. For the annealed joint law `J` of the environment and the
path from the origin, the expected clock is the time integral of the expected observed
density: `E[A(t)] = ∫_0^t E[μ(ω_u)] du`. An almost-sure rate `A(t)/t → η` then transfers to
`E[A(t)]/t → η` by dominated convergence, once the clock is bounded along every path.

The clock is `physicalPathClock`, the observed density at time `u` is the origin value of
`reducedObservationAt u`, and the joint law is `annealedCoordinateJoint`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open EinsteinRelation.Carriers (annealedCoordinateJoint reducedObservationAt)
open EinsteinRelation.Probability.ValidAnnealedLawSupport
  (annealedJointOnProbabilityFibers_isProbabilityMeasure annealedJointOnProbabilityFibers_lintegral)

namespace EinsteinRelation.Clock

/-- The observed density at the origin is the clock density at the path position. -/
theorem clockDensity_obs {d : ℕ} (t : ℝ≥0) (z : FieldPair d × Path d) :
    (reducedObservationAt t z).2 0 = clockDensity z.1 (pathPosition t z.2) := by
  change clockDensity (translate (pathPosition t z.2) z.1) 0 =
    clockDensity z.1 (pathPosition t z.2)
  simp only [clockDensity, translate_scalar, add_zero]

/-- The clock density along a fixed environment and path is continuous in time. -/
theorem continuous_clockDensity_along {d : ℕ} (ω : FieldPair d) (γ : Path d) :
    Continuous fun u : ℝ => clockDensity ω (γ u.toNNReal) := by
  show Continuous fun u : ℝ => Real.exp (-2 * ω.2 (γ u.toNNReal))
  exact Real.continuous_exp.comp
    (continuous_const.mul (ω.2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)))

/-- The clock density at a fixed time is continuous in the environment-path pair. -/
theorem continuous_clockDensity_at {d : ℕ} (s : ℝ≥0) :
    Continuous fun z : FieldPair d × Path d => clockDensity z.1 (pathPosition s z.2) := by
  have h1 : Continuous fun z : FieldPair d × Path d => z.1.2 :=
    continuous_snd.comp continuous_fst
  have h2 : Continuous fun z : FieldPair d × Path d => z.2 s :=
    (continuous_eval_const s).comp continuous_snd
  show Continuous fun z : FieldPair d × Path d => Real.exp (-2 * z.1.2 (z.2 s))
  exact Real.continuous_exp.comp (continuous_const.mul (h1.eval h2))

/-- The clock density along a path is jointly continuous in the environment-path pair and time. -/
theorem continuous_clockDensity_path_time {d : ℕ} :
    Continuous fun q : (FieldPair d × Path d) × ℝ =>
      clockDensity q.1.1 (pathPosition q.2.toNNReal q.1.2) := by
  have hγ : Continuous fun q : (FieldPair d × Path d) × ℝ => q.1.2 :=
    continuous_snd.comp continuous_fst
  have ht : Continuous fun q : (FieldPair d × Path d) × ℝ => q.2.toNNReal :=
    continuous_real_toNNReal.comp continuous_snd
  have hfield : Continuous fun q : (FieldPair d × Path d) × ℝ => q.1.1.2 :=
    continuous_snd.comp (continuous_fst.comp continuous_fst)
  have hval : Continuous fun q : (FieldPair d × Path d) × ℝ => q.1.2 q.2.toNNReal :=
    hγ.eval ht
  have hdens : Continuous fun q : (FieldPair d × Path d) × ℝ =>
      q.1.1.2 (q.1.2 q.2.toNNReal) :=
    hfield.eval hval
  show Continuous fun q : (FieldPair d × Path d) × ℝ =>
    Real.exp (-2 * q.1.1.2 (q.1.2 q.2.toNNReal))
  exact Real.continuous_exp.comp (continuous_const.mul hdens)

/-- The same joint continuity with time as the first coordinate. -/
theorem continuous_clockDensity_time_path {d : ℕ} :
    Continuous fun p : ℝ × (FieldPair d × Path d) =>
      clockDensity p.2.1 (pathPosition p.1.toNNReal p.2.2) :=
  continuous_clockDensity_path_time.comp continuous_swap

/-- The integrated clock at a fixed time is continuous in the environment-path pair. -/
theorem continuous_clockIntegral {d : ℕ} (s : ℝ) :
    Continuous fun z : FieldPair d × Path d =>
      ∫ u in (0 : ℝ)..s, clockDensity z.1 (pathPosition u.toNNReal z.2) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (z : FieldPair d × Path d) (u : ℝ) =>
      clockDensity z.1 (pathPosition u.toNNReal z.2))
    continuous_clockDensity_path_time 0 s

/-- The physical clock, as a real function of the environment-path pair, is continuous. -/
theorem continuous_physicalPathClock_at {d : ℕ} (s : ℝ≥0) :
    Continuous fun z : FieldPair d × Path d => (physicalPathClock z.1 z.2 s : ℝ) :=
  continuous_clockIntegral (s : ℝ)

/-- A pointwise clock-density bound `K` gives the linear clock bound `K * s`. -/
theorem physicalPathClock_le_of_clock_bound {d : ℕ} (ω : FieldPair d) (γ : Path d) {K : ℝ}
    (hK : ∀ s : ℝ≥0, clockDensity ω (pathPosition s γ) ≤ K) (s : ℝ≥0) :
    (physicalPathClock ω γ s : ℝ) ≤ K * (s : ℝ) := by
  have hint : IntervalIntegrable (fun u : ℝ => clockDensity ω (γ u.toNNReal)) volume 0 (s : ℝ) :=
    (continuous_clockDensity_along ω γ).intervalIntegrable _ _
  have hconst : IntervalIntegrable (fun _ : ℝ => K) volume 0 (s : ℝ) := intervalIntegrable_const
  have hK' : (∫ _u in (0 : ℝ)..(s : ℝ), K) = K * (s : ℝ) := by
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
  show (∫ u in (0 : ℝ)..(s : ℝ), clockDensity ω (γ u.toNNReal)) ≤ K * (s : ℝ)
  rw [← hK']
  exact intervalIntegral.integral_mono_on s.property hint hconst fun u _ => hK u.toNNReal

/-- The physical clock is nondecreasing in time, since its density is positive. -/
theorem physicalPathClock_mono {d : ℕ} (z : FieldPair d × Path d) {s t : ℝ≥0} (hst : s ≤ t) :
    (physicalPathClock z.1 z.2 s : ℝ) ≤ (physicalPathClock z.1 z.2 t : ℝ) := by
  have hc := continuous_clockDensity_along z.1 z.2
  have hT : IntervalIntegrable (fun u : ℝ => clockDensity z.1 (z.2 u.toNNReal)) volume
      0 (t : ℝ) :=
    hc.intervalIntegrable _ _
  have hS : IntervalIntegrable (fun u : ℝ => clockDensity z.1 (z.2 u.toNNReal)) volume
      0 (s : ℝ) :=
    hc.intervalIntegrable _ _
  have hdiff := intervalIntegral.integral_interval_sub_left hT hS
  have hnn : 0 ≤ ∫ u in (s : ℝ)..(t : ℝ), clockDensity z.1 (z.2 u.toNNReal) :=
    intervalIntegral.integral_nonneg (NNReal.coe_le_coe.mpr hst)
      fun u _ => (clockDensity_pos _ _).le
  show (∫ u in (0 : ℝ)..(s : ℝ), clockDensity z.1 (z.2 u.toNNReal)) ≤
    ∫ u in (0 : ℝ)..(t : ℝ), clockDensity z.1 (z.2 u.toNNReal)
  linarith

/-- Fubini for the expected clock: the expectation of `A(t)` under the annealed joint law is the
time integral of the expected observed density at the origin (`paper/main.tex`, line 1185). -/
theorem integral_physicalPathClock_eq {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (K : ℝ)
    (hbound : ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K)
    (t : ℝ≥0) :
    ∫ z, (physicalPathClock z.1 z.2 t : ℝ) ∂(annealedCoordinateJoint Q P origin_probability) =
      ∫ u in (0 : ℝ)..(t : ℝ), ∫ z, (reducedObservationAt u.toNNReal z).2 0
        ∂(annealedCoordinateJoint Q P origin_probability) := by
  haveI : IsProbabilityMeasure (annealedCoordinateJoint Q P origin_probability) :=
    annealedJointOnProbabilityFibers_isProbabilityMeasure Q (originLaw P) origin_probability
  have hfin : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (t : ℝ)) ≠ ⊤ := by
    rw [Set.uIoc_of_le (NNReal.coe_nonneg t), Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) (t : ℝ))) :=
    isFiniteMeasure_restrict.mpr hfin
  have hmeas := (continuous_clockDensity_time_path (d := d)).measurable
  have hint : Integrable (Function.uncurry fun (u : ℝ) (z : FieldPair d × Path d) =>
      clockDensity z.1 (pathPosition u.toNNReal z.2))
      (((volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) (t : ℝ))).prod
        (annealedCoordinateJoint Q P origin_probability)) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable K ?_
    refine (Measure.ae_prod_iff_ae_ae ?_).mpr (Filter.Eventually.of_forall fun u => ?_)
    · exact measurableSet_le hmeas.norm measurable_const
    · filter_upwards [hbound] with z hz
      show ‖clockDensity z.1 (pathPosition u.toNNReal z.2)‖ ≤ K
      rw [Real.norm_of_nonneg (clockDensity_pos z.1 (pathPosition u.toNNReal z.2)).le]
      exact hz u.toNNReal
  have hL : ∫ z, (physicalPathClock z.1 z.2 t : ℝ) ∂(annealedCoordinateJoint Q P origin_probability) =
      ∫ z, (∫ u in (0 : ℝ)..(t : ℝ), clockDensity z.1 (pathPosition u.toNNReal z.2))
        ∂(annealedCoordinateJoint Q P origin_probability) :=
    rfl
  rw [hL]
  simp only [clockDensity_obs]
  exact (intervalIntegral_integral_swap hint).symm

/-- Dominated convergence for the time average of a clock with a deterministic linear bound
`0 ≤ Φ s a ≤ K * s` and almost-sure rate `η`, under any probability measure. -/
theorem tendsto_integral_clock_div_of_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (Φ : ℝ≥0 → α → ℝ) (K η : ℝ)
    (hmeas : ∀ s : ℝ≥0, AEStronglyMeasurable (Φ s) μ)
    (hbound : ∀ᵐ a ∂μ, ∀ s : ℝ≥0, 0 ≤ Φ s a ∧ Φ s a ≤ K * (s : ℝ))
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun s : ℝ≥0 => Φ s a / (s : ℝ)) atTop (𝓝 η)) :
    Tendsto (fun t : ℝ => (∫ a, Φ t.toNNReal a ∂μ) / t) atTop (𝓝 η) := by
  have hF : ∀ᶠ t : ℝ in atTop, AEStronglyMeasurable (fun a => Φ t.toNNReal a * t⁻¹) μ :=
    Eventually.of_forall fun t => (hmeas t.toNNReal).mul aestronglyMeasurable_const
  have hb : ∀ᶠ t : ℝ in atTop, ∀ᵐ a ∂μ, ‖Φ t.toNNReal a * t⁻¹‖ ≤ K := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    filter_upwards [hbound] with a ha
    obtain ⟨h0, h1⟩ := ha t.toNNReal
    rw [Real.coe_toNNReal t ht.le] at h1
    rw [Real.norm_of_nonneg (mul_nonneg h0 (inv_nonneg.mpr ht.le)), ← div_eq_mul_inv,
      div_le_iff₀ ht]
    exact h1
  have hl : ∀ᵐ a ∂μ, Tendsto (fun t : ℝ => Φ t.toNNReal a * t⁻¹) atTop (𝓝 η) := by
    filter_upwards [hlim] with a ha
    refine Tendsto.congr' ?_ (ha.comp tendsto_real_toNNReal_atTop)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [Function.comp, Real.coe_toNNReal t ht, div_eq_mul_inv]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun (t : ℝ) (a : α) => Φ t.toNNReal a * t⁻¹) (f := fun _ => η) (fun _ => K)
    hF hb (integrable_const K) hl
  have hη : ∫ _a, η ∂μ = η := by simp
  simp only [integral_mul_const, hη] at key
  simpa only [div_eq_mul_inv] using key

/-- The time-averaged expected physical clock converges to `η` when the clock is bounded along
every path and its rate converges almost surely under the annealed joint law. -/
theorem tendsto_integral_physicalPathClock_div {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (K η : ℝ)
    (hbound : ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K)
    (hlim : ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability),
      Tendsto (fun t : ℝ≥0 => (physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ)) atTop (𝓝 η)) :
    Tendsto (fun t : ℝ => (∫ z, (physicalPathClock z.1 z.2 t.toNNReal : ℝ)
      ∂(annealedCoordinateJoint Q P origin_probability)) / t) atTop (𝓝 η) := by
  haveI : IsProbabilityMeasure (annealedCoordinateJoint Q P origin_probability) :=
    annealedJointOnProbabilityFibers_isProbabilityMeasure Q (originLaw P) origin_probability
  refine tendsto_integral_clock_div_of_ae (annealedCoordinateJoint Q P origin_probability)
    (fun s z => (physicalPathClock z.1 z.2 s : ℝ)) K η (fun s => ?_) ?_ hlim
  · exact (continuous_physicalPathClock_at s).aestronglyMeasurable
  · filter_upwards [hbound] with z hz
    intro s
    exact ⟨NNReal.coe_nonneg _, physicalPathClock_le_of_clock_bound z.1 z.2 hz s⟩

/-- A measurable event that holds for almost every environment and almost every path from the
origin holds almost surely under the annealed joint law. The proof uses the fibre identity
for the joint law, applied to the indicator of the complement. -/
theorem ae_annealedCoordinateJoint_mem {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    {S : Set (FieldPair d × Path d)} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω), (ω, γ) ∈ S) :
    ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability), z ∈ S := by
  have hF : Measurable (Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS.compl
  have hint : ∫⁻ z, Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) z
      ∂(annealedCoordinateJoint Q P origin_probability) =
      ∫⁻ ω, ∫⁻ γ, Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) (ω, γ)
        ∂(originLaw P ω) ∂Q :=
    annealedJointOnProbabilityFibers_lintegral Q (originLaw P) origin_probability _ hF
  have hfib : ∀ᵐ ω ∂Q,
      ∫⁻ γ, Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) (ω, γ)
        ∂(originLaw P ω) = 0 := by
    filter_upwards [h] with ω hω
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hω] with γ hγ
    exact Set.indicator_of_notMem (not_not.mpr hγ) _
  have hzero : ∫⁻ z, Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) z
      ∂(annealedCoordinateJoint Q P origin_probability) = 0 := by
    rw [hint, lintegral_congr_ae hfib]
    simp
  filter_upwards [(lintegral_eq_zero_iff hF).mp hzero] with z hz
  by_contra hzS
  have h1 : Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) z = 1 :=
    Set.indicator_of_mem hzS _
  have h2 : Sᶜ.indicator (fun _ : FieldPair d × Path d => (1 : ℝ≥0∞)) z = 0 := hz
  exact one_ne_zero (h1.symm.trans h2)

/-- Environment-path pairs whose clock density is bounded by `K` at every time. -/
def clockBoundSet {d : ℕ} (K : ℝ) : Set (FieldPair d × Path d) :=
  {z | ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K}

theorem isClosed_clockBoundSet {d : ℕ} (K : ℝ) : IsClosed (clockBoundSet (d := d) K) := by
  unfold clockBoundSet
  rw [Set.setOf_forall]
  exact isClosed_iInter fun s => isClosed_le (continuous_clockDensity_at s) continuous_const

/-- Environment-path pairs along which the physical clock divided by integer time converges
to `η`. -/
def clockRateNatSet {d : ℕ} (η : ℝ) : Set (FieldPair d × Path d) :=
  {z | Tendsto (fun n : ℕ => (physicalPathClock z.1 z.2 (n : ℝ≥0) : ℝ) / ((n : ℝ≥0) : ℝ))
    atTop (𝓝 η)}

theorem measurableSet_clockRateNatSet {d : ℕ} (η : ℝ) :
    MeasurableSet (clockRateNatSet (d := d) η) := by
  unfold clockRateNatSet
  exact measurableSet_tendsto (𝓝 η)
    (f := fun (n : ℕ) (z : FieldPair d × Path d) =>
      (physicalPathClock z.1 z.2 (n : ℝ≥0) : ℝ) / ((n : ℝ≥0) : ℝ))
    fun n => ((continuous_physicalPathClock_at (n : ℝ≥0)).div_const ((n : ℝ≥0) : ℝ)).measurable

/-- A monotone nonnegative profile whose ratio `Φ n / n` converges along the integers has the
same limit of `Φ s / s` along all nonnegative times. The proof squeezes `Φ s / s` between the
values at `⌊s⌋₊` and `⌊s⌋₊ + 1`. -/
theorem tendsto_div_of_tendsto_natCast {Φ : ℝ≥0 → ℝ} (hnn : ∀ s, 0 ≤ Φ s)
    (hmono : Monotone Φ) {η : ℝ}
    (hnat : Tendsto (fun n : ℕ => Φ (n : ℝ≥0) / ((n : ℝ≥0) : ℝ)) atTop (𝓝 η)) :
    Tendsto (fun s : ℝ≥0 => Φ s / (s : ℝ)) atTop (𝓝 η) := by
  have hnat' : Tendsto (fun n : ℕ => Φ (n : ℝ≥0) / (n : ℝ)) atTop (𝓝 η) := by
    simpa only [NNReal.coe_natCast] using hnat
  have hlow : Tendsto (fun n : ℕ => Φ (n : ℝ≥0) / ((n : ℝ) + 1)) atTop (𝓝 η) := by
    have h := hnat'.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    show Φ (n : ℝ≥0) / (n : ℝ) * ((n : ℝ) / ((n : ℝ) + 1)) = Φ (n : ℝ≥0) / ((n : ℝ) + 1)
    rw [div_mul_div_comm, mul_comm (Φ (n : ℝ≥0)) (n : ℝ), mul_div_mul_left _ _ hn0]
  have hnat1 : Tendsto (fun n : ℕ => Φ ((n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ)) atTop
      (𝓝 η) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hnat'
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 1) := by
      have h0 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at h0
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    show (1 : ℝ) + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ)
    rw [add_div, div_self hn0]
  have hup : Tendsto (fun n : ℕ => Φ ((n + 1 : ℕ) : ℝ≥0) / (n : ℝ)) atTop (𝓝 η) := by
    have h := hnat1.mul hratio
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_add_one n
    show Φ ((n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ) * (((n : ℝ) + 1) / (n : ℝ)) =
      Φ ((n + 1 : ℕ) : ℝ≥0) / (n : ℝ)
    rw [hc, div_mul_div_comm, mul_comm ((n : ℝ) + 1) (n : ℝ), mul_div_mul_right _ _ hn1]
  have hfl : Tendsto (fun s : ℝ≥0 => ⌊s⌋₊) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨(b : ℝ≥0), fun s hs => Nat.le_floor hs⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlow.comp hfl) (hup.comp hfl) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with s hs
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hs0 : (0 : ℝ) < (s : ℝ) := by linarith
    have hslt : (s : ℝ) ≤ ((⌊s⌋₊ : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.lt_floor_add_one s).le
    have hPn : Φ ((⌊s⌋₊ : ℕ) : ℝ≥0) ≤ Φ s := hmono (Nat.floor_le zero_le)
    have hden : (0 : ℝ) < ((⌊s⌋₊ : ℕ) : ℝ) + 1 := by positivity
    show Φ ((⌊s⌋₊ : ℕ) : ℝ≥0) / (((⌊s⌋₊ : ℕ) : ℝ) + 1) ≤ Φ s / (s : ℝ)
    rw [div_le_div_iff₀ hden hs0]
    exact (mul_le_mul_of_nonneg_right hPn hs0.le).trans (mul_le_mul_of_nonneg_left hslt (hnn s))
  · filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with s hs
    have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have hs0 : (0 : ℝ) < (s : ℝ) := by linarith
    have hn1 : 0 < ⌊s⌋₊ := Nat.floor_pos.mpr hs
    have hm0 : (0 : ℝ) < ((⌊s⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn1
    have hmle : ((⌊s⌋₊ : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.floor_le (zero_le (a := s))
    have hPs : Φ s ≤ Φ ((⌊s⌋₊ + 1 : ℕ) : ℝ≥0) :=
      hmono (by push_cast; exact (Nat.lt_floor_add_one s).le)
    show Φ s / (s : ℝ) ≤ Φ ((⌊s⌋₊ + 1 : ℕ) : ℝ≥0) / ((⌊s⌋₊ : ℕ) : ℝ)
    rw [div_le_div_iff₀ hs0 hm0]
    exact (mul_le_mul_of_nonneg_left hmle (hnn s)).trans
      (mul_le_mul_of_nonneg_right hPs hs0.le)

/-- Environment-almost-sure form of the time-averaged expected clock: the clock bound and the
rate are assumed for almost every environment and almost every path from the origin
(`paper/main.tex`, lines 1185–1186). -/
theorem tendsto_integral_physicalPathClock_div_of_fiber {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (K η : ℝ)
    (hbound : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω),
      ∀ s : ℝ≥0, clockDensity ω (pathPosition s γ) ≤ K)
    (hlim : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω),
      Tendsto (fun t : ℝ≥0 => (physicalPathClock ω γ t : ℝ) / (t : ℝ)) atTop (𝓝 η)) :
    Tendsto (fun t : ℝ => (∫ z, (physicalPathClock z.1 z.2 t.toNNReal : ℝ)
      ∂(annealedCoordinateJoint Q P origin_probability)) / t) atTop (𝓝 η) := by
  have hJb : ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K :=
    (ae_annealedCoordinateJoint_mem Q P origin_probability
      (isClosed_clockBoundSet K).measurableSet
      (hbound.mono fun ω hω => hω.mono fun γ hγ => hγ)).mono fun z hz => hz
  have hGn : ∀ᵐ z ∂(annealedCoordinateJoint Q P origin_probability), z ∈ clockRateNatSet η :=
    ae_annealedCoordinateJoint_mem Q P origin_probability (measurableSet_clockRateNatSet η)
      (hlim.mono fun ω hω => hω.mono fun γ hγ => hγ.comp tendsto_natCast_atTop_atTop)
  refine tendsto_integral_physicalPathClock_div Q P origin_probability K η hJb ?_
  filter_upwards [hGn] with z hz
  exact tendsto_div_of_tendsto_natCast (η := η)
    (Φ := fun s => (physicalPathClock z.1 z.2 s : ℝ))
    (fun s => NNReal.coe_nonneg _) (fun _ _ hst => physicalPathClock_mono z hst) hz

end EinsteinRelation.Clock
