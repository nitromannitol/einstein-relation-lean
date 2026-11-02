import EinsteinFull.Work.W1.PhysicalInteriorL2Support
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The actual exit-killed GMP endpoint kernels

These kernels restrict the supplied continuous-path realization to strict
survival in an arbitrary open domain, then evaluate at the displayed time.
Their support and absolute continuity follow from the actual path laws and
heat kernels. Detailed balance gives excessiveness of the physical measure
and hence bounded linear killed operators on the actual interior L² carrier.
They are identity at zero and recover interior bounded continuous tests as
time decreases to zero. Equality with the constructed variational evolution,
the semigroup law and strong continuity on all L² data remain to be proved.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support

noncomputable section

/-- The measurable strict-survival event, including time zero. -/
theorem measurableSet_localitySurvival {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) : MeasurableSet {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ} :=
  measurableSet_lt measurable_const (measurable_localityExitTime U hU)

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- The actual GMP law killed at its first exit from `U`, with zero mass after exit. -/
def gmpKilledEndpointKernel (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    Kernel (Vec d) (Vec d) :=
  (G.pathLaw.restrict (measurableSet_localitySurvival U hU t)).map (pathPosition t)

/-- The definition is a literal restriction and endpoint pushforward of the GMP law. -/
theorem gmpKilledEndpointKernel_apply (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x =
      ((G.pathLaw x).restrict {γ | (t : ℝ≥0∞) < localityExitTime U γ}).map
        (pathPosition t) := by
  rw [gmpKilledEndpointKernel, Kernel.map_apply _ (measurable_pathPosition t),
    Kernel.restrict_apply]

/-- Killing can only decrease each actual endpoint measure. -/
theorem gmpKilledEndpointKernel_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x ≤ G.transitionKernel t x := by
  rw [gmpKilledEndpointKernel_apply, ← G.pathLaw_endpoint t x]
  exact Measure.map_mono Measure.restrict_le_self (measurable_pathPosition t)

/-- The killed endpoint kernel has mass at most one, for every starting point. -/
theorem gmpKilledEndpointKernel_mass_le_one (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x Set.univ ≤ 1 := by
  letI := G.transitionKernel_isMarkovKernel t
  exact (gmpKilledEndpointKernel_le G U hU t x Set.univ).trans_eq (measure_univ)

/-- These actual killed kernels are finite uniformly over their starting points. -/
theorem isFiniteKernel_gmpKilledEndpointKernel (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) : IsFiniteKernel (gmpKilledEndpointKernel G U hU t) := by
  letI := G.pathLaw_isMarkovKernel
  unfold gmpKilledEndpointKernel
  infer_instance

/-- All surviving endpoints are in the open domain; no exceptional starting points occur. -/
theorem gmpKilledEndpointKernel_ae_mem (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) :
    ∀ᵐ y ∂gmpKilledEndpointKernel G U hU t x, y ∈ U := by
  rw [gmpKilledEndpointKernel_apply]
  apply (ae_map_iff (p := fun y : Vec d => y ∈ U)
    (measurable_pathPosition t).aemeasurable hU.measurableSet).mpr
  rw [ae_restrict_iff' (measurableSet_localitySurvival U hU t)]
  exact ae_of_all _ fun γ hγ => (lt_localityExitTime_iff U hU γ t).mp hγ t le_rfl

/-- Starting outside `U` kills immediately, including at time zero. -/
theorem gmpKilledEndpointKernel_eq_zero_of_notMem (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (hx : x ∉ U) :
    gmpKilledEndpointKernel G U hU t x = 0 := by
  rw [gmpKilledEndpointKernel_apply]
  have hz : (G.pathLaw x) {γ | (t : ℝ≥0∞) < localityExitTime U γ} = 0 := by
    have hnot : ∀ᵐ γ ∂G.pathLaw x, ¬(t : ℝ≥0∞) < localityExitTime U γ := by
      filter_upwards [G.pathLaw_starts_at x] with γ hγ hs
      exact hx (hγ ▸ (lt_localityExitTime_iff U hU γ t).mp hs 0 zero_le)
    simpa only [not_not] using (ae_iff.mp hnot)
  rw [Measure.restrict_eq_zero.mpr hz, Measure.map_zero]

/-- At positive time the actual killed endpoint has a Lebesgue density. -/
theorem gmpKilledEndpointKernel_absolutelyContinuous_volume
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x ≪ (volume : Measure (Vec d)) := by
  apply (Measure.absolutelyContinuous_of_le (gmpKilledEndpointKernel_le G U hU t x)).trans
  rw [G.transitionKernel_eq_heatKernel t ht x]
  exact withDensity_absolutelyContinuous _ _

/-- Positive-time killed endpoints respect the actual physical speed-measure classes. -/
theorem gmpKilledEndpointKernel_absolutelyContinuous_physical
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x ≪ physicalReversibleMeasure ω hd lam := by
  apply (gmpKilledEndpointKernel_absolutelyContinuous_volume G U hU t ht x).trans
  exact withDensity_absolutelyContinuous'
    ((ENNReal.continuous_ofReal.comp (physicalReversibleDensity_continuous ω hd lam)).measurable.aemeasurable)
    (ae_of_all _ fun y => (ENNReal.ofReal_pos.mpr (physicalReversibleDensity_pos ω hd lam y)).ne')

/-- Any physical almost-everywhere equality of inputs gives equal killed expectations
at every starting point and every positive time. -/
theorem integral_gmpKilledEndpointKernel_congr_ae
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) (x : Vec d)
    (f g : Vec d → ℝ) (hfg : f =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =
      ∫ y, g y ∂gmpKilledEndpointKernel G U hU t x :=
  integral_congr_ae ((gmpKilledEndpointKernel_absolutelyContinuous_physical G U hU t ht x).ae_le hfg)

/-- Killed expectations are precisely survival-weighted path expectations. -/
theorem integral_gmpKilledEndpointKernel (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (f : Vec d → ℝ) (hf : Measurable f) :
    (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) =
      ∫ γ, {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}.indicator
        (fun γ => f (pathPosition t γ)) γ ∂G.pathLaw x := by
  rw [gmpKilledEndpointKernel_apply,
    integral_map (measurable_pathPosition t).aemeasurable hf.aestronglyMeasurable,
    integral_indicator (measurableSet_localitySurvival U hU t)]

/-- At time zero, the killed law is the Dirac mass inside the domain and zero outside. -/
theorem gmpKilledEndpointKernel_zero (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) :
    gmpKilledEndpointKernel G U hU 0 x = U.indicator (fun x => Measure.dirac x) x := by
  classical
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, gmpKilledEndpointKernel_apply]
    have hs : ∀ᵐ γ ∂G.pathLaw x, (0 : ℝ≥0∞) < localityExitTime U γ := by
      filter_upwards [G.pathLaw_starts_at x] with γ hγ
      change γ 0 = x at hγ
      apply (lt_localityExitTime_iff U hU γ 0).mpr
      intro t ht
      have ht0 : t = 0 := le_antisymm ht zero_le
      simpa only [ht0, hγ] using hx
    rw [Measure.restrict_eq_self_of_ae_mem
      (s := {γ : Path d | ((0 : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ}) hs, G.pathLaw_endpoint,
      G.transitionKernel_zero, Kernel.id_apply]
  · rw [Set.indicator_of_notMem hx]
    exact gmpKilledEndpointKernel_eq_zero_of_notMem G U hU 0 x hx

/-- A path starting in an open domain survives for a positive interval. -/
theorem eventually_localitySurvival_at_zero {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (γ : Path d) (hγ : γ 0 ∈ U) :
    ∀ᶠ t : ℝ≥0 in 𝓝 0, (t : ℝ≥0∞) < localityExitTime U γ := by
  have hs : (0 : ℝ≥0∞) < localityExitTime U γ := by
    apply (lt_localityExitTime_iff U hU γ 0).mpr
    intro t ht
    have ht0 : t = 0 := le_antisymm ht zero_le
    simpa only [ht0] using hγ
  exact (ENNReal.continuous_coe.tendsto (0 : ℝ≥0)).eventually (Iio_mem_nhds hs)

/-- Actual killed expectations recover every interior initial value for bounded continuous
tests. This uses continuous paths and dominated convergence, with no Feller premise. -/
theorem tendsto_integral_gmpKilledEndpointKernel_at_zero
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d) (hx : x ∈ U)
    (f : Vec d → ℝ) (hf : Continuous f) (B : ℝ) (hB : ∀ y, |f y| ≤ B) :
    Tendsto (fun t : ℝ≥0 => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x)
      (𝓝 0) (𝓝 (f x)) := by
  classical
  letI := G.pathLaw_isMarkovKernel
  let F : ℝ≥0 → Path d → ℝ := fun t =>
    {γ : Path d | (t : ℝ≥0∞) < localityExitTime U γ}.indicator
      (fun γ => f (pathPosition t γ))
  have hB0 : 0 ≤ B := (abs_nonneg (f x)).trans (hB x)
  have hmeas : ∀ t, AEStronglyMeasurable (F t) (G.pathLaw x) := by
    intro t
    exact ((hf.measurable.comp (measurable_pathPosition t)).indicator
      (measurableSet_localitySurvival U hU t)).aestronglyMeasurable
  have hbound : ∀ t, ∀ᵐ γ ∂G.pathLaw x, ‖F t γ‖ ≤ B := by
    intro t
    apply ae_of_all
    intro γ
    by_cases hs : (t : ℝ≥0∞) < localityExitTime U γ
    · simpa only [F, Set.indicator, Set.mem_setOf_eq, hs, ↓reduceIte, Real.norm_eq_abs]
        using hB (pathPosition t γ)
    · simpa only [F, Set.indicator, Set.mem_setOf_eq, hs, ↓reduceIte, norm_zero] using hB0
  have hlim : ∀ᵐ γ ∂G.pathLaw x, Tendsto (fun t => F t γ) (𝓝 0) (𝓝 (f x)) := by
    filter_upwards [G.pathLaw_starts_at x] with γ hγ
    change γ 0 = x at hγ
    have hsurvive := eventually_localitySurvival_at_zero U hU γ (by
      simpa only [hγ] using hx)
    have ht : Tendsto (fun t => f (γ t)) (𝓝 0) (𝓝 (f x)) := by
      simpa only [hγ] using! (hf.tendsto (γ 0)).comp (γ.continuous.tendsto 0)
    apply ht.congr'
    filter_upwards [hsurvive] with t ht
    simp only [F, Set.indicator, Set.mem_setOf_eq, ht, ↓reduceIte, pathPosition]
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound) (integrable_const B) hlim
  simpa only [F, ← integral_gmpKilledEndpointKernel G U hU _ x f hf.measurable,
    integral_const, probReal_univ, one_smul] using h

/-- Detailed balance of the supplied realization gives invariance of its physical measure. -/
theorem lintegral_gmpTransitionKernel (t : ℝ≥0) (A : Set (Vec d))
    (hA : MeasurableSet A) :
    (∫⁻ x, G.transitionKernel t x A ∂physicalReversibleMeasure ω hd lam) =
      physicalReversibleMeasure ω hd lam A := by
  letI := G.transitionKernel_isMarkovKernel t
  have h := G.transitionKernel_reversible t Set.univ A MeasurableSet.univ hA
  simpa only [Measure.restrict_univ, measure_univ, lintegral_one, Measure.restrict_apply hA,
    Set.univ_inter, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h

/-- Killing makes the actual physical measure excessive, on every measurable set. -/
theorem lintegral_gmpKilledEndpointKernel_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (A : Set (Vec d)) (hA : MeasurableSet A) :
    (∫⁻ x, gmpKilledEndpointKernel G U hU t x A ∂physicalReversibleMeasure ω hd lam) ≤
      physicalReversibleMeasure ω hd lam A := by
  rw [← lintegral_gmpTransitionKernel G t A hA]
  exact lintegral_mono fun x => gmpKilledEndpointKernel_le G U hU t x A

/-- The physical measure composed with the actual killed kernel is dominated by itself. -/
theorem gmpKilledEndpointKernel_comp_physical_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) :
    gmpKilledEndpointKernel G U hU t ∘ₘ physicalReversibleMeasure ω hd lam ≤
      physicalReversibleMeasure ω hd lam := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  exact lintegral_gmpKilledEndpointKernel_le G U hU t A hA

private theorem sq_integral_le_of_mass_le_one {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (hν : ν Set.univ ≤ 1)
    (f : α → ℝ) (hf : MemLp f 2 ν) :
    (∫ y, f y ∂ν) ^ 2 ≤ ∫ y, (f y) ^ 2 ∂ν := by
  have hone : MemLp (fun _ : α => (1 : ℝ)) 2 ν := memLp_const 1
  let u := hf.toLp f
  let v := hone.toLp (fun _ : α => (1 : ℝ))
  have huv : inner ℝ u v = ∫ y, f y ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hone.coeFn_toLp] with y hy hz
    simp only [u, v, hy, hz, RCLike.inner_apply, conj_trivial, one_mul]
  have huu : inner ℝ u u = ∫ y, f y ^ 2 ∂ν := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    simp only [u, hy, RCLike.inner_apply, conj_trivial, pow_two]
  have hvv : inner ℝ v v = ν.real Set.univ := by
    rw [L2.inner_def]
    calc
      (∫ y, inner ℝ (v y) (v y) ∂ν) = ∫ _ : α, (1 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hone.coeFn_toLp] with y hy
        simp only [v, hy, RCLike.inner_apply, conj_trivial, one_mul]
      _ = ν.real Set.univ := by simp
  have hmass : ν.real Set.univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa only [ENNReal.ofReal_one] using hν)
  have hcs := real_inner_mul_inner_self_le u v
  rw [huv, huu, hvv] at hcs
  calc
    _ ≤ (∫ y, f y ^ 2 ∂ν) * ν.real Set.univ := by simpa only [pow_two] using hcs
    _ ≤ _ := mul_le_of_le_one_right (integral_nonneg fun _ => sq_nonneg _) hmass

/-- Physical L² inputs are square integrable under almost every killed endpoint law,
with the actual kernel and physical measure, at every time including zero. -/
theorem ae_memLp_gmpKilledEndpointKernel (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      MemLp f 2 (gmpKilledEndpointKernel G U hU t x) := by
  have hint := (Lp.memLp f).integrable_sq.mono_measure
    (gmpKilledEndpointKernel_comp_physical_le G U hU t)
  filter_upwards [Measure.ae_integrable_of_integrable_comp hint] with x hx
  exact (memLp_two_iff_integrable_sq (Lp.stronglyMeasurable f).aestronglyMeasurable).mpr hx

/-- The square of each actual killed expectation is bounded by the killed second moment,
for physical almost every starting point. -/
theorem sq_integral_gmpKilledEndpointKernel_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) ^ 2 ≤
        ∫ y, (f y) ^ 2 ∂gmpKilledEndpointKernel G U hU t x := by
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  filter_upwards [ae_memLp_gmpKilledEndpointKernel G U hU t f] with x hx
  exact sq_integral_le_of_mass_le_one _ (gmpKilledEndpointKernel_mass_le_one G U hU t x) f hx

/-- The actual killed expectation of every physical L² datum is again in physical L². -/
theorem memLp_integral_gmpKilledEndpointKernel (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    MemLp (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) 2
      (physicalReversibleMeasure ω hd lam) := by
  have hint := (Lp.memLp f).integrable_sq.mono_measure
    (gmpKilledEndpointKernel_comp_physical_le G U hU t)
  have hg := Measure.integrable_integral_norm_of_integrable_comp hint
  have hg' : Integrable (fun x => ∫ y, (f y) ^ 2 ∂gmpKilledEndpointKernel G U hU t x)
      (physicalReversibleMeasure ω hd lam) := by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hg
  have hm := (Lp.stronglyMeasurable f).integral_kernel (κ := gmpKilledEndpointKernel G U hU t)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply hg'.mono' (hm.pow 2).aestronglyMeasurable
  filter_upwards [sq_integral_gmpKilledEndpointKernel_le G U hU t f] with x hx
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hx

/-- The actual killed expectations contract the physical second moment. -/
theorem integral_sq_gmpKilledEndpointKernel_le (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∫ x, (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) ^ 2
      ∂physicalReversibleMeasure ω hd lam) ≤
        ∫ y, (f y) ^ 2 ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := gmpKilledEndpointKernel G U hU t
  have hint : Integrable (fun y => (f y) ^ 2) (K ∘ₘ μ) :=
    (Lp.memLp f).integrable_sq.mono_measure (gmpKilledEndpointKernel_comp_physical_le G U hU t)
  have hcomp := Kernel.integral_comp (η := K) (κ := Kernel.const Unit μ)
    (a := ()) (by simpa only [Kernel.comp_const, Kernel.const_apply] using hint)
  have hg : Integrable (fun x => ∫ y, (f y) ^ 2 ∂K x) μ := by
    have hg := Measure.integrable_integral_norm_of_integrable_comp hint
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hg
  calc
    _ ≤ ∫ x, ∫ y, (f y) ^ 2 ∂K x ∂μ :=
      integral_mono_ae (memLp_integral_gmpKilledEndpointKernel G U hU t f).integrable_sq
        hg (sq_integral_gmpKilledEndpointKernel_le G U hU t f)
    _ = ∫ y, (f y) ^ 2 ∂(K ∘ₘ μ) := by
      simpa only [Kernel.comp_const, Kernel.const_apply] using hcomp.symm
    _ ≤ _ := integral_mono_measure (gmpKilledEndpointKernel_comp_physical_le G U hU t)
      (ae_of_all _ fun _ => sq_nonneg _) (Lp.memLp f).integrable_sq

/-- The actual killed expectation as a class in the physical L² space. -/
def gmpKilledL2 (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (memLp_integral_gmpKilledEndpointKernel G U hU t f).toLp
    (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x)

/-- The L² construction has the literal killed expectation as its representative. -/
theorem gmpKilledL2_ae_eq (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU t f =ᵐ[physicalReversibleMeasure ω hd lam]
      (fun x => ∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) :=
  MemLp.coeFn_toLp _

private theorem norm_sq_L2_eq_integral_sq {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : Lp ℝ 2 ν) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

/-- The actual killed L² map is a contraction, with constant one for all domains and times. -/
theorem gmpKilledL2_norm_le (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖gmpKilledL2 G U hU t f‖ ≤ ‖f‖ := by
  have hsq : ‖gmpKilledL2 G U hU t f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_L2_eq_integral_sq, norm_sq_L2_eq_integral_sq]
    calc
      _ = ∫ x, (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) ^ 2
          ∂physicalReversibleMeasure ω hd lam := by
        apply integral_congr_ae
        filter_upwards [gmpKilledL2_ae_eq G U hU t f] with x hx
        rw [hx]
      _ ≤ _ := integral_sq_gmpKilledEndpointKernel_le G U hU t f
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The actual killed L² datum belongs to the previously constructed interior value closure. -/
theorem gmpKilledL2_mem_zeroBoundaryL2 (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU t f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
  apply (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω _).mpr
  filter_upwards [gmpKilledL2_ae_eq G U hU t f] with x hx hxU
  rw [hx, gmpKilledEndpointKernel_eq_zero_of_notMem G U hU t x hxU, integral_zero_measure]

/-- At zero, the actual killed L² map is the already constructed physical interior projection. -/
theorem gmpKilledL2_zero (U : Set (Vec d)) (hU : IsOpen U)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU 0 f = physicalZeroBoundaryProjection U hd ω lam L hω f := by
  classical
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G U hU 0 f,
    physicalZeroBoundaryProjection_ae_eq_indicator U hU hd ω lam L hω f] with x hx hy
  rw [hx, hy, gmpKilledEndpointKernel_zero G U hU x]
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, integral_dirac]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU, integral_zero_measure]

/-- Almost-everywhere identities under the physical measure hold under almost every
actual killed endpoint law, also at time zero. -/
theorem ae_ae_gmpKilledEndpointKernel_of_ae (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) {p : Vec d → Prop} (hp : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, p y) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∀ᵐ y ∂gmpKilledEndpointKernel G U hU t x, p y :=
  Measure.ae_ae_of_ae_comp ((Measure.absolutelyContinuous_of_le
    (gmpKilledEndpointKernel_comp_physical_le G U hU t)).ae_le hp)

/-- Linearity of the actual killed L² construction, derived from the endpoint laws. -/
theorem gmpKilledL2_add (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU t (f + g) = gmpKilledL2 G U hU t f + gmpKilledL2 G U hU t g := by
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G U hU t (f + g), gmpKilledL2_ae_eq G U hU t f,
    gmpKilledL2_ae_eq G U hU t g, Lp.coeFn_add (gmpKilledL2 G U hU t f) (gmpKilledL2 G U hU t g),
    ae_memLp_gmpKilledEndpointKernel G U hU t f, ae_memLp_gmpKilledEndpointKernel G U hU t g,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t (Lp.coeFn_add f g)]
    with x hx hf hg hsum hfi hgi hfg
  rw [hx, hsum, Pi.add_apply, hf, hg]
  exact (integral_congr_ae hfg).trans
    (integral_add (hfi.integrable (by norm_num)) (hgi.integrable (by norm_num)))

/-- Scalar multiplication of the actual killed L² construction. -/
theorem gmpKilledL2_smul (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (c : ℝ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2 G U hU t (c • f) = c • gmpKilledL2 G U hU t f := by
  apply Lp.ext
  filter_upwards [gmpKilledL2_ae_eq G U hU t (c • f), gmpKilledL2_ae_eq G U hU t f,
    Lp.coeFn_smul c (gmpKilledL2 G U hU t f),
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t (Lp.coeFn_smul c f)] with x hx hf hsmul hcf
  rw [hx, hsmul, Pi.smul_apply, hf]
  exact (integral_congr_ae hcf).trans (integral_smul c f)

/-- The actual killed expectation is a bounded linear operator on physical L². -/
def gmpKilledL2Operator (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  LinearMap.mkContinuous
    { toFun := gmpKilledL2 G U hU t
      map_add' := gmpKilledL2_add G U hU t
      map_smul' := gmpKilledL2_smul G U hU t }
    1 (by intro f; simpa only [one_mul] using! gmpKilledL2_norm_le G U hU t f)

/-- The bounded operator is the actual integral construction, without further extension. -/
theorem gmpKilledL2Operator_apply (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpKilledL2Operator G U hU t f = gmpKilledL2 G U hU t f := rfl

/-- The physical L² operator bound is uniform over all open domains and times. -/
theorem gmpKilledL2Operator_norm_le_one (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    ‖gmpKilledL2Operator G U hU t‖ ≤ 1 := by
  apply (gmpKilledL2Operator G U hU t).opNorm_le_bound zero_le_one
  intro f
  simpa only [gmpKilledL2Operator_apply, one_mul] using gmpKilledL2_norm_le G U hU t f

/-- The actual killed operator on exactly the carrier of the constructed interior evolution. -/
def gmpKilledInteriorOperator (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) :
    physicalZeroBoundaryL2 U hd ω lam L hω →L[ℝ] physicalZeroBoundaryL2 U hd ω lam L hω :=
  ContinuousLinearMap.codRestrict
    ((gmpKilledL2Operator G U hU t).comp (physicalZeroBoundaryL2 U hd ω lam L hω).subtypeL)
    (physicalZeroBoundaryL2 U hd ω lam L hω)
    (fun f => gmpKilledL2_mem_zeroBoundaryL2 G U hU t f.val)

/-- The interior operator retains the actual survival-weighted GMP expectation. -/
theorem gmpKilledInteriorOperator_ae_eq (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (gmpKilledInteriorOperator G U hU t f).val =ᵐ[physicalReversibleMeasure ω hd lam]
      (fun x => ∫ y, f.val y ∂gmpKilledEndpointKernel G U hU t x) :=
  gmpKilledL2_ae_eq G U hU t f.val

/-- The actual killed operator is identity on the interior carrier at time zero. -/
theorem gmpKilledInteriorOperator_zero (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    gmpKilledInteriorOperator G U hU 0 f = f := by
  apply Subtype.ext
  change gmpKilledL2 G U hU 0 f.val = f.val
  rw [gmpKilledL2_zero]
  exact (physicalZeroBoundaryL2 U hd ω lam L hω).starProjection_mem_subspace_eq_self f

/-- The actual interior killed operator is contractive. -/
theorem gmpKilledInteriorOperator_norm_le (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ‖gmpKilledInteriorOperator G U hU t f‖ ≤ ‖f‖ :=
  gmpKilledL2_norm_le G U hU t f.val

end

end EinsteinFull
