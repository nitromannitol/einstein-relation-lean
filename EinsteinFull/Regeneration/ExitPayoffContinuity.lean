import EinsteinFull.Calculus.SunaS1KilledExitContinuity
import EinsteinFull.Calculus.SunaS6GMPEnvironment
import EinsteinFull.Calculus.U4RegularKernelSmoothing
import EinsteinFull.Regeneration.GMPBoundedSlabPayoff

/-!
# Continuity of exit payoffs

For a supplied realization of the regular diffusion, the expected value of a bounded
continuous payoff at the exit position of an open set is continuous inside the set: a
short time step of the Markov property approximates it by a transition average, which is
continuous by the strong Feller property, with an error controlled by the probability of
an early exit.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- The expected payoff at the exit position of a set. -/
noncomputable def exitPayoff (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ γ, f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0)) ∂G.pathLaw x

/-- The exit payoff functional on paths. -/
noncomputable def exitPayoffFunctional (U : Set (Vec d)) (f : Vec d → ℝ) (γ : Path d) : ℝ :=
  f (γ ((MarkovProcess.ContinuousPath.exitTimeTop U γ).untopD 0))

theorem measurable_exitPayoffFunctional (U : Set (Vec d)) (hU : IsOpen U)
    (f : Vec d → ℝ) (hf : Measurable f) :
    Measurable (exitPayoffFunctional U f) :=
  hf.comp (MarkovProcess.ContinuousPath.measurable_eval_untopD_exitTimeTop U hU)

/-- The exit payoff is measurable in the starting point. -/
theorem measurable_exitPayoff (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (f : Vec d → ℝ) (hf : Measurable f) :
    Measurable (exitPayoff G U f) :=
  ((measurable_exitPayoffFunctional U hU f hf).stronglyMeasurable.integral_kernel
    (κ := G.pathLaw)).measurable

/-- A bounded payoff has a bounded exit payoff. -/
theorem abs_exitPayoff_le (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (f : Vec d → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B) (x : Vec d) :
    |exitPayoff G U f x| ≤ B := by
  have : IsProbabilityMeasure (G.pathLaw x) := G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have h := norm_integral_le_of_norm_le_const (μ := G.pathLaw x)
    (f := fun γ => exitPayoffFunctional U f γ) (C := B)
    (Eventually.of_forall fun γ => by
      rw [Real.norm_eq_abs]
      exact hB _)
  have hone : (G.pathLaw x).real univ = 1 := by simp [measureReal_def]
  rw [hone, mul_one, Real.norm_eq_abs] at h
  exact h

/-- Outside the set the exit happens at time zero. -/
theorem exitPayoff_of_notMem (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (f : Vec d → ℝ) (x : Vec d) (hx : x ∉ U) :
    exitPayoff G U f x = f x := by
  have : IsProbabilityMeasure (G.pathLaw x) := G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have hae : ∀ᵐ γ ∂G.pathLaw x, exitPayoffFunctional U f γ = f x := by
    filter_upwards [G.pathLaw_starts_at x] with γ hγ
    change γ 0 = x at hγ
    have hle : MarkovProcess.ContinuousPath.exitTime U γ ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
      MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ 0 (by rw [hγ]; exact hx)
    have hzero : MarkovProcess.ContinuousPath.exitTime U γ = 0 := by
      simpa using hle
    have hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
      rw [hzero]
      exact ENNReal.zero_ne_top
    unfold exitPayoffFunctional
    rw [MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hfin, hzero,
      ENNReal.toNNReal_zero, hγ]
  unfold exitPayoff
  change ∫ γ, exitPayoffFunctional U f γ ∂G.pathLaw x = f x
  have hone : (G.pathLaw x).real univ = 1 := by simp [measureReal_def]
  rw [integral_congr_ae hae, integral_const, hone, one_smul]


/-- Shifting a path before its finite exit time leaves the exit position unchanged. -/
theorem exitPayoffFunctional_shift (U : Set (Vec d)) (f : Vec d → ℝ) (γ : Path d) (s : ℝ≥0)
    (hs : (s : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ)
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    exitPayoffFunctional U f (MarkovProcess.ContinuousPath.shift s γ) =
      exitPayoffFunctional U f γ := by
  have hadd := MarkovProcess.ContinuousPath.exitTime_shift_add U γ s hs
  have hfin' : MarkovProcess.ContinuousPath.exitTime U
      (MarkovProcess.ContinuousPath.shift s γ) ≠ ⊤ := by
    intro h
    rw [h, top_add] at hadd
    exact hfin hadd.symm
  unfold exitPayoffFunctional
  rw [MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U _ hfin',
    MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hfin,
    MarkovProcess.ContinuousPath.shift_apply, ← hadd,
    ENNReal.toNNReal_add hfin' ENNReal.coe_ne_top, ENNReal.toNNReal_coe, add_comm]

/-- The Markov property at a deterministic time: before the exit, the payoff restarts
from the current position. -/
theorem exitPayoff_markov (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (f : Vec d → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B) (x : Vec d)
    (hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) (s : ℝ≥0) :
    exitPayoff G U f x =
      (∫ γ in {γ : Path d | (s : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ},
        exitPayoff G U f (γ s) ∂G.pathLaw x) +
      ∫ γ in {γ : Path d | (s : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ}ᶜ,
        exitPayoffFunctional U f γ ∂G.pathLaw x := by
  let K := G.pathLaw
  have : IsMarkovKernel K := G.pathLaw_isMarkovKernel
  let E := {γ : Path d | (s : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ}
  have hEc : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s]
      E := MarkovProcess.ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU s
  have hE : MeasurableSet E := MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU s
  have hFm := measurable_exitPayoffFunctional U hU f hf
  have hFb : ∀ γ, ‖exitPayoffFunctional U f γ‖ ≤ B := fun γ => by
    rw [Real.norm_eq_abs]
    exact hB _
  have hint : Integrable (exitPayoffFunctional U f) (K x) :=
    Integrable.of_bound hFm.aestronglyMeasurable B (Eventually.of_forall hFb)
  have hfdd := EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h₀ h₁ G
  let μ := (K x).restrict E
  let Q := Kernel.comap K (pathPosition s) (measurable_pathPosition s)
  have hshift : Measurable (MarkovProcess.ContinuousPath.shift (alpha := Vec d) s) :=
    MarkovProcess.ContinuousPath.measurable_shift_fixed s
  have hr : μ.map (MarkovProcess.ContinuousPath.shift s) = Q ∘ₘ μ :=
    MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift
      (EinsteinFull.u2RegularC0KernelSemigroup hd ω lam L hL hω)
      (EinsteinFull.u2RegularC0KernelSemigroup_isFeller hd ω lam L hL hω)
      (EinsteinFull.u2_regular_kernel_conservative hd ω lam L hL hω)
      ⟨fun _ => 0, continuous_const⟩ K hfdd x s E hEc
  have hint' : Integrable (exitPayoffFunctional U f)
      ((Q ∘ₖ Kernel.const Unit μ) ()) := by
    rw [← Measure.comp_eq_comp_const_apply, ← hr]
    exact Integrable.of_bound hFm.aestronglyMeasurable B (Eventually.of_forall hFb)
  have hset : ∫ γ in E, exitPayoffFunctional U f γ ∂K x =
      ∫ γ in E, exitPayoff G U f (γ s) ∂K x := by
    calc ∫ γ in E, exitPayoffFunctional U f γ ∂K x
        = ∫ γ in E, exitPayoffFunctional U f (MarkovProcess.ContinuousPath.shift s γ) ∂K x := by
          apply setIntegral_congr_ae hE
          filter_upwards [hfin] with γ hγ hγE
          exact (exitPayoffFunctional_shift U f γ s hγE hγ).symm
      _ = ∫ γ, exitPayoffFunctional U f γ ∂(μ.map (MarkovProcess.ContinuousPath.shift s)) :=
          (integral_map hshift.aemeasurable hFm.aestronglyMeasurable).symm
      _ = ∫ γ, exitPayoffFunctional U f γ ∂((Q ∘ₖ Kernel.const Unit μ) ()) := by
          rw [hr, Measure.comp_eq_comp_const_apply]
      _ = ∫ γ, ∫ η, exitPayoffFunctional U f η ∂Q γ ∂μ := by
          rw [Kernel.integral_comp hint', Kernel.const_apply]
      _ = ∫ γ in E, exitPayoff G U f (γ s) ∂K x := rfl
  rw [← hset]
  exact (integral_add_compl hE hint).symm


/-- The locality exit time is the path exit time. -/
theorem localityExitTime_eq_exitTime (U : Set (Vec d)) (γ : Path d) :
    localityExitTime U γ = MarkovProcess.ContinuousPath.exitTime U γ := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le_of_le t (iInf_le _ ht)
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ t ht

/-- A transition average after a short time approximates the exit payoff, up to twice
the payoff bound times the probability of an exit before that time. -/
theorem abs_exitPayoff_sub_transition_le
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (f : Vec d → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B) (x : Vec d)
    (hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) (s : ℝ≥0) :
    |exitPayoff G U f x - ∫ γ, exitPayoff G U f (γ s) ∂G.pathLaw x| ≤
      2 * B * (G.pathLaw x).real
        {γ : Path d | MarkovProcess.ContinuousPath.exitTime U γ ≤ (s : ℝ≥0∞)} := by
  let K := G.pathLaw
  have : IsMarkovKernel K := G.pathLaw_isMarkovKernel
  let E := {γ : Path d | (s : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ}
  have hE : MeasurableSet E := MarkovProcess.ContinuousPath.measurableSet_lt_exitTime U hU s
  have hEc : Eᶜ = {γ : Path d | MarkovProcess.ContinuousPath.exitTime U γ ≤ (s : ℝ≥0∞)} := by
    ext γ
    simp [E]
  have hFm := measurable_exitPayoffFunctional U hU f hf
  have hHm : Measurable (fun γ : Path d => exitPayoff G U f (γ s)) :=
    (measurable_exitPayoff G U hU f hf).comp (measurable_pathPosition s)
  have hh : ∀ y, |exitPayoff G U f y| ≤ B := abs_exitPayoff_le G U f B hB
  have hFint : Integrable (exitPayoffFunctional U f) (K x) :=
    Integrable.of_bound hFm.aestronglyMeasurable B
      (Eventually.of_forall fun γ => by rw [Real.norm_eq_abs]; exact hB _)
  have hHint : Integrable (fun γ : Path d => exitPayoff G U f (γ s)) (K x) :=
    Integrable.of_bound hHm.aestronglyMeasurable B
      (Eventually.of_forall fun γ => by rw [Real.norm_eq_abs]; exact hh _)
  have hmarkov := exitPayoff_markov G U hU f hf B hB x hfin s
  have hsplit := (integral_add_compl hE hHint).symm
  rw [hmarkov, hsplit]
  have hdiff : (∫ γ in Eᶜ, exitPayoffFunctional U f γ ∂K x) -
      ∫ γ in Eᶜ, exitPayoff G U f (γ s) ∂K x =
      ∫ γ in Eᶜ, (exitPayoffFunctional U f γ - exitPayoff G U f (γ s)) ∂K x :=
    (integral_sub hFint.integrableOn hHint.integrableOn).symm
  have hbound : ‖∫ γ in Eᶜ, (exitPayoffFunctional U f γ - exitPayoff G U f (γ s)) ∂K x‖ ≤
      (2 * B) * (K x).real Eᶜ := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _)
    intro γ _
    rw [Real.norm_eq_abs]
    calc |exitPayoffFunctional U f γ - exitPayoff G U f (γ s)|
        ≤ |exitPayoffFunctional U f γ| + |exitPayoff G U f (γ s)| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hh _)
      _ = 2 * B := by ring
  rw [Real.norm_eq_abs] at hbound
  rw [← hEc]
  calc |(∫ γ in E, exitPayoff G U f (γ s) ∂K x) + (∫ γ in Eᶜ, exitPayoffFunctional U f γ ∂K x) -
        ((∫ γ in E, exitPayoff G U f (γ s) ∂K x) +
          ∫ γ in Eᶜ, exitPayoff G U f (γ s) ∂K x)|
      = |(∫ γ in Eᶜ, exitPayoffFunctional U f γ ∂K x) -
          ∫ γ in Eᶜ, exitPayoff G U f (γ s) ∂K x| := by ring_nf
    _ ≤ 2 * B * (K x).real Eᶜ := by rw [hdiff]; exact hbound

/-- The exit payoff of a bounded measurable payoff is continuous inside the open set,
provided exits are almost surely finite. -/
theorem continuousOn_exitPayoff (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (f : Vec d → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B)
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) :
    ContinuousOn (exitPayoff G U f) U := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hhm := measurable_exitPayoff G U hU f hf
  have hh : ∀ y, |exitPayoff G U f y| ≤ B := abs_exitPayoff_le G U f B hB
  apply continuousOn_of_locally_uniform_approx_of_continuousWithinAt
  intro x hx v hv
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_uniformity_dist.mp hv
  have hden : 0 < 2 * B + 1 := by positivity
  obtain ⟨δ, ρ, hδ, hρ, hexit⟩ :=
    EinsteinFull.s1_supplied_killed_exit_probability_locally_uniform hd L hL ω hω lam h₀ h₁ G
      U hU x hx (ε / (2 * B + 1)) (div_pos hε hden)
  let s : ℝ≥0 := Real.toNNReal (δ / 2)
  have hs : 0 < s := Real.toNNReal_pos.mpr (by linarith)
  have hsδ : (s : ℝ) < δ := by
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  let F : Vec d → ℝ := fun y => ∫ z, exitPayoff G U f z ∂G.transitionKernel s y
  have hFcont : Continuous F := by
    have hcan := EinsteinFull.s6_supplied_gmp_transition_eq_canonical_unconditional hd ω lam L
      hL hω h₀ h₁ G s
    simp only [F, hcan]
    exact EinsteinFull.u4_regular_signed_kernel_strongFeller hd ω lam L hL hω s hs _ hhm B hh
  have hFeq : ∀ y, F y = ∫ γ, exitPayoff G U f (γ s) ∂G.pathLaw y := by
    intro y
    simp only [F]
    rw [← G.pathLaw_endpoint s y, integral_map (measurable_pathPosition s).aemeasurable
      hhm.aestronglyMeasurable]
    rfl
  have hnear : {y : Vec d | euclideanNorm (y - x) < ρ} ∈ 𝓝[U] x := by
    apply nhdsWithin_le_nhds
    apply (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const).mem_nhds
    simp only [Set.mem_ofPred_eq]
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  refine ⟨_, hnear, F, hFcont.continuousWithinAt, ?_⟩
  intro y hy
  apply hεv
  have happrox := abs_exitPayoff_sub_transition_le G U hU f hf B hB y (hfin y) s
  have hprob := hexit y hy s hsδ
  have hset : {γ : Path d | localityExitTime U γ ≤ (s : ℝ≥0∞)} =
      {γ : Path d | MarkovProcess.ContinuousPath.exitTime U γ ≤ (s : ℝ≥0∞)} := by
    ext γ
    simp only [Set.mem_ofPred_eq, localityExitTime_eq_exitTime]
  rw [hset] at hprob
  have hprob' : (G.pathLaw y).real
      {γ : Path d | MarkovProcess.ContinuousPath.exitTime U γ ≤ (s : ℝ≥0∞)} <
      ε / (2 * B + 1) := hprob
  rw [Real.dist_eq, hFeq y]
  calc |exitPayoff G U f y - ∫ γ, exitPayoff G U f (γ s) ∂G.pathLaw y|
      ≤ 2 * B * (G.pathLaw y).real
          {γ : Path d | MarkovProcess.ContinuousPath.exitTime U γ ≤ (s : ℝ≥0∞)} := happrox
    _ ≤ 2 * B * (ε / (2 * B + 1)) :=
        mul_le_mul_of_nonneg_left hprob'.le (by linarith)
    _ < (2 * B + 1) * (ε / (2 * B + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) (div_pos hε hden)
    _ = ε := by field_simp

end EinsteinFull.Regeneration
