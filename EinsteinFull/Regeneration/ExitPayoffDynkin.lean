import EinsteinFull.Regeneration.ExitPayoffBoundary

/-!
# Dynkin's formula at the exit time

For a smooth compactly supported payoff and an open set with integrable exit time, the
exit payoff differs from the payoff at the start by the expected integral of the
generator applied to the payoff along the path up to the exit.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- The truncated exit time is the exit time once the horizon exceeds it. -/
theorem exitTimeTrunc_eq_of_le {U : Set (Vec d)} {γ : Path d} {K : ℝ≥0}
    (hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hK : (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal ≤ K) :
    MarkovProcess.ContinuousPath.exitTimeTrunc U K γ =
      (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal := by
  apply ENNReal.coe_injective
  rw [MarkovProcess.ContinuousPath.coe_exitTimeTrunc_ennreal, ENNReal.coe_toNNReal hfin,
    min_eq_left]
  rw [← ENNReal.coe_toNNReal hfin]
  exact_mod_cast hK

/-- Dynkin's formula at the exit time from an open set with integrable exit time. -/
theorem exitPayoff_sub_eq_integral_generator
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (x : Vec d)
    (hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) :
    exitPayoff G U φ x - φ x =
      ∫ γ, (∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ (γ s.toNNReal)) ∂G.pathLaw x := by
  let K := G.pathLaw
  have : IsMarkovKernel K := G.pathLaw_isMarkovKernel
  have : IsProbabilityMeasure (K x) := G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have hfdd := EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam L hL hω h₀ h₁ G
  let Lg := physicalGenerator (firstCoordinateIndex hd) ω lam
  obtain ⟨B, hB0, hB⟩ := EinsteinFull.sbxS4_physicalGenerator_bounded hd
    (firstCoordinateIndex hd) (lt_of_lt_of_le zero_lt_one hL) hω lam hφ hφc
  have hLgm : Measurable (Lg φ) := measurable_physicalGenerator _ ω lam φ
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  let T : ℕ → Path d → ℝ≥0 := fun n =>
    MarkovProcess.ContinuousPath.exitTimeTrunc U (n : ℝ≥0)
  have hT : ∀ n, IsStoppingTime
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T n γ : WithTop ℝ≥0)) := fun n =>
    MarkovProcess.ContinuousPath.isStoppingTime_exitTimeTrunc U hU (n : ℝ≥0)
  have hTm : ∀ n, Measurable (T n) := fun n =>
    MarkovProcess.ContinuousPath.measurable_of_isStoppingTime (T n) (hT n)
  have hTle : ∀ n γ, T n γ ≤ (n : ℝ≥0) := fun n γ =>
    MarkovProcess.ContinuousPath.exitTimeTrunc_le U (n : ℝ≥0) γ
  -- the stopped functionals
  let F : ℕ → Path d → ℝ := fun n γ =>
    φ (γ (T n γ)) - ∫ s in (0 : ℝ)..(T n γ : ℝ), Lg φ (γ s.toNNReal)
  let Fτ : Path d → ℝ := fun γ =>
    exitPayoffFunctional U φ γ -
      ∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal, Lg φ (γ s.toNNReal)
  have hIbound : ∀ (r : ℝ), 0 ≤ r → ∀ γ : Path d,
      |∫ s in (0 : ℝ)..r, Lg φ (γ s.toNNReal)| ≤ B * r := by
    intro r hr γ
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
      (f := fun s => Lg φ (γ s.toNNReal)) (C := B) (fun s _ => by
        rw [Real.norm_eq_abs]
        exact hB _)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr] at h
    exact h
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact (hφ.continuous.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel (T n) (hT n))).sub
      (measurable_stopped_pathIntegral (Lg φ) hLgm (T n) (hTm n))
  have hFint : ∀ n, ∫ γ, F n γ ∂K x = φ x := by
    intro n
    have hD := EinsteinFull.u5_regular_physical_compensated_stopping_mean_zero hd ω lam L hL hω K
      hfdd x φ hφ hφc (T n) (hT n) (n : ℝ≥0) (hTle n)
    have hFi : Integrable (F n) (K x) := by
      refine Integrable.of_bound (hFm n).aestronglyMeasurable (Mφ + B * n)
        (Eventually.of_forall fun γ => ?_)
      rw [Real.norm_eq_abs]
      calc |F n γ| ≤ |φ (γ (T n γ))| + |∫ s in (0 : ℝ)..(T n γ : ℝ), Lg φ (γ s.toNNReal)| :=
            abs_sub _ _
        _ ≤ Mφ + B * (T n γ : ℝ) := by
            refine add_le_add ?_ (hIbound _ (T n γ).coe_nonneg γ)
            simpa [Real.norm_eq_abs] using hMφ _
        _ ≤ Mφ + B * n := by
            gcongr
            exact_mod_cast hTle n γ
    have hcomp : (fun γ => compensatedTest Lg φ (T n γ) γ) =ᵐ[K x] fun γ => F n γ - φ x := by
      filter_upwards [G.pathLaw_starts_at x] with γ hγ
      change γ 0 = x at hγ
      simp only [compensatedTest, F, hγ]
      ring
    rw [integral_congr_ae hcomp, integral_sub hFi (integrable_const _), integral_const] at hD
    have hone : (K x).real univ = 1 := by simp [measureReal_def]
    rw [hone, one_smul] at hD
    linarith
  -- convergence along the truncations
  have hlim : ∀ᵐ γ ∂K x, Tendsto (fun n => F n γ) atTop (𝓝 (Fτ γ)) := by
    filter_upwards [hfin] with γ hγ
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge ((MarkovProcess.ContinuousPath.exitTime U γ).toNNReal : ℝ)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hK : (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal ≤ (n : ℝ≥0) := by
      have : ((MarkovProcess.ContinuousPath.exitTime U γ).toNNReal : ℝ) ≤ n :=
        hN.trans (by exact_mod_cast hn)
      exact_mod_cast this
    have heq := exitTimeTrunc_eq_of_le hγ hK
    simp only [F, Fτ, T, heq, exitPayoffFunctional,
      MarkovProcess.ContinuousPath.untopD_exitTimeTop_eq_toNNReal U γ hγ]
    rfl
  have hdom : ∀ n, ∀ᵐ γ ∂K x, ‖F n γ‖ ≤ Mφ + B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal := by
    intro n
    filter_upwards [hfin] with γ hγ
    rw [Real.norm_eq_abs]
    calc |F n γ| ≤ |φ (γ (T n γ))| + |∫ s in (0 : ℝ)..(T n γ : ℝ), Lg φ (γ s.toNNReal)| :=
          abs_sub _ _
      _ ≤ Mφ + B * (T n γ : ℝ) := by
          refine add_le_add ?_ (hIbound _ (T n γ).coe_nonneg γ)
          simpa [Real.norm_eq_abs] using hMφ _
      _ ≤ Mφ + B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal := by
          gcongr
          have h := MarkovProcess.ContinuousPath.coe_exitTimeTrunc_ennreal U (n : ℝ≥0) γ
          have hle : ((T n γ : ℝ≥0) : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime U γ := by
            change ((MarkovProcess.ContinuousPath.exitTimeTrunc U (n : ℝ≥0) γ : ℝ≥0) : ℝ≥0∞) ≤ _
            rw [h]
            exact min_le_left _ _
          have := ENNReal.toReal_mono hγ hle
          simpa using this
  have hconv := tendsto_integral_of_dominated_convergence
    (fun γ => Mφ + B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
    (fun n => (hFm n).aestronglyMeasurable) ((integrable_const Mφ).add (hτ.const_mul B))
    hdom hlim
  have hconv' : Tendsto (fun _ : ℕ => φ x) atTop (𝓝 (∫ γ, Fτ γ ∂K x)) := by
    refine hconv.congr' (Eventually.of_forall fun n => ?_)
    exact hFint n
  have hFτ : ∫ γ, Fτ γ ∂K x = φ x := tendsto_nhds_unique hconv' tendsto_const_nhds
  have hPint : Integrable (exitPayoffFunctional U φ) (K x) :=
    Integrable.of_bound
      (measurable_exitPayoffFunctional U hU φ hφ.continuous.measurable).aestronglyMeasurable Mφ
      (Eventually.of_forall fun γ => hMφ _)
  have hIint : Integrable (fun γ => ∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal,
      Lg φ (γ s.toNNReal)) (K x) := by
    have hτm : Measurable (fun γ : Path d =>
        (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal) :=
      (MarkovProcess.ContinuousPath.measurable_exitTime U hU).ennreal_toNNReal
    refine Integrable.mono' (hτ.const_mul B)
      (measurable_stopped_pathIntegral (Lg φ) hLgm _ hτm).aestronglyMeasurable
      (Eventually.of_forall fun γ => ?_)
    rw [Real.norm_eq_abs]
    exact hIbound _ ENNReal.toReal_nonneg γ
  rw [integral_sub hPint hIint] at hFτ
  unfold exitPayoff
  change ∫ γ, exitPayoffFunctional U φ γ ∂K x - φ x = _
  linarith

end EinsteinFull.Regeneration
