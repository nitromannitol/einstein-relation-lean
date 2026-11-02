import EinsteinFull.Calculus.VolterraSeriesSupport
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Force-disc analyticity of bounded Volterra equations

Neumann inversion is analytic wherever the perturbation norm is below one.
Left composition gives the same conclusion in operator norm. An elementary
square-root subdivision estimate supports extension by the semigroup law.
-/

open Filter
open scoped Topology
noncomputable section
namespace EinsteinFull
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Bounded linear perturbation solutions are analytic throughout their Neumann disc. -/
theorem analyticAt_of_eq_add_smul_of_norm_lt_one
    (V : E →L[ℂ] E) (b : E) (u : ℂ → E) (z₀ : ℂ)
    (he : ∀ z, u z = b + z • V (u z)) (hs : ‖z₀ • V‖ < 1) :
    AnalyticAt ℂ u z₀ := by
  have hi : AnalyticAt ℂ (fun z : ℂ => 1 - z • V) z₀ :=
    analyticAt_const.sub (analyticAt_id.fun_smul analyticAt_const)
  have hu : IsUnit (1 - z₀ • V) := isUnit_one_sub_of_norm_lt_one hs
  have hinv : AnalyticAt ℂ (fun z : ℂ => Ring.inverse (1 - z • V)) z₀ := by
    exact (analyticAt_inverse (𝕜 := ℂ) hu.unit).comp_of_eq hi hu.unit_spec.symm
  have ha : AnalyticAt ℂ (fun z : ℂ => Ring.inverse (1 - z • V) b) z₀ :=
    ((ContinuousLinearMap.apply ℂ E b).analyticAt _).comp hinv
  apply ha.congr
  have hn : ∀ᶠ z : ℂ in 𝓝 z₀, ‖z • V‖ < 1 :=
    ((continuous_id.smul continuous_const).norm.tendsto z₀).eventually
      (eventually_lt_nhds hs)
  filter_upwards [hn] with z hz
  exact (eq_inverse_one_sub_smul_of_eq_add V z (u z) b (he z) hz).symm

/-- Left composition gives operator-norm analyticity throughout the Neumann disc. -/
theorem analyticAt_clm_of_eq_add_comp_smul_of_norm_lt_one
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (V : E →L[ℂ] E) (b : F →L[ℂ] E) (u : ℂ → F →L[ℂ] E) (z₀ : ℂ)
    (he : ∀ z, u z = b + z • V.comp (u z)) (hs : ‖z₀ • V‖ < 1) :
    AnalyticAt ℂ u z₀ := by
  apply analyticAt_of_eq_add_smul_of_norm_lt_one
    ((ContinuousLinearMap.compL ℂ F E E) V) b u z₀ he
  apply lt_of_le_of_lt ?_ hs
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro A
  change ‖(z₀ • V).comp A‖ ≤ ‖z₀ • V‖ * ‖A‖
  exact (z₀ • V).opNorm_comp_le A

/-- Arbitrarily fine time subdivisions make any fixed square-root perturbation bound small. -/
theorem exists_pos_nat_mul_sqrt_div_lt_one (A t : ℝ) :
    ∃ n : ℕ, 0 < n ∧ A * Real.sqrt (t / n) < 1 := by
  have hl : Tendsto (fun n : ℕ => A * Real.sqrt (t / n)) atTop (𝓝 0) := by
    have h := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp
      (tendsto_const_div_atTop_nhds_zero_nat t)).const_mul A
    rw [Real.sqrt_zero, mul_zero] at h
    exact h
  exact ((eventually_gt_atTop (0 : ℕ)).and
    (hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))).exists

end EinsteinFull
