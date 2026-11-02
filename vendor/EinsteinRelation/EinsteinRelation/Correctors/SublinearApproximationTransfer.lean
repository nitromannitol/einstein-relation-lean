import EinsteinRelation.Correctors.NormalizedBallPoincare
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing sublinear oscillation through uniform approximation errors

Source: `paper/main.tex:693-698`. The approximation index is fixed before
sending the spatial radius to infinity. A uniform geometric gradient error
then makes the limiting normalized oscillation arbitrarily small.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM

/-- A nonnegative radius-dependent quantity vanishes if every sufficiently
accurate approximation bounds it by a geometric error and a vanishing term. -/
theorem tendsto_zero_of_uniform_geometric_approximation
    (S : ℝ → ℝ) (A : ℕ → ℝ → ℝ) (C : ℝ)
    (hS : ∀ᶠ R in atTop, 0 ≤ S R)
    (hA : ∀ n, Tendsto (A n) atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ R : ℝ, 1 ≤ R →
      S R ≤ C * (1 / 2 : ℝ)^n + 2 * A n R) :
    Tendsto S atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact hS.mono fun R hR => ha.trans_le hR
  · intro ε hε
    have hgeo : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul C
    obtain ⟨n, hn, hsmall⟩ := (hbound.and
      (hgeo.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))).exists
    have hAn := (hA n).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
    filter_upwards [eventually_ge_atTop (1 : ℝ), hAn] with R hR hAR
    exact (hn R hR).trans_lt (by linarith)

/-- A squared, radius-normalized oscillation limit is the sublinearity
condition in the AKM corrector definition. -/
theorem sublinear_oscillation_of_squared_limit {d : ℕ} (u : Vec d → ℝ)
    (h : Tendsto (fun R : ℝ => (R^2)⁻¹ *
      (⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume))
        atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt
      (⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume))
        atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  dsimp only [Function.comp_def]
  rw [Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg R)), Real.sqrt_inv,
    Real.sqrt_sq_eq_abs, abs_of_pos hR]

end EinsteinRelation.Correctors
