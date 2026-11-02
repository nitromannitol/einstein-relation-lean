import EinsteinRelation.Diffusion.Basic
import MarkovProcess.Path.ExitTime
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Every continuous path stays in all sufficiently large Euclidean balls through a
fixed horizon, so its canonical truncated exit times equal their horizons. -/
theorem physical_path_euclidean_ball_exit_exhaustion :
∀ {d : ℕ} (γ : Path d) (T : ℝ≥0),
  ∀ᶠ n : ℕ in atTop, ∀ t : ℝ≥0, t ≤ T →
    MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : Vec d | euclideanNorm y < (n + 1 : ℝ)} t γ = t := by
  intro d γ T
  have hc : Continuous (fun s : ℝ≥0 => euclideanNorm (γ s)) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp γ.continuous).mul
          ((continuous_apply i).comp γ.continuous))
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image
    (hc.continuousOn : ContinuousOn (fun s : ℝ≥0 => euclideanNorm (γ s)) (Icc 0 T))
  obtain ⟨N, hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with n hn
  intro t ht
  have hbound : ∀ s : ℝ≥0, s ≤ T → euclideanNorm (γ s) < (n + 1 : ℝ) := by
    intro s hs
    have hsB : euclideanNorm (γ s) ≤ B := hB ⟨s, ⟨bot_le, hs⟩, rfl⟩
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hexit : (t : ℝ≥0∞) ≤ MarkovProcess.ContinuousPath.exitTime
      {y : Vec d | euclideanNorm y < (n + 1 : ℝ)} γ := by
    apply le_sInf
    rintro u ⟨s, rfl, hs⟩
    have hts : t ≤ s := by
      by_contra hnot
      exact hs (hbound s ((le_of_lt (lt_of_not_ge hnot)).trans ht))
    exact_mod_cast hts
  apply WithTop.coe_injective
  rw [MarkovProcess.ContinuousPath.coe_exitTimeTrunc, min_eq_right]
  exact hexit
end EinsteinFull.Blueprint
