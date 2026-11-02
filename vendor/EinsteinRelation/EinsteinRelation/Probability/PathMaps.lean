import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Integral.Prod

open scoped NNReal ENNReal
namespace EinsteinRelation.Probability

/-! # Continuity of path shifts and recentering

Joint continuity for the compact-open topology on `Path d = C(ℝ≥0, Vec d)` of the
two path maps used by the coupled kernels and the future records:
the time shift `γ ↦ (u ↦ γ (t + u))` is the path part of `θ_t`
(`paper/main.tex:283–286`), and recentering `γ ↦ γ - x` is the path part of
`Y_{τ_k+t} - Y_{τ_k}` in the future record (`paper/main.tex:331–340`).
-/

/-- Joint continuity of the time shift `(t, γ) ↦ γ (t + ·)`, the path part of `θ_t`
(`paper/main.tex:283–286`). -/
theorem continuous_path_time_shift {d : ℕ} :
    Continuous (fun p : ℝ≥0 × Path d => (⟨fun u => p.2 (p.1 + u), p.2.continuous.comp (continuous_const.add continuous_id)⟩ : Path d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.snd).eval (continuous_fst.fst.add continuous_snd)

/-- Joint continuity of recentering `(x, γ) ↦ γ - x`, the path part of
`Y_{τ_k+·} - Y_{τ_k}` in the future record (`paper/main.tex:331–340`). -/
theorem continuous_path_recenter {d : ℕ} :
    Continuous (fun p : Vec d × Path d => (⟨fun t => p.2 t - p.1, p.2.continuous.sub continuous_const⟩ : Path d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.snd).eval continuous_snd).sub continuous_fst.fst

end EinsteinRelation.Probability
