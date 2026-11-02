import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal BigOperators

namespace EinsteinRelation.Regeneration

/-! # Continuity of the coordinate maximum

Source: `paper/main.tex:278–282`, the running maximum
`M(t) = sup_{0 ≤ s ≤ t} e₁ · (Y_s - Y_0)` (`regen.hitting`). For a continuous path `γ`
and a coordinate `i`, `M(t)` is the supremum of the coordinate displacement over the
compact interval `[0, t]`. Rescaling time to the fixed compact interval `[0, 1]` makes
the parameter set independent of `t`, and joint continuity of path evaluation then
finishes the proof. No other claim of the paper is used here.
-/

/-- The image of `[0, t]` under `f` is the image of `[0, 1]` under `r ↦ f (t * r)`.
For `t = 0` both sides are the singleton `{f 0}`, and the witness is `r = 0`. -/
private theorem image_Icc_eq_image_rescaled (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
    f '' Set.Icc (0 : ℝ≥0) t = (fun r : ℝ≥0 => f (t * r)) '' Set.Icc (0 : ℝ≥0) 1 := by
  ext y
  constructor
  · rintro ⟨u, ⟨hu0, hut⟩, rfl⟩
    by_cases ht : t = 0
    · subst ht
      have hu : u = 0 := le_antisymm hut hu0
      exact ⟨0, ⟨zero_le, zero_le⟩, by simp [hu]⟩
    · refine ⟨u / t, ⟨zero_le, div_le_one_of_le₀ hut zero_le⟩, ?_⟩
      show f (t * (u / t)) = f u
      rw [mul_div_cancel₀ u ht]
  · rintro ⟨r, ⟨_, hr1⟩, rfl⟩
    exact ⟨t * r, ⟨zero_le, mul_le_of_le_one_right zero_le hr1⟩, rfl⟩

/-- Joint continuity of `(t, γ) ↦ M(t)` (`paper/main.tex:280–281`) for a fixed
coordinate `i`, where `M(t)` is the supremum of `s ↦ γ s i - γ 0 i` over `[0, t]`.
Because the time is a coordinate of the pair, composing with a continuous path-dependent
finite time `T(γ)` gives continuity of `γ ↦ M(T(γ))`. -/
theorem continuous_coordinate_maximum {d : ℕ} (i : Fin d) :
    Continuous (fun p : ℝ≥0 × Path d =>
      sSup ((fun u : ℝ≥0 => p.2 u i - p.2 0 i) '' Set.Icc (0 : ℝ≥0) p.1)) := by
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) 1) := isCompact_Icc
  have hjoint : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 =>
      q.1.2 (q.1.1 * q.2) i - q.1.2 0 i := by
    have hA : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 := continuous_fst.snd
    have hB : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.1 * q.2 :=
      continuous_fst.fst.mul continuous_snd
    have hE : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 (q.1.1 * q.2) :=
      hA.eval hB
    have hC : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 0 :=
      (continuous_eval_const (0 : ℝ≥0)).comp hA
    exact ((continuous_apply i).comp hE).sub ((continuous_apply i).comp hC)
  have hmain : Continuous fun p : ℝ≥0 × Path d =>
      sSup ((fun r : ℝ≥0 => p.2 (p.1 * r) i - p.2 0 i) '' Set.Icc (0 : ℝ≥0) 1) :=
    IsCompact.continuous_sSup
      (f := fun (p : ℝ≥0 × Path d) (r : ℝ≥0) => p.2 (p.1 * r) i - p.2 0 i) hK hjoint
  refine hmain.congr ?_
  intro p
  exact congrArg sSup
    (image_Icc_eq_image_rescaled (fun u : ℝ≥0 => p.2 u i - p.2 0 i) p.1).symm

end EinsteinRelation.Regeneration
