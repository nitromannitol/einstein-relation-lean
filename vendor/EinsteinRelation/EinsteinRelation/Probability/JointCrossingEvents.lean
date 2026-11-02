import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Compact

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal BigOperators

/-! # Joint crossing events with a path-dependent level

Source: `paper/main.tex:278-306`, `regen.hitting` and `regen.D`. The hitting
times `T_u` and `T_{-R}` compare the displacement `e₁ · (Y_t - Y_0)` with a level.
Here the level is a real variable `u`. Each crossing event is the projection, along
the compact time interval `[0, T]`, of a closed inequality set in `((u, γ), t)`
built from a continuous function. Equality touches (`≤`) are kept, and the horizon
`T` is the actual finite time. A path-dependent level such as the `M(·) + R`
threshold of `V_{j+1}(a)` would enter by composing these sets with a map
`γ ↦ (level(γ), γ)`; this file does not prove that composition.
-/

namespace EinsteinRelation.Probability

/-- Joint continuity of `((u, γ), t) ↦ γ t i - γ 0 i` on the level-path space
times the compact interval `[0, T]`. -/
private theorem continuous_joint_crossing_eval {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    Continuous fun q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T =>
      q.1.2 (q.2 : ℝ≥0) i - q.1.2 0 i := by
  have hpos : Continuous fun q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T =>
      q.1.2 (q.2 : ℝ≥0) :=
    continuous_fst.snd.eval (continuous_subtype_val.comp continuous_snd)
  have hzero : Continuous fun q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T =>
      q.1.2 (0 : ℝ≥0) :=
    (continuous_eval_const (0 : ℝ≥0)).comp continuous_fst.snd
  exact ((continuous_apply i).comp hpos).sub ((continuous_apply i).comp hzero)

/-- The closed set of joint data `((u, γ), t)` with `γ t i - γ 0 i ≤ u`. -/
private theorem isClosed_joint_downcrossing_lift {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    IsClosed {q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T |
      q.1.2 (q.2 : ℝ≥0) i - q.1.2 0 i ≤ q.1.1} :=
  isClosed_le (continuous_joint_crossing_eval i T) continuous_fst.fst

/-- The closed set of joint data `((u, γ), t)` with `u ≤ γ t i - γ 0 i`. -/
private theorem isClosed_joint_upcrossing_lift {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    IsClosed {q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T |
      q.1.1 ≤ q.1.2 (q.2 : ℝ≥0) i - q.1.2 0 i} :=
  isClosed_le continuous_fst.fst (continuous_joint_crossing_eval i T)

/-- Projection of a closed subset of `X × [0, T]` along the compact time interval
is closed. -/
private theorem isClosed_image_fst_of_time {X : Type*} [TopologicalSpace X]
    (T : ℝ≥0) {S : Set (X × Set.Icc (0 : ℝ≥0) T)} (hS : IsClosed S) :
    IsClosed (Prod.fst '' S) := by
  have hK : CompactSpace (Set.Icc (0 : ℝ≥0) T) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact isClosedMap_fst_of_compactSpace _ hS

/-- The joint finite-horizon downcrossing event `{∃ t ∈ [0, T], γ t i - γ 0 i ≤ u}`
is closed in the pair `(u, γ)` (`paper/main.tex:300-306`, `regen.D`, with the level
`-R` replaced by a real variable `u`). -/
theorem isClosed_joint_downcrossing_by {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    IsClosed {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T,
      p.2 t i - p.2 0 i ≤ p.1} := by
  have hS := isClosed_joint_downcrossing_lift i T
  have himage : {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T,
      p.2 t i - p.2 0 i ≤ p.1} =
      Prod.fst '' {q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T |
        q.1.2 (q.2 : ℝ≥0) i - q.1.2 0 i ≤ q.1.1} := by
    ext p
    constructor
    · rintro ⟨t, ht, hle⟩
      exact ⟨(p, ⟨t, ht⟩), hle, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2.1, q.2.2, hq⟩
  rw [himage]
  exact isClosed_image_fst_of_time T hS

/-- The joint finite-horizon upcrossing event `{∃ t ∈ [0, T], u ≤ γ t i - γ 0 i}`
is closed in the pair `(u, γ)`. The inequality keeps equality touches. -/
theorem isClosed_joint_upcrossing_by {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    IsClosed {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T,
      p.1 ≤ p.2 t i - p.2 0 i} := by
  have hS := isClosed_joint_upcrossing_lift i T
  have himage : {p : ℝ × Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T,
      p.1 ≤ p.2 t i - p.2 0 i} =
      Prod.fst '' {q : (ℝ × Path d) × Set.Icc (0 : ℝ≥0) T |
        q.1.1 ≤ q.1.2 (q.2 : ℝ≥0) i - q.1.2 0 i} := by
    ext p
    constructor
    · rintro ⟨t, ht, hle⟩
      exact ⟨(p, ⟨t, ht⟩), hle, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2.1, q.2.2, hq⟩
  rw [himage]
  exact isClosed_image_fst_of_time T hS

end EinsteinRelation.Probability
