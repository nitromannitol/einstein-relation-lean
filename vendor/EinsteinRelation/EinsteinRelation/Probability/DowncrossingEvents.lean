import EinsteinRelation.Diffusion.Basic
import Mathlib.Topology.Maps.Proper.Basic

open scoped NNReal

/-! # Downcrossing events on continuous paths

Source: `paper/main.tex:300-306`, `regen.D`. The downward hitting time
`T_{-R} = inf {t ≥ 0 : e₁ · (Y_t - Y_0) ≤ -R}` and the event `𝒟 = {T_{-R} = ∞}`
are the events of the continuous-path space `Path d`. The finite-horizon
downcrossing event is the projection of a closed sublevel set along the compact
time interval `[0, T]`; the all-time event is the complement of the countable
union of finite-horizon events over natural-number horizons.
-/

namespace EinsteinRelation.Probability

/-- Joint continuity of `(γ, t) ↦ γ t i - γ 0 i` on paths times the compact
interval `[0, T]`. -/
private theorem continuous_downcrossing_eval {d : ℕ} (i : Fin d) (T : ℝ≥0) :
    Continuous fun p : Path d × Set.Icc (0 : ℝ≥0) T => p.1 (p.2 : ℝ≥0) i - p.1 0 i := by
  have hpos : Continuous fun p : Path d × Set.Icc (0 : ℝ≥0) T => p.1 (p.2 : ℝ≥0) :=
    continuous_fst.eval (continuous_subtype_val.comp continuous_snd)
  have hzero : Continuous fun p : Path d × Set.Icc (0 : ℝ≥0) T => p.1 (0 : ℝ≥0) :=
    (continuous_eval_const (0 : ℝ≥0)).comp continuous_fst
  exact ((continuous_apply i).comp hpos).sub ((continuous_apply i).comp hzero)

/-- The finite-horizon downcrossing event `{∃ t ∈ [0, T], γ t i - γ 0 i ≤ -R}`
(`paper/main.tex:300-306`, `regen.D`, truncated at horizon `T`) is closed in the
compact-open topology on continuous paths. -/
theorem isClosed_downcrossing_by {d : ℕ} (i : Fin d) (R : ℝ) (T : ℝ≥0) :
    IsClosed {γ : Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T, γ t i - γ 0 i ≤ -R} := by
  have hK : CompactSpace (Set.Icc (0 : ℝ≥0) T) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hS : IsClosed {p : Path d × Set.Icc (0 : ℝ≥0) T |
      p.1 (p.2 : ℝ≥0) i - p.1 0 i ≤ -R} :=
    isClosed_le (continuous_downcrossing_eval i T) continuous_const
  have himage : {γ : Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) T, γ t i - γ 0 i ≤ -R} =
      Prod.fst '' {p : Path d × Set.Icc (0 : ℝ≥0) T |
        p.1 (p.2 : ℝ≥0) i - p.1 0 i ≤ -R} := by
    ext γ
    constructor
    · rintro ⟨t, ht, hle⟩
      exact ⟨(γ, ⟨t, ht⟩), hle, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2.1, p.2.2, hp⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ hS

/-- The all-time no-downcrossing event `{∀ t, -R < γ t i - γ 0 i}`
(`paper/main.tex:300-306`, `regen.D`, with `i = e₁`: the event `𝒟 = {T_{-R} = ∞}`)
is measurable. It is the complement of the union over natural-number horizons `n`
of the closed finite-horizon events, since every `t ≥ 0` lies below some `n`. -/
theorem measurableSet_no_downcrossing {d : ℕ} (i : Fin d) (R : ℝ) :
    MeasurableSet {γ : Path d | ∀ t : ℝ≥0, -R < γ t i - γ 0 i} := by
  have hcover : {γ : Path d | ∀ t : ℝ≥0, -R < γ t i - γ 0 i} =
      (⋃ n : ℕ, {γ : Path d | ∃ t ∈ Set.Icc (0 : ℝ≥0) (n : ℝ≥0), γ t i - γ 0 i ≤ -R})ᶜ := by
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion]
    constructor
    · rintro h ⟨n, t, _, hle⟩
      linarith [h t]
    · intro h t
      by_contra hcon
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact h ⟨n, t, ⟨zero_le, hn⟩, not_lt.mp hcon⟩
  rw [hcover]
  exact MeasurableSet.compl (MeasurableSet.iUnion fun n : ℕ =>
    (isClosed_downcrossing_by i R (n : ℝ≥0)).measurableSet)

end EinsteinRelation.Probability
