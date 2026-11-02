import EinsteinRelation.Diffusion.Basic
import Mathlib.Topology.Order.Compact
open EinsteinRelation MeasureTheory Set
open scoped NNReal ENNReal
namespace EinsteinRelation.Regeneration

/-!
Deterministic closedness prerequisite for the good-passage events, from
`paper/main.tex:289--293`: the coordinate-`i` oscillation of a path over the
interval `[s, t]`, measured from `γ s`, is at most `R / 2`.

The interval endpoints vary with the point of the space, so the family of
conditions over `u ∈ [s, t]` is reparameterized by `r ∈ [0, 1]` through
`u = s + (t - s) * r`. Each `r`-condition is closed in `((s, t), γ)`, and the
intersection over `r` together with `s ≤ t` gives the closed set.
-/

/-- The set of endpoint-and-path pairs `((s, t), γ)` with `s ≤ t` whose
coordinate-`i` oscillation over `[s, t]` from `γ s` is at most `R / 2` is closed.
This is the deterministic closedness fact behind the good-passage condition
(`paper/main.tex:289--293`). -/
theorem isClosed_good_passage_interval {d : ℕ} (i : Fin d) (R : ℝ) :
    IsClosed {p : (ℝ≥0 × ℝ≥0) × Path d |
      p.1.1 ≤ p.1.2 ∧ ∀ u ∈ Icc p.1.1 p.1.2,
        |p.2 u i - p.2 p.1.1 i| ≤ R / 2} := by
  -- Reparameterization of `[s, t]` by `r ∈ [0, 1]`, valid under `s ≤ t`.
  have hreparam : ∀ (s t : ℝ≥0) (g : ℝ≥0 → ℝ) (c : ℝ), s ≤ t →
      ((∀ u ∈ Icc s t, g u ≤ c) ↔ ∀ r ∈ Icc (0 : ℝ≥0) 1, g (s + (t - s) * r) ≤ c) := by
    intro s t g c hst
    constructor
    · intro hg r hr
      refine hg (s + (t - s) * r) ⟨le_add_of_nonneg_right zero_le, ?_⟩
      calc s + (t - s) * r ≤ s + (t - s) :=
            add_le_add le_rfl (mul_le_of_le_one_right zero_le hr.2)
        _ = t := add_tsub_cancel_of_le hst
    · intro hg u hu
      obtain ⟨hsu, hut⟩ := hu
      have hkey : (t - s) * ((u - s) * (t - s)⁻¹) = u - s := by
        by_cases h : t - s = 0
        · have hus : u - s = 0 :=
            tsub_eq_zero_iff_le.mpr (le_trans hut (tsub_eq_zero_iff_le.mp h))
          simp [h, hus]
        · rw [mul_left_comm (t - s) (u - s) (t - s)⁻¹, mul_inv_cancel₀ h, mul_one]
      have hrep : s + (t - s) * ((u - s) * (t - s)⁻¹) = u := by
        rw [hkey, add_tsub_cancel_of_le hsu]
      have hmem : (u - s) * (t - s)⁻¹ ∈ Icc (0 : ℝ≥0) 1 := by
        refine ⟨zero_le, ?_⟩
        by_cases h : t - s = 0
        · simp [h]
        · calc (u - s) * (t - s)⁻¹ ≤ (t - s) * (t - s)⁻¹ :=
              mul_le_mul_of_nonneg_right (tsub_le_tsub_right hut s) zero_le
            _ = 1 := mul_inv_cancel₀ h
      have h := hg _ hmem
      rw [hrep] at h
      exact h
  have hset : {p : (ℝ≥0 × ℝ≥0) × Path d |
      p.1.1 ≤ p.1.2 ∧ ∀ u ∈ Icc p.1.1 p.1.2,
        |p.2 u i - p.2 p.1.1 i| ≤ R / 2} =
      {p : (ℝ≥0 × ℝ≥0) × Path d | p.1.1 ≤ p.1.2} ∩
        (⋂ r ∈ Icc (0 : ℝ≥0) 1, {p : (ℝ≥0 × ℝ≥0) × Path d |
          |p.2 (p.1.1 + (p.1.2 - p.1.1) * r) i - p.2 p.1.1 i| ≤ R / 2}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hst, hu⟩
      exact ⟨hst, (hreparam _ _ (fun u => |p.2 u i - p.2 p.1.1 i|) (R / 2) hst).mp hu⟩
    · rintro ⟨hst, hr⟩
      exact ⟨hst, (hreparam _ _ (fun u => |p.2 u i - p.2 p.1.1 i|) (R / 2) hst).mpr hr⟩
  rw [hset]
  apply IsClosed.inter
  · exact isClosed_le continuous_fst.fst continuous_fst.snd
  · apply isClosed_biInter
    intro r _
    refine isClosed_le ?_ continuous_const
    have hT : Continuous fun p : (ℝ≥0 × ℝ≥0) × Path d => p.1.1 + (p.1.2 - p.1.1) * r :=
      continuous_fst.fst.add ((continuous_fst.snd.sub continuous_fst.fst).mul continuous_const)
    have hcur : Continuous fun p : (ℝ≥0 × ℝ≥0) × Path d =>
        p.2 (p.1.1 + (p.1.2 - p.1.1) * r) i :=
      (continuous_apply i).comp (continuous_snd.eval hT)
    have hbase : Continuous fun p : (ℝ≥0 × ℝ≥0) × Path d => p.2 p.1.1 i :=
      (continuous_apply i).comp (continuous_snd.eval continuous_fst.fst)
    exact (hcur.sub hbase).abs

end EinsteinRelation.Regeneration
