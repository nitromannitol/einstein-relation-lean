import EinsteinFull.Regeneration.LaterCoordinateVelocity

/-!
# Measurability of cycle maxima

The absolute coordinate maximum over a finite interval varies continuously with its length
and path. Composing with regeneration times makes the literal later-cycle maximum measurable.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The maximum absolute coordinate displacement over an initial time interval. -/
noncomputable def absoluteCoordinateMaximum {d : ℕ} (i : Fin d) (t : ℝ≥0) (γ : Path d) : ℝ :=
  sSup ((fun u : ℝ≥0 => |γ u i - γ 0 i|) '' Set.Icc 0 t)

private theorem image_Icc_rescale (f : ℝ≥0 → ℝ) (t : ℝ≥0) :
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

/-- The absolute coordinate maximum is jointly continuous in time and path. -/
theorem continuous_absoluteCoordinateMaximum {d : ℕ} (i : Fin d) :
    Continuous (fun p : ℝ≥0 × Path d => absoluteCoordinateMaximum i p.1 p.2) := by
  have hK : IsCompact (Set.Icc (0 : ℝ≥0) 1) := isCompact_Icc
  have hjoint : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 =>
      |q.1.2 (q.1.1 * q.2) i - q.1.2 0 i| := by
    have hA : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 := continuous_fst.snd
    have hB : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.1 * q.2 :=
      continuous_fst.fst.mul continuous_snd
    have hE : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 (q.1.1 * q.2) := hA.eval hB
    have hC : Continuous fun q : (ℝ≥0 × Path d) × ℝ≥0 => q.1.2 0 :=
      (continuous_eval_const (0 : ℝ≥0)).comp hA
    exact (((continuous_apply i).comp hE).sub ((continuous_apply i).comp hC)).abs
  have hmain : Continuous fun p : ℝ≥0 × Path d =>
      sSup ((fun r : ℝ≥0 => |p.2 (p.1 * r) i - p.2 0 i|) '' Set.Icc (0 : ℝ≥0) 1) :=
    IsCompact.continuous_sSup
      (f := fun (p : ℝ≥0 × Path d) (r : ℝ≥0) => |p.2 (p.1 * r) i - p.2 0 i|) hK hjoint
  refine hmain.congr ?_
  intro p
  exact congrArg sSup (image_Icc_rescale (fun u : ℝ≥0 => |p.2 u i - p.2 0 i|) p.1).symm

/-- The absolute maximum over each literal later regeneration cycle is measurable. -/
theorem measurable_laterCoordinateMaximum {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i j : Fin d) (k : ℕ) : Measurable (laterCoordinateMaximum Δ lam R i j k) := by
  have hτ (n : ℕ) := ((measurable_regenerationTime Δ lam R i n).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))).ennreal_toNNReal
  have hshift : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      (sampleTimeShift Δ ωz.2 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal).1) :=
    ((measurable_sampleTimeShift Δ).comp ((hτ (k + 1)).prodMk measurable_snd)).fst
  have hlen := (hτ (k + 2)).sub (hτ (k + 1))
  have h := (continuous_absoluteCoordinateMaximum j).measurable.comp (hlen.prodMk hshift)
  convert h using 1
  funext ωz
  simp [laterCoordinateMaximum, absoluteCoordinateMaximum, sampleTimeShift, pathTimeShift]

end EinsteinFull.Regeneration
