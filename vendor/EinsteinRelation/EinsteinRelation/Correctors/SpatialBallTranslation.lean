import EinsteinRelation.Correctors.SpatialBallLocalL2
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation on Euclidean spatial balls

Source: `paper/main.tex:718-723`. These are coordinate Lebesgue balls for
the Euclidean norm, including when the ambient coordinate space has a
different default norm. Translation preserves their restricted measures.
-/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM TimeChange

/-- Adding the center transports the restricted origin-ball measure exactly. -/
theorem measurePreserving_add_center_ball {d : ℕ} (z : Vec d) (R : ℝ) :
    MeasurePreserving (fun x : Vec d => x + z)
      (volume.restrict (ball 0 R)) (volume.restrict (ball z R)) := by
  refine ⟨measurable_add_const z, ?_⟩
  have hm : MeasurableSet (ball z R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hpre : (fun x : Vec d => x + z) ⁻¹' ball z R = ball 0 R := by
    ext x
    simp [ball, Set.mem_setOf_eq, add_sub_cancel_right, sub_zero]
  rw [← hpre, ← Measure.restrict_map (measurable_add_const z) hm,
    map_add_right_eq_self volume z]

/-- Spatial translation preserves the exact local `L^p` norm on its ball. -/
theorem eLpNorm_add_center_ball {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Vec d → E) {p : ℝ≥0∞} (z : Vec d) (R : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (ball z R))) :
    eLpNorm (fun x => f (x + z)) p (volume.restrict (ball 0 R)) =
      eLpNorm f p (volume.restrict (ball z R)) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_center_ball z R)

/-- A translated local norm is bounded by the norm on any larger origin ball. -/
theorem eLpNorm_add_center_ball_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Vec d → E) {p : ℝ≥0∞} (z : Vec d) (R S : ℝ)
    (hRS : R + euclideanNorm z ≤ S)
    (hf : AEStronglyMeasurable f (volume.restrict (ball 0 S))) :
    eLpNorm (fun x => f (x + z)) p (volume.restrict (ball 0 R)) ≤
      eLpNorm f p (volume.restrict (ball 0 S)) := by
  have hsub : ball z R ⊆ ball (0 : Vec d) S := by
    intro x hx
    have htri := euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    change euclideanNorm (x - z) < R at hx
    change euclideanNorm (x - 0) < S
    rw [sub_zero]
    linarith
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  rw [eLpNorm_add_center_ball f z R (hf.mono_measure hm)]
  exact eLpNorm_mono_measure f hm

/-- Translation preserves genuine local L² membership on every Euclidean ball. -/
theorem memLp_two_on_euclidean_balls_translation {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (u : Vec d → E)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (z : Vec d) :
    ∀ R : ℝ, 0 < R → MemLp (fun x => u (x + z)) 2
      (volume.restrict (ball 0 R)) := by
  intro R hR
  have hsub : ball z R ⊆ ball (0 : Vec d) (R + euclideanNorm z) := by
    intro x hx
    have htri := euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at htri
    change euclideanNorm (x - z) < R at hx
    change euclideanNorm (x - 0) < R + euclideanNorm z
    rw [sub_zero]
    linarith
  have hpos : 0 < R + euclideanNorm z :=
    add_pos_of_pos_of_nonneg hR (Real.sqrt_nonneg _)
  have hmem := (hu (R + euclideanNorm z) hpos).mono_measure
    (Measure.restrict_mono_set (volume : Measure (Vec d)) hsub)
  exact hmem.comp_measurePreserving (measurePreserving_add_center_ball z R)

end EinsteinRelation.Correctors
