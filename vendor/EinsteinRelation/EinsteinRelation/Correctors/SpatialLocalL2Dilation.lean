import EinsteinRelation.Correctors.SpatialBallVolume
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Local square integrability under spatial dilation

Source: `paper/main.tex:693-702`. Positive spatial dilation sends the
Euclidean radius `R` to `r * R`; the Haar Jacobian preserves local L².
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positive dilation and constant multiplication preserve local spatial L². -/
theorem memLp_two_on_euclidean_balls_dilation {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E)
    (hf : ∀ R : ℝ, 0 < R → MemLp f 2 (volume.restrict (ball 0 R)))
    (r c : ℝ) (hr : 0 < r) :
    ∀ R : ℝ, 0 < R → MemLp (fun x => c • f (r • x)) 2
      (volume.restrict (ball 0 R)) := by
  intro R hR
  have hmeas (S : ℝ) : MeasurableSet (ball (0 : Vec d) S) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hI := (memLp_indicator_iff_restrict (hmeas (r * R))).mpr
    (hf (r * R) (mul_pos hr hR))
  have hJ : MemLp ((ball (0 : Vec d) (r * R)).indicator f) 2
      (Measure.map (fun x : Vec d => r • x) volume) := by
    rw [Measure.map_addHaar_smul volume hr.ne']
    exact hI.smul_measure ENNReal.ofReal_ne_top
  have hcomp := hJ.comp_of_map
    ((continuous_id.const_smul r).measurable.aemeasurable)
  have heq : (fun x : Vec d => (ball (0 : Vec d) (r * R)).indicator f (r • x)) =
      (ball (0 : Vec d) R).indicator (fun x => f (r • x)) := by
    funext x
    have hx : r • x ∈ ball (0 : Vec d) (r * R) ↔ x ∈ ball (0 : Vec d) R := by
      simp only [ball, Set.mem_setOf_eq, sub_zero, euclideanNorm_smul r hr.le]
      exact mul_lt_mul_iff_right₀ hr
    by_cases hxR : x ∈ ball (0 : Vec d) R
    · simp only [Set.indicator_of_mem hxR, Set.indicator_of_mem (hx.mpr hxR)]
    · simp only [Set.indicator_of_notMem hxR, Set.indicator_of_notMem (mt hx.mp hxR)]
  change MemLp (fun x => (ball (0 : Vec d) (r * R)).indicator f (r • x)) 2 volume at hcomp
  rw [heq] at hcomp
  exact ((memLp_indicator_iff_restrict (hmeas R)).mp hcomp).const_smul c

end EinsteinRelation.Correctors
