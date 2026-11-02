import EinsteinRelation.External.GantertSection7Support
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace EinsteinRelation.External.GantertSection7Support

/-- Source `paper/main.tex:400–402`: finite-dimensional distributions commute with a spatial change of coordinates. -/
theorem iteratedMarkovCylinderIntegral_conjugate {d : ℕ}
    (e : Vec d ≃ᵐ Vec d) (K : ℝ≥0 → Kernel (Vec d) (Vec d))
    (increments : List ℝ≥0) (F : List (Vec d) → ℝ) (x : Vec d) :
    iteratedMarkovCylinderIntegral
      (fun t => ((K t).comap e e.measurable).map e.symm) increments F x =
      iteratedMarkovCylinderIntegral K increments (fun ys => F (ys.map e.symm)) (e x) := by
  induction increments generalizing K F x with
  | nil => simp [iteratedMarkovCylinderIntegral]
  | cons t ts ih =>
    simp only [iteratedMarkovCylinderIntegral]
    have hmeas_symm : Measurable e.symm := e.symm.measurable
    have h_measure : ((K t).comap e e.measurable).map e.symm x =
        Measure.map e.symm ((K t) (e x)) := by
      simp [Kernel.comap_apply, Kernel.map_apply _ hmeas_symm]
    rw [h_measure]
    rw [integral_map_equiv e.symm]
    have h_inner : ∀ z, iteratedMarkovCylinderIntegral
        (fun t' => ((K t').comap e e.measurable).map e.symm) ts (fun ys => F (e.symm z :: ys)) (e.symm z) =
        iteratedMarkovCylinderIntegral K ts (fun ys => F (e.symm z :: ys.map e.symm)) z := by
      intro z
      simpa [e.apply_symm_apply] using ih K (fun (ys : List (Vec d)) => F (e.symm z :: ys)) (e.symm z)
    have h_integrand : (fun (z : Vec d) =>
        iteratedMarkovCylinderIntegral (fun t' => ((K t').comap e e.measurable).map e.symm) ts
          (fun ys => F (e.symm z :: ys)) (e.symm z)) =
        (fun (z : Vec d) =>
          iteratedMarkovCylinderIntegral K ts (fun ys => F (e.symm z :: ys.map e.symm)) z) := by
      ext z; exact h_inner z
    rw [h_integrand]
    simp [List.map_cons]

end EinsteinRelation.External.GantertSection7Support
