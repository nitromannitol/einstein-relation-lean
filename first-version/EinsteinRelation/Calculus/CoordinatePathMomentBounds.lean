import EinsteinRelation.Calculus.CoordinatePathMeasurability
import EinsteinRelation.Correctors.StationaryParameterAverages

/-! # Finite moments of concrete coordinate path primitives

Source: `paper/main.tex:1028–1029`. The literal path integral costs the
length of the corresponding coordinate segment in every finite moment.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation

/-- Segment length controls the moment of the actual coordinate primitive
(`paper/main.tex:1028–1029`). -/
theorem eLpNorm_coordinatePathFlux_bound {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : FieldPair d → ℝ} (hf : Measurable f)
    (z : Vec d) (i : Fin d) :
    eLpNorm (fun ω => coordinatePathFlux f z ω i) p Q ≤
      ENNReal.ofReal |z i| * eLpNorm f p Q := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  haveI : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hT : Measurable (fun t : ℝ => coordinateSegment z i (t * z i)) :=
    (continuous_coordinateSegment_unit i).measurable.comp (measurable_const.prodMk measurable_id)
  have hb := Correctors.eLpNorm_integral_stationary_param_le hQ ν hp hpt hf hT
    (measurable_const (a := (1 : ℝ))) (fun _ => by norm_num : ∀ _ : ℝ, |(1 : ℝ)| ≤ 1)
  simp only [one_mul] at hb
  have heq : (fun ω => coordinatePathFlux f z ω i) = z i •
      (fun ω => ∫ t, f (translate (coordinateSegment z i (t * z i)) ω) ∂ν) := by
    funext ω
    rw [coordinatePathFlux_eq_unit_integral,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  rw [heq, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs]
  exact mul_le_mul_right hb _

end EinsteinRelation
