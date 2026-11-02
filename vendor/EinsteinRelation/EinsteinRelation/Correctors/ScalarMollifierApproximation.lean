import EinsteinRelation.Correctors.HorizontalMollifierRepresentative
import EinsteinRelation.Correctors.HorizontalMollifierApproximation

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The literal scalar orbit smoothing of a bounded measurable observable converges to that
observable in actual L². Source paper/main.tex:545–566. -/
theorem exists_scalarMollifier_Lp_approximation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hFm : Measurable F) (hFb : ∃ M : ℝ, ∀ ω, |F ω| ≤ M) (hF : MemLp F 2 Q) :
    ∃ hS : ∀ ε : ℝ, MemLp
      (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)) 2 Q,
    Filter.Tendsto (fun ε : ℝ => (hS ε).toLp
      (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε • x) ω)))
      (nhds 0) (nhds (hF.toLp F)) := by
  choose hS heq using exists_mollifier_representative_eq_translation_integral Q hQ hFm hFb hF
  refine ⟨hS, ?_⟩
  have h := tendsto_horizontalMollifier_translation_integral Q hQ (hF.toLp F)
  exact h.congr (fun ε => (heq ε).symm)
end EinsteinRelation.Correctors
