import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-!
# Scalar orbit integrals under a stationary law

Source: `paper/main.tex:693-698`. Fubini and stationarity identify the
expected spatial integral with volume times the environment expectation.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Fubini and stationarity for a measurable integrable scalar field. -/
theorem stationary_spatial_integral {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (f : FieldPair d → ℝ) (hf : Measurable f) (hi : Integrable f Q) :
    Integrable (fun p : Vec d × FieldPair d => f (translate p.1 p.2)) (ν.prod Q) ∧
    Integrable (fun ω => ∫ x, f (translate x ω) ∂ν) Q ∧
      (∫ ω, ∫ x, f (translate x ω) ∂ν ∂Q) =
        (ν Set.univ).toReal * ∫ ω, f ω ∂Q := by
  have hm : Measurable (fun p : Vec d × FieldPair d => f (translate p.1 p.2)) :=
    hf.comp Probability.continuous_translate.measurable
  have hx (x : Vec d) : Integrable (fun ω => f (translate x ω)) Q :=
    (measurePreserving_translate Q hQ x).integrable_comp_of_integrable hi
  have hn (x : Vec d) : (∫ ω, ‖f (translate x ω)‖ ∂Q) = ∫ ω, ‖f ω‖ ∂Q :=
    Probability.integral_translate Q hQ x _ hf.norm
  have hp : Integrable (fun p : Vec d × FieldPair d => f (translate p.1 p.2)) (ν.prod Q) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨ae_of_all _ hx, ?_⟩
    simpa only [hn] using (integrable_const (∫ ω, ‖f ω‖ ∂Q) : Integrable _ ν)
  refine ⟨hp, hp.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hp]
  simp_rw [Probability.integral_translate Q hQ _ _ hf]
  simp only [integral_const, smul_eq_mul]
  rfl

end EinsteinRelation.Correctors
