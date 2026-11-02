import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-!
# Annealed spatial approximation errors

Source: `paper/main.tex:693-698`. Stationarity and Fubini identify the
expected local squared error with its environment L² norm. All differences
in the spatial integrals are literal differences of representatives.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open StationarySpatialRealization

/-- The expected spatial squared error is the spatial volume times the
squared environment L² distance. -/
theorem integral_spatial_sq_norm_eq_volume_mul {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (F G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    Integrable (fun ω => ∫ x, ‖F (translate x ω) - G (translate x ω)‖ ^ 2 ∂ν) Q ∧
    (∫ ω, ∫ x, ‖F (translate x ω) - G (translate x ω)‖ ^ 2 ∂ν ∂Q) =
      (ν Set.univ).toReal * ‖F - G‖ ^ 2 := by
  have hm : Measurable (fun ω => ‖F ω - G ω‖ ^ 2) :=
    (((Lp.stronglyMeasurable F).measurable.sub
      (Lp.stronglyMeasurable G).measurable).norm.pow_const 2)
  have hp := (memLp_spatialRealization_prod hQ ν F).sub
    (memLp_spatialRealization_prod hQ ν G)
  have hi : Integrable (fun p : Vec d × FieldPair d =>
      ‖F (translate p.1 p.2) - G (translate p.1 p.2)‖ ^ 2) (ν.prod Q) :=
    (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have he (x : Vec d) :
      (∫ ω, ‖F (translate x ω) - G (translate x ω)‖ ^ 2 ∂Q) = ‖F - G‖ ^ 2 := by
    rw [Probability.integral_translate Q hQ x _ hm]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub F G] with ω hω
    rw [hω, real_inner_self_eq_norm_sq]
    rfl
  refine ⟨hi.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hi]
  simp_rw [he]
  simp only [integral_const, smul_eq_mul]
  rfl

end EinsteinRelation.Correctors
