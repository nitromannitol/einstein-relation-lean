import EinsteinRelation.Correctors.AKMParabolicIntegrability

/-! Coordinatewise integral pairings for `paper/main.tex:787–792,850`. -/
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- The finite Euclidean pairing commutes with coordinate integration. -/
theorem dot_integral_components {T : Type*} [MeasurableSpace T]
    (μ : Measure T) {d : ℕ} (F : T → Vec d) (v : Vec d)
    (hF : ∀ j, Integrable (fun t => F t j) μ) :
    dot (fun j => ∫ t, F t j ∂μ) v = ∫ t, dot (F t) v ∂μ := by
  calc
    dot (fun j => ∫ t, F t j ∂μ) v
        = ∑ j, (∫ t, F t j ∂μ) * v j := rfl
    _ = ∑ j, ∫ t, F t j * v j ∂μ := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [← integral_mul_const (v j) (fun t => F t j)]
    _ = ∫ t, ∑ j, F t j * v j ∂μ := by
      rw [← integral_finset_sum Finset.univ (fun j hj => (hF j).mul_const (v j))]
    _ = ∫ t, dot (F t) v ∂μ := rfl

/-- A matrix coordinate commutes with time integration. -/
theorem matrix_coordinate_integral_components{T : Type*} [MeasurableSpace T]
    (μ : Measure T) {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (F : T → Vec d) (hF : ∀ j, Integrable (fun t => F t j) μ) (i : Fin d) :
    (A.mulVec (fun j => ∫ t, F t j ∂μ)) i =
      ∫ t, (A.mulVec (F t)) i ∂μ := by
  have hcomm (u v : Vec d) : dot u v = dot v u := by
    simp only [dot, mul_comm]
  calc
    (A.mulVec (fun j => ∫ t, F t j ∂μ)) i =
        dot (fun j => ∫ t, F t j ∂μ) (A i) := hcomm _ _
    _ = ∫ t, dot (F t) (A i) ∂μ := dot_integral_components μ F (A i) hF
    _ = ∫ t, (A.mulVec (F t)) i ∂μ := integral_congr_ae (Filter.Eventually.of_forall
      fun t => hcomm _ _)

/-- Matrix-weighted pairings commute with time integration (`paper/main.tex:808–816`). -/
theorem matrix_pairing_integral_components{T : Type*} [MeasurableSpace T]
    (μ : Measure T) {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (F : T → Vec d) (v : Vec d)
    (hF : ∀ j, Integrable (fun t => F t j) μ) :
    dot (A.mulVec (fun j => ∫ t, F t j ∂μ)) v =
      ∫ t, dot (A.mulVec (F t)) v ∂μ := by
  have hAF : ∀ i, Integrable (fun t => (A.mulVec (F t)) i) μ := by
    intro i
    change Integrable (fun t => ∑ j, A i j * F t j) μ
    exact integrable_finset_sum _ fun j _ => (hF j).const_mul (A i j)
  calc
    dot (A.mulVec (fun j => ∫ t, F t j ∂μ)) v =
        dot (fun i => ∫ t, (A.mulVec (F t)) i ∂μ) v := by
      congr 1
      funext i
      exact matrix_coordinate_integral_components μ A F hF i
    _ = ∫ t, dot (A.mulVec (F t)) v ∂μ :=
      dot_integral_components μ (fun t => A.mulVec (F t)) v hAF

end EinsteinRelation.Correctors
