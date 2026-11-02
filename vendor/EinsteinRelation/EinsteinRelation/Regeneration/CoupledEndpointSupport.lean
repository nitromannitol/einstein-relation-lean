import EinsteinRelation.Regeneration.CoupledHistoryLocalityIteration

/-! # Endpoint density and initial support of coupled histories

Source `paper/main.tex:377–381`. These facts transfer the actual path
marginal to the coupled histories used by the locality iteration.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:377–381`: endpoint density lifts through the actual path marginal. -/
theorem coupled_endpoint_density_of_path_marginal {d : ℕ}
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    (hm : (K p).map Prod.fst = P p) (t : ℝ≥0)
    (hd : (P p).map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    (K p).map (fun z : CoupledSample d => z.1 t) ≪ (volume : Measure (Vec d)) := by
  have h_eq : (K p).map (fun z : CoupledSample d => z.1 t) =
      (P p).map (pathPosition t) := by
    calc
      (K p).map (fun z : CoupledSample d => z.1 t) =
          (K p).map (pathPosition t ∘ Prod.fst) := rfl
      _ = ((K p).map Prod.fst).map (pathPosition t) := by
        rw [Measure.map_map (measurable_pathPosition t) measurable_fst]
      _ = (P p).map (pathPosition t) := by rw [hm]
  exact h_eq ▸ hd

/-- Source `paper/main.tex:377–381`: a supported functional has zero expectation when its initial point lies outside the barrier. -/
theorem integral_supported_history_eq_zero_of_start_not_mem {d : ℕ}
    (Δ : ℝ≥0) (n : ℕ) (V : Set (Vec d)) (μ : Measure (CoupledSample d))
    (x : Vec d) (hx : x ∉ V) (hstart : ∀ᵐ z ∂μ, z.1 0 = x)
    (F : CoupledSample d → ℝ)
    (hs : ∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ n V) :
    (∫ z, F z ∂μ) = 0 := by
  have hzero : ∀ᵐ z ∂μ, F z = 0 := by
    filter_upwards [hstart] with z hz
    by_contra hnz
    have hmem := hs z hnz
    have hzero_start : z.1 0 ∈ V := hmem 0 zero_le
    rw [hz] at hzero_start
    exact hx hzero_start
  rw [integral_congr_ae hzero, integral_zero]


end EinsteinRelation.Regeneration
