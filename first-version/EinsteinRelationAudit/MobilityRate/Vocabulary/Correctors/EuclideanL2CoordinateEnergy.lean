import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import EinsteinRelationAudit.MobilityRate.Vocabulary.Correctors.EuclideanCoordinateCharacterization

/-! Restated from the library module `EinsteinRelation.Correctors.EuclideanL2CoordinateEnergy`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
/-- For `f : Ω → EuclideanSpace ℝ ι` in `L^2(μ)`, the `L^2` energy in the Euclidean norm splits as
the finite sum of the coordinate energies `∫ (f_i)^2 dμ`, for an arbitrary measure `μ`. -/
theorem integral_euclidean_norm_sq_eq_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι) (hf : MemLp f 2 μ) :
    (∫ ω, ‖f ω‖^2 ∂μ) = ∑ i : ι, ∫ ω, (f ω i)^2 ∂μ := by
  have hsq : ∀ ω, ‖f ω‖ ^ 2 = ∑ i : ι, (f ω i) ^ 2 := by
    intro ω
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have hint : ∀ i ∈ (Finset.univ : Finset ι), Integrable (fun ω => (f ω i) ^ 2) μ :=
    fun i _ => (memLp_euclidean_coordinate μ f hf i).1.integrable_sq
  calc (∫ ω, ‖f ω‖ ^ 2 ∂μ) = ∫ ω, ∑ i : ι, (f ω i) ^ 2 ∂μ := by simp only [hsq]
    _ = ∑ i : ι, ∫ ω, (f ω i) ^ 2 ∂μ := MeasureTheory.integral_finset_sum Finset.univ hint
end EinsteinRelation.Correctors
