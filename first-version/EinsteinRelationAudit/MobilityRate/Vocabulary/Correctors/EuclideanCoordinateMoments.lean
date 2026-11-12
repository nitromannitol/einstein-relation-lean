import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Restated from the library module `EinsteinRelation.Correctors.EuclideanCoordinateMoments`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Each Euclidean coordinate of an `L^2` function is `L^2`, and its `L^2` seminorm is bounded by
the Euclidean `L^2` seminorm of the vector-valued function. Holds for an arbitrary measure,
including infinite mass. -/
theorem memLp_euclidean_coordinate {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι) (hf : MemLp f 2 μ) (i : ι) :
    MemLp (fun ω => f ω i) 2 μ ∧
      eLpNorm (fun ω => f ω i) 2 μ ≤ eLpNorm f 2 μ := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ ι => x i) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun ω => f ω i) μ :=
    hcont.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hle : ∀ ω, ‖f ω i‖ ≤ ‖f ω‖ := fun ω => PiLp.norm_apply_le (f ω) i
  exact ⟨hf.of_le hmeas (Filter.Eventually.of_forall hle), eLpNorm_mono hle⟩
end EinsteinRelation.Correctors
