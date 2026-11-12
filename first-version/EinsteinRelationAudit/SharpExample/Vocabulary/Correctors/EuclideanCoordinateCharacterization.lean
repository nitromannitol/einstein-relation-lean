import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EuclideanCoordinateMoments

/-! Restated from the library module `EinsteinRelation.Correctors.EuclideanCoordinateCharacterization`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
/-- A function `Ω → EuclideanSpace ℝ ι` is `L^2(μ)` if and only if each Euclidean coordinate is
`L^2(μ)`, for an arbitrary measure `μ`. -/
theorem memLp_euclidean_iff_coordinates {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : Ω → EuclideanSpace ℝ ι) :
    MemLp f 2 μ ↔ ∀ i : ι, MemLp (fun ω => f ω i) 2 μ := by
  constructor
  · intro hf i
    exact (memLp_euclidean_coordinate μ f hf i).1
  · intro hf
    exact memLp_piLp_iff.mpr hf
end EinsteinRelation.Correctors
