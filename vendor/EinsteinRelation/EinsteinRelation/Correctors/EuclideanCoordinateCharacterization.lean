import EinsteinRelation.Correctors.EuclideanCoordinateMoments
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Characterization of `L^2` membership of Euclidean-valued functions through their coordinates.

Source anchors: paper/main.tex:240-248 (the `L^2` horizontal gradient, a vector-valued quantity
with its Euclidean norm) and paper/main.tex:834-838 (moment estimates in the Euclidean norm).
A function into `EuclideanSpace ℝ ι` is `L^2(μ)` exactly when each of its Euclidean coordinates is.
The forward direction is the compiled coordinate comparison `memLp_euclidean_coordinate`. The
reverse direction is Mathlib's `memLp_piLp_iff` for `PiLp 2`, which covers every finite index type
including the empty one. The measure is arbitrary: no probability, finiteness, or extra
measurability premise is used, and the Euclidean norm is kept (no maximum-norm replacement).
-/

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
