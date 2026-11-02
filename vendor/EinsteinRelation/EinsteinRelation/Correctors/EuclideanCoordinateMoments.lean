import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Euclidean coordinate projection of `L^2` functions.

Source anchors: paper/main.tex:240-248 (the actual `L^2` gradient) and paper/main.tex:834-838
(the moment estimates), where the Euclidean coordinates of a vector-valued quantity are
controlled by its Euclidean norm. The coordinate map `x ↦ x i` is continuous, so each coordinate
is strongly measurable, and `|f_i| ≤ ‖f‖` pointwise gives the `L^2` comparison. The measure is
arbitrary: no probability or finiteness assumption is used.
-/

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
  exact ⟨hf.of_le hmeas (Filter.Eventually.of_forall hle), eLpNorm_mono hmeas hle⟩

end EinsteinRelation.Correctors
