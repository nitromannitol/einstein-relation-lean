import EinsteinRelation.Correctors.EuclideanCoordinateCharacterization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Energy of an `L^2` Euclidean-valued function as the sum of its coordinate energies.

Source anchors: paper/main.tex:240-248 (the `L^2` horizontal gradient, whose energy is measured in the
Euclidean norm) and paper/main.tex:834-838 (moment estimates in the Euclidean norm). For `f : Ω →
EuclideanSpace ℝ ι` in `L^2(μ)`, the integral of the squared Euclidean norm equals the sum over the
finitely many coordinates of the integrals of the squared coordinates. The measure is arbitrary, the
index type is an arbitrary finite type (including the empty one), and the Euclidean norm is kept.
Each coordinate square is integrable by the coordinate comparison `memLp_euclidean_coordinate`.
-/

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
