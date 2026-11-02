import EinsteinRelation.Correctors.EuclideanL2CoordinateEnergy
import Mathlib.MeasureTheory.Function.L2Space

/-! Assembly of an `L^2` Euclidean-valued function from finitely many `L^2` coordinate functions.

Source anchors: paper/main.tex:240-248 (the `L^2` horizontal gradient, whose energy is measured in the
Euclidean norm) and paper/main.tex:834-838 (moment estimates in the Euclidean norm). Given coordinate
functions `f i ∈ L^2(μ)`, the pointwise vector `ω ↦ (f i ω)_i` in `EuclideanSpace ℝ ι` is `L^2(μ)`
(by `memLp_euclidean_iff_coordinates`), its coordinates are the `f i` almost everywhere, and its squared
Euclidean `L^2` norm is the sum of the squared `L^2` norms of the coordinates. The measure is arbitrary,
the index type is an arbitrary finite type (including the empty one), and no probability or
measurability premise is used. The Euclidean norm is kept: no maximum-norm replacement.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- For `h` in `L^2(μ)` with values in a real inner product space, the squared `L^2` norm is the
integral of the squared pointwise norm, for an arbitrary measure. -/
private theorem norm_sq_eq_integral_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω) (h : Lp E 2 μ) :
    ‖h‖ ^ 2 = ∫ ω, ‖h ω‖ ^ 2 ∂μ :=
  calc ‖h‖ ^ 2 = inner ℝ h h := (real_inner_self_eq_norm_sq h).symm
    _ = ∫ ω, inner ℝ (h ω) (h ω) ∂μ := L2.inner_def h h
    _ = ∫ ω, ‖h ω‖ ^ 2 ∂μ := by simp only [real_inner_self_eq_norm_sq]

/-- Assembly of coordinates: for finitely many `f i ∈ L^2(μ)`, there is
`g ∈ L^2(μ; EuclideanSpace ℝ ι)` whose `i`-th coordinate is `f i` almost everywhere and whose
squared Euclidean `L^2` norm is `∑ ‖f i‖^2`. Holds for an arbitrary measure `μ` and an arbitrary
finite index type. -/
theorem exists_Lp_euclidean_of_coordinates {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : ι → Lp ℝ 2 μ) :
    ∃ g : Lp (EuclideanSpace ℝ ι) 2 μ,
      (∀ i : ι, (fun ω => g ω i) =ᵐ[μ] (f i : Ω → ℝ)) ∧
      ‖g‖^2 = ∑ i : ι, ‖f i‖^2 := by
  obtain ⟨G, hGdef⟩ : ∃ G : Ω → EuclideanSpace ℝ ι,
      ∀ (ω : Ω) (i : ι), G ω i = (f i : Ω → ℝ) ω :=
    ⟨fun ω => (WithLp.toLp 2 (fun i => (f i : Ω → ℝ) ω) : EuclideanSpace ℝ ι), fun ω i => rfl⟩
  have hG : MemLp G 2 μ := by
    refine (memLp_euclidean_iff_coordinates μ G).mpr fun i => ?_
    have hcoord : (fun ω => G ω i) = (f i : Ω → ℝ) := funext fun ω => hGdef ω i
    rw [hcoord]
    exact Lp.memLp (f i)
  refine ⟨hG.toLp G, ?_, ?_⟩
  · intro i
    filter_upwards [MemLp.coeFn_toLp hG] with ω hω
    simp only [hω, hGdef]
  · have hA : (∫ ω, ‖hG.toLp G ω‖ ^ 2 ∂μ) = ∫ ω, ‖G ω‖ ^ 2 ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hG] with ω hω
      simp only [hω]
    have hsum : ‖hG.toLp G‖ ^ 2 = ∑ i : ι, ∫ ω, (G ω i) ^ 2 ∂μ :=
      (norm_sq_eq_integral_norm_sq μ (hG.toLp G)).trans
        (hA.trans (integral_euclidean_norm_sq_eq_sum μ G hG))
    refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
    refine Eq.trans ?_ (norm_sq_eq_integral_norm_sq μ (f i)).symm
    simp only [hGdef, Real.norm_eq_abs, sq_abs]

end EinsteinRelation.Correctors
