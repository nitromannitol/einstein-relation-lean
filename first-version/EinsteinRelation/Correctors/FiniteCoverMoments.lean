import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Local moment bounds from a finite spatial cover

Source: `paper/main.tex:724-731`. This is the finite-cover step for the
stationary cell estimates. It concerns a moment of the spatial integral,
without changing that quantity to a spatial higher norm.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A finite spatial cover bounds each moment of order at least one by
the sum of the corresponding moments on its members. -/
theorem lintegral_setLIntegral_rpow_le_finite_cover
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure X) [SFinite μ]
    (s : Finset ι) (U : ι → Set X) (A : Set X)
    (hcover : A ⊆ ⋃ i ∈ s, U i)
    (F : Ω → X → ℝ≥0∞) (hF : Measurable (Function.uncurry F))
    (q : ℝ) (hq : 1 ≤ q) :
    (∫⁻ ω, (∫⁻ x in A, F ω x ∂μ) ^ q ∂P) ≤
      (s.card : ℝ≥0∞) ^ (q - 1) *
        ∑ i ∈ s, ∫⁻ ω, (∫⁻ x in U i, F ω x ∂μ) ^ q ∂P := by
  classical
  have hlocal (ω : Ω) : (∫⁻ x in A, F ω x ∂μ) ≤
      ∑ i ∈ s, ∫⁻ x in U i, F ω x ∂μ := by
    calc
      _ ≤ ∫⁻ x in ⋃ i : s, U i, F ω x ∂μ :=
        lintegral_mono_set (by simpa only [Set.iUnion_subtype] using hcover)
      _ ≤ ∑' i : s, ∫⁻ x in U i, F ω x ∂μ :=
        lintegral_iUnion_le (fun i : s => U i) (F ω)
      _ = _ := by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort s (fun i : ι => ∫⁻ x in U i, F ω x ∂μ)
  calc
    _ ≤ ∫⁻ ω, (s.card : ℝ≥0∞) ^ (q - 1) *
        ∑ i ∈ s, (∫⁻ x in U i, F ω x ∂μ) ^ q ∂P := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (hlocal ω) (by linarith)).trans
        (ENNReal.rpow_sum_le_const_mul_sum_rpow s _ hq)
    _ = _ := by
      rw [lintegral_const_mul', lintegral_finset_sum]
      · intro i _
        exact (hF.lintegral_prod_right (ν := μ.restrict (U i))).pow_const q
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.natCast_ne_top s.card)

end EinsteinRelation.Correctors

