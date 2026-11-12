import EinsteinRelation.Correctors.CenteredScalarIntegrableMoments
open MeasureTheory
open Set
open ENNReal
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:743-745`. Pair differences remove arbitrary
samplewise additive gauges before the spatial centering step. -/
theorem lintegral_centered_rpow_le_pair_difference
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (u : X → ℝ) (p : ℝ) (hp : 1 ≤ p) (hu : Integrable u μ) :
    (∫⁻ x, ENNReal.ofReal (|u x - ∫ y, u y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) *
        (∫⁻ y, ∫⁻ x, ENNReal.ofReal (|u x - u y| ^ p) ∂μ ∂μ) := by
  have hb (y : X) : (∫⁻ x, ENNReal.ofReal (|u x - ∫ z, u z ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) * (∫⁻ x, ENNReal.ofReal (|u x - u y| ^ p) ∂μ) :=
    lintegral_abs_sub_mean_rpow_le μ u (u y) p hp hu
  calc
    _ = ∫⁻ _ : X, (∫⁻ x, ENNReal.ofReal (|u x - ∫ z, u z ∂μ| ^ p) ∂μ) ∂μ := by simp
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 ^ p) *
        (∫⁻ x, ENNReal.ofReal (|u x - u y| ^ p) ∂μ) ∂μ := lintegral_mono hb
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
end EinsteinRelation.Correctors
