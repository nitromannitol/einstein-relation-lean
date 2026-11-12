import EinsteinRelation.Correctors.CenteredFrobeniusMoments
open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:743-745`. Centering a finite spatial average
costs a constant depending only on the exponent. -/
theorem laverage_abs_sub_average_rpow_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (u : X → ℝ) (c p : ℝ) (hp : 1 ≤ p) (hu : Integrable u μ) :
    (⨍⁻ x, ENNReal.ofReal (|u x - ⨍ y, u y ∂μ| ^ p) ∂μ) ≤
      ENNReal.ofReal (2 ^ p) * (⨍⁻ x, ENNReal.ofReal (|u x - c| ^ p) ∂μ) :=
  lintegral_abs_sub_mean_rpow_le ((μ Set.univ)⁻¹ • μ) u c p hp hu.to_average
/-- Source: `paper/main.tex:743-745`. The tensor version retains the
entrywise spatial mean and the Frobenius norm. -/
theorem laverage_frobenius_sub_average_rpow_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    {d : ℕ} (hd : 0 < d) (A : X → Mat d) (c : Mat d) (p : ℝ) (hp : 2 ≤ p)
    (hA : Measurable A) (hi : ∀ j k, Integrable (fun x => A x j k) μ) :
    (⨍⁻ x, ENNReal.ofReal (frobeniusNorm
      (A x - Matrix.of (fun j k => ⨍ y, A y j k ∂μ)) ^ p) ∂μ) ≤
      ENNReal.ofReal ((d : ℝ) ^ p * 2 ^ p) *
        (⨍⁻ x, ENNReal.ofReal (frobeniusNorm (A x - c) ^ p) ∂μ) :=
  lintegral_frobenius_sub_entrywise_mean_rpow_le ((μ Set.univ)⁻¹ • μ) hd A c p hp hA
    (fun j k => (hi j k).to_average)
end EinsteinRelation.Correctors
