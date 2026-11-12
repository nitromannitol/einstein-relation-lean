import EinsteinRelation.Correctors.EuclideanRmsNorm

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Exact RMS normalization on a positive finite-volume domain.
Source: `paper/main.tex:798–806`. -/
theorem sqrt_energy_eq_volume_mul_vectorRms {X : Type*} [MeasurableSpace X]
    {d : ℕ} (μ : Measure X) (U : Set X) (hU : 0 < μ.real U) (G : X → Vec d) :
    Real.sqrt (∫ x in U, euclideanSq (G x) ∂μ) =
      Real.sqrt (μ.real U) * vectorRms μ U G := by
  simp only [vectorRms, average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  change Real.sqrt _ = Real.sqrt (μ.real U) * Real.sqrt ((μ.real U)⁻¹ * _)
  rw [← Real.sqrt_mul hU.le, ← mul_assoc, mul_inv_cancel₀ hU.ne', one_mul]

end EinsteinRelation.Correctors
