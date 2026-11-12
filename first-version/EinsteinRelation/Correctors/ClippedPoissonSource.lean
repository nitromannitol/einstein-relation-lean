import EinsteinRelation.Correctors.PoissonLift
import EinsteinRelation.Environment.EuclideanLipschitz

/-! Source: `paper/main.tex:735-739`. Normalize a locally bounded
Poisson source, setting its values outside the bound to zero. -/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- A source divided by a positive bound, clipped outside that bound. -/
def clippedPoissonSource {d : ℕ} (F : Vec d → Vec d) (M : ℝ) (x : Vec d) : Vec d :=
  if euclideanNorm (F x) ≤ M then M⁻¹ • F x else 0

/-- The clipping operation is measurable in a measurable source. -/
theorem measurable_clippedPoissonSource {d : ℕ} (F : Vec d → Vec d)
    (hF : Measurable F) (M : ℝ) : Measurable (clippedPoissonSource F M) := by
  have hc : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact Measurable.ite (measurableSet_le (hc.measurable.comp hF) measurable_const)
    (measurable_const.smul hF) measurable_const

/-- The normalized clipped field is bounded at every point. -/
theorem euclideanNorm_clippedPoissonSource_le {d : ℕ} (F : Vec d → Vec d)
    (M : ℝ) (hM : 0 < M) (x : Vec d) :
    euclideanNorm (clippedPoissonSource F M x) ≤ 1 := by
  unfold clippedPoissonSource
  split_ifs with hx
  · rw [euclideanNorm_smul M⁻¹ (inv_nonneg.mpr hM.le)]
    calc
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  · simp [euclideanNorm, euclideanSq, dot]

/-- The clipping agrees with division by the bound on every region where
the original source satisfies that bound almost everywhere. -/
theorem clippedPoissonSource_eq_ae {d : ℕ} (F : Vec d → Vec d) (M : ℝ)
    (μ : Measure (Vec d)) (hF : ∀ᵐ x ∂μ, euclideanNorm (F x) ≤ M) :
    clippedPoissonSource F M =ᵐ[μ] fun x => M⁻¹ • F x := by
  filter_upwards [hF] with x hx
  exact if_pos hx

end EinsteinRelation.Correctors
