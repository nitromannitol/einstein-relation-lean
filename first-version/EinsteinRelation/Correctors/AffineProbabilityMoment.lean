import EinsteinRelation.External.AKMEnergyDensity
import Mathlib.Analysis.MeanInequalitiesPow

/-! Auxiliary moment and support estimates; source `paper/main.tex:735–753,808–848`. -/

open MeasureTheory
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

theorem lintegral_nonneg_affine_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → ℝ)
    {D B p : ℝ} {K : ℝ≥0∞} (hD : 0 ≤ D) (hB : 0 ≤ B) (hp : 0 < p)
    (hA : ∀ ω, 0 ≤ A ω)
    (hmoment : (∫⁻ ω, ENNReal.ofReal (A ω ^ p) ∂P) ≤ K) :
    (∫⁻ ω, ENNReal.ofReal ((D*A ω+B)^p) ∂P) ≤
      ENNReal.ofReal ((2 : ℝ)^p) *
        (ENNReal.ofReal (D^p) * K + ENNReal.ofReal (B^p)) := by
  have hpt : ∀ ω, ENNReal.ofReal ((D * A ω + B) ^ p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p) *
        (ENNReal.ofReal (D ^ p) * ENNReal.ofReal (A ω ^ p) + ENNReal.ofReal (B ^ p)) := by
    intro ω
    calc ENNReal.ofReal ((D * A ω + B) ^ p)
        = (ENNReal.ofReal D * ENNReal.ofReal (A ω) + ENNReal.ofReal B) ^ p := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (add_nonneg (mul_nonneg hD (hA ω)) hB) hp.le,
            ENNReal.ofReal_add (mul_nonneg hD (hA ω)) hB, ENNReal.ofReal_mul hD]
      _ ≤ (2 : ℝ≥0∞) ^ p *
          ((ENNReal.ofReal D * ENNReal.ofReal (A ω)) ^ p + ENNReal.ofReal B ^ p) :=
          ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
            ← ENNReal.ofReal_rpow_of_nonneg hD hp.le,
            ← ENNReal.ofReal_rpow_of_nonneg (hA ω) hp.le,
            ← ENNReal.ofReal_rpow_of_nonneg hB hp.le,
            ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp.le]
  calc (∫⁻ ω, ENNReal.ofReal ((D * A ω + B) ^ p) ∂P)
      ≤ ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ p) *
          (ENNReal.ofReal (D ^ p) * ENNReal.ofReal (A ω ^ p) + ENNReal.ofReal (B ^ p)) ∂P :=
        lintegral_mono fun ω => hpt ω
    _ = ENNReal.ofReal ((2 : ℝ) ^ p) *
        (ENNReal.ofReal (D ^ p) * (∫⁻ ω, ENNReal.ofReal (A ω ^ p) ∂P) +
          ENNReal.ofReal (B ^ p)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ p) *
        (ENNReal.ofReal (D ^ p) * K + ENNReal.ofReal (B ^ p)) := by
        gcongr <;> exact hmoment

end EinsteinRelation.Correctors
