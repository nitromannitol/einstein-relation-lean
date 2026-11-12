import EinsteinRelation.Correctors.ScalarGaugeReconstruction
import EinsteinRelation.Environment.MatrixNorm
open MeasureTheory
namespace EinsteinRelation.Correctors

open Set

/-- Source: `paper/main.tex:716,743-745`. Centering eliminates an
almost-everywhere additive gauge on any finite nonzero spatial measure. -/
theorem centered_scalar_ae_eq_of_gauge {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {u v : X → ℝ}
    (hv : Integrable v μ) (c : ℝ) (heq : u =ᵐ[μ] (fun x => v x + c)) :
    (fun x => u x - ⨍ y, u y ∂μ) =ᵐ[μ]
      (fun x => v x - ⨍ y, v y ∂μ) := by
  have havg_eq : ⨍ y, u y ∂μ = ⨍ y, v y ∂μ + c := by
    calc
      ⨍ y, u y ∂μ = ⨍ y, (v y + c) ∂μ := average_congr heq
      _ = (⨍ y, v y ∂μ) + c := by
        rw [average_eq, average_eq, integral_add hv (integrable_const _),
          integral_const, measureReal_def]
        have hpos : (μ univ).toReal ≠ 0 := by
          haveI : NeZero (μ univ) := inferInstance
          exact ENNReal.toReal_ne_zero.2 ⟨NeZero.ne _, measure_ne_top _ _⟩
        calc
          (μ univ).toReal⁻¹ • (∫ (a : X), v a ∂μ + (μ univ).toReal • c)
              = (μ univ).toReal⁻¹ • (∫ (a : X), v a ∂μ) +
                (μ univ).toReal⁻¹ • ((μ univ).toReal • c) := by
            rw [smul_add]
          _ = (μ univ).toReal⁻¹ • (∫ (a : X), v a ∂μ) +
              ((μ univ).toReal⁻¹ * (μ univ).toReal) • c := by
            rw [mul_smul]
          _ = (μ univ).toReal⁻¹ • (∫ (a : X), v a ∂μ) + 1 • c := by
            simp [hpos]
          _ = (μ univ).toReal⁻¹ • (∫ (a : X), v a ∂μ) + c := by
            rw [one_smul]
  filter_upwards [heq] with x hx
  simp [hx, havg_eq]

/-- Source: `paper/main.tex:716,743-745`. Entrywise constants cancel
from the centered matrix itself, preserving the genuine Frobenius norm. -/
theorem centered_matrix_ae_eq_of_entrywise_gauge
    {X : Type*} [MeasurableSpace X] {d : ℕ}
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] {u v : X → Mat d}
    (hv : ∀ j k, Integrable (fun x => v x j k) μ)
    (heq : ∀ j k, ∃ c : ℝ,
      (fun x => u x j k) =ᵐ[μ] (fun x => v x j k + c)) :
    (fun x => u x - Matrix.of (fun j k => ⨍ y, u y j k ∂μ)) =ᵐ[μ]
      (fun x => v x - Matrix.of (fun j k => ⨍ y, v y j k ∂μ)) := by
  -- For each entry j,k, apply the scalar theorem to get a.e. equality of centered entries
  have h_entries (j k : Fin d) : (fun x => u x j k - ⨍ y, u y j k ∂μ) =ᵐ[μ]
      (fun x => v x j k - ⨍ y, v y j k ∂μ) := by
    rcases heq j k with ⟨c, hc⟩
    have hv_entry : Integrable (fun x => v x j k) μ := hv j k
    exact centered_scalar_ae_eq_of_gauge μ hv_entry c hc
  -- Now lift to matrix equality using funext
  filter_upwards [ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => h_entries j k] with x hx
  ext j k
  simp [hx j k]
end EinsteinRelation.Correctors
