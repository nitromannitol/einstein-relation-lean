import EinsteinRelation.Correctors.ScalarGaugeReconstruction
import EinsteinRelation.Correctors.CenteredGaugeInvariance
import EinsteinRelation.Environment.MatrixNorm
open MeasureTheory
namespace EinsteinRelation.Correctors

open Set

/-- Source: `paper/main.tex:716,743-745`. A physical additive gauge
comparison transports centered scalar moments, without requiring joint
measurability of the raw scalar carrier. -/
theorem lintegral_centered_scalar_le_of_physical_gauge
    {Ω Ξ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace X]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q)
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (u : Ξ → X → ℝ) (v : Ω → X → ℝ) (p : ℝ)
    (hv : ∀ᵐ ω ∂P, Integrable (v ω) μ)
    (hg : ∀ᵐ ω ∂P, ∃ c : ℝ, u (T ω) =ᵐ[μ] (fun x => v ω x + c)) :
    (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (|u ρ x - ⨍ y, u ρ y ∂μ| ^ p) ∂μ ∂Q) ≤
      ∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (|v ω x - ⨍ y, v ω y ∂μ| ^ p) ∂μ ∂P := by
  have h_ae_centered : ∀ᵐ ω ∂P,
      ⨍⁻ x, ENNReal.ofReal (|u (T ω) x - ⨍ y, u (T ω) y ∂μ| ^ p) ∂μ =
      ⨍⁻ x, ENNReal.ofReal (|v ω x - ⨍ y, v ω y ∂μ| ^ p) ∂μ := by
    filter_upwards [hv, hg] with ω hvω hgω
    rcases hgω with ⟨c, hc⟩
    have h_centered : (fun x => u (T ω) x - ⨍ y, u (T ω) y ∂μ) =ᵐ[μ]
        (fun x => v ω x - ⨍ y, v ω y ∂μ) :=
      centered_scalar_ae_eq_of_gauge μ hvω c hc
    have h_enn : (fun x => ENNReal.ofReal (|u (T ω) x - ⨍ y, u (T ω) y ∂μ| ^ p)) =ᵐ[μ]
        (fun x => ENNReal.ofReal (|v ω x - ⨍ y, v ω y ∂μ| ^ p)) := by
      filter_upwards [h_centered] with x hx
      simp [hx]
    exact laverage_congr h_enn
  calc
    (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (|u ρ x - ⨍ y, u ρ y ∂μ| ^ p) ∂μ ∂Q)
        = (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (|u ρ x - ⨍ y, u ρ y ∂μ| ^ p) ∂μ ∂(Measure.map T P)) := by
      rw [hT.map_eq]
    _ ≤ (∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (|u (T ω) x - ⨍ y, u (T ω) y ∂μ| ^ p) ∂μ ∂P) :=
      lintegral_map_le _ _
    _ = (∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (|v ω x - ⨍ y, v ω y ∂μ| ^ p) ∂μ ∂P) := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_ae_centered] with ω hω
      exact hω

/-- Source: `paper/main.tex:716,743-745`. Entrywise physical gauges
cancel in the centered tensor itself and hence in its Frobenius moment. -/
theorem lintegral_centered_flux_le_of_physical_gauge
    {Ω Ξ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace X]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ} {d : ℕ}
    (hT : MeasurePreserving T P Q)
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (u : Ξ → X → Mat d) (v : Ω → X → Mat d) (p : ℝ)
    (hv : ∀ᵐ ω ∂P, ∀ j k, Integrable (fun x => v ω x j k) μ)
    (hg : ∀ᵐ ω ∂P, ∀ j k, ∃ c : ℝ,
      (fun x => u (T ω) x j k) =ᵐ[μ] (fun x => v ω x j k + c)) :
    (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (u ρ x -
      Matrix.of (fun j k => ⨍ y, u ρ y j k ∂μ)) ^ p) ∂μ ∂Q) ≤
      ∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (v ω x -
        Matrix.of (fun j k => ⨍ y, v ω y j k ∂μ)) ^ p) ∂μ ∂P := by
  have h_ae_centered : ∀ᵐ ω ∂P,
      ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (u (T ω) x -
        Matrix.of (fun j k => ⨍ y, u (T ω) y j k ∂μ)) ^ p) ∂μ =
      ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (v ω x -
        Matrix.of (fun j k => ⨍ y, v ω y j k ∂μ)) ^ p) ∂μ := by
    filter_upwards [hv, hg] with ω hvω hgω
    have h_centered : (fun x => u (T ω) x - Matrix.of (fun j k => ⨍ y, u (T ω) y j k ∂μ)) =ᵐ[μ]
        (fun x => v ω x - Matrix.of (fun j k => ⨍ y, v ω y j k ∂μ)) :=
      centered_matrix_ae_eq_of_entrywise_gauge μ hvω hgω
    have h_enn : (fun x => ENNReal.ofReal (frobeniusNorm (u (T ω) x -
        Matrix.of (fun j k => ⨍ y, u (T ω) y j k ∂μ)) ^ p)) =ᵐ[μ]
        (fun x => ENNReal.ofReal (frobeniusNorm (v ω x -
          Matrix.of (fun j k => ⨍ y, v ω y j k ∂μ)) ^ p)) := by
      filter_upwards [h_centered] with x hx
      simp [hx]
    exact laverage_congr h_enn
  calc
    (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (u ρ x -
        Matrix.of (fun j k => ⨍ y, u ρ y j k ∂μ)) ^ p) ∂μ ∂Q)
        = (∫⁻ ρ, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (u ρ x -
            Matrix.of (fun j k => ⨍ y, u ρ y j k ∂μ)) ^ p) ∂μ ∂(Measure.map T P)) := by
      rw [hT.map_eq]
    _ ≤ (∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (u (T ω) x -
        Matrix.of (fun j k => ⨍ y, u (T ω) y j k ∂μ)) ^ p) ∂μ ∂P) :=
      lintegral_map_le _ _
    _ = (∫⁻ ω, ⨍⁻ x, ENNReal.ofReal (frobeniusNorm (v ω x -
        Matrix.of (fun j k => ⨍ y, v ω y j k ∂μ)) ^ p) ∂μ ∂P) := by
      refine lintegral_congr_ae ?_
      filter_upwards [h_ae_centered] with ω hω
      exact hω

end EinsteinRelation.Correctors
