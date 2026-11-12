import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport
import EinsteinRelation.Correctors.SpatialWeakCongruence

open MeasureTheory

namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Spatial volume-class replacement preserves the heat-selected tensor.
Source: `paper/main.tex:694-708,740-743`. -/
theorem heatSelectedSkewCorrector_congr_spatial_ae
    {d : ℕ} (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    {σ σ' : FieldPair d → Vec d → Mat d}
    (hσ : HasHeatSelectedSkewCorrectorColumn hd Q i σ)
    (heq : ∀ᵐ ω ∂reducedEnvironmentLaw Q, σ ω =ᵐ[volume] σ' ω) :
    HasHeatSelectedSkewCorrectorColumn hd Q i σ' := by
  rcases hσ with ⟨F, hF_meas, hF⟩
  refine ⟨F, hF_meas, ?_⟩
  filter_upwards [hF, heq] with ρ hρF hρeq
  rcases hρF with ⟨hρ_skew, hρ_heat, hρ_sel⟩
  let dCoord : (Vec d → ℝ) → Fin d → Vec d → ℝ := fun f j x =>
    coordinateDerivative j f x
  let laplacian : (Vec d → ℝ) → Vec d → ℝ := fun f x =>
    ∑ ℓ : Fin d, dCoord (dCoord f ℓ) ℓ x
  let g : Vec d → Vec d := fun x =>
    (canonicalCorrectorFlux Q i (translate x ρ) -
      expectedCorrectorFlux Q i).ofLp
  have h_skew' : HasSourceSkewCorrectorColumnAt hd Q i σ' ρ := by
    rcases hρ_skew with ⟨h_skew1, h_skew2, h_skew3⟩
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [h_skew1, hρeq] with x hx1 hx2
      simpa [hx2] using hx1
    · intro ψ hψ_cont hψ_cs j
      rcases h_skew2 ψ hψ_cont hψ_cs j with ⟨h_int_g, h_int_σ, h_eq⟩
      have heq_sum : (fun x : Vec d => ∑ k : Fin d, σ' ρ x j k *
          dCoord ψ k x) =ᵐ[volume]
          (fun x : Vec d => ∑ k : Fin d, σ ρ x j k *
            dCoord ψ k x) := by
        filter_upwards [hρeq] with x hx
        simp [hx, dCoord]
      refine ⟨h_int_g, ((integrable_congr heq_sum).mpr h_int_σ), ?_⟩
      calc
        (∫ x : Vec d, g x j * ψ x ∂volume) =
            -(∫ x : Vec d, ∑ k : Fin d, σ ρ x j k *
              dCoord ψ k x ∂volume) := h_eq
        _ = -(∫ x : Vec d, ∑ k : Fin d, σ' ρ x j k *
              dCoord ψ k x ∂volume) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hρeq] with x hx
          simp [hx, dCoord]
    · intro ψ hψ_cont hψ_cs j k
      rcases h_skew3 ψ hψ_cont hψ_cs j k with ⟨h_int_σ, h_int_g1, h_int_g2, h_eq⟩
      have heq_val : (fun x : Vec d => σ' ρ x j k *
          (-laplacian ψ x)) =ᵐ[volume]
          (fun x : Vec d => σ ρ x j k *
            (-laplacian ψ x)) := by
        filter_upwards [hρeq] with x hx
        simp [hx, laplacian, dCoord]
      refine ⟨((integrable_congr heq_val).mpr h_int_σ), h_int_g1, h_int_g2, ?_⟩
      calc
        (∫ x : Vec d, σ' ρ x j k * (-laplacian ψ x) ∂volume) =
            (∫ x : Vec d, σ ρ x j k * (-laplacian ψ x) ∂volume) := by
          apply integral_congr_ae
          filter_upwards [hρeq] with x hx
          simp [hx, laplacian, dCoord]
        _ = -(∫ x : Vec d, g x k * dCoord ψ j x ∂volume) +
            ∫ x : Vec d, g x j * dCoord ψ k x ∂volume := h_eq
  have h_sel' : HasSelectedHeatGradientRepresentative (σ' ρ) F ρ := by
    intro row col
    have h := hρ_sel row col
    have heq_fn : (fun x : Vec d => σ ρ x row col) =ᵐ[volume]
        (fun x : Vec d => σ' ρ x row col) := by
      filter_upwards [hρeq] with x hx
      simp [hx]
    apply hasWeakGradient_congr_ae isOpen_univ h
    · simpa [Measure.restrict_univ] using heq_fn
    · exact Filter.EventuallyEq.rfl
  exact ⟨h_skew', hρ_heat, h_sel'⟩

end EinsteinRelation.Correctors
