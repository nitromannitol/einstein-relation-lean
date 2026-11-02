import EinsteinFull.Calculus.SbxS14MinorizationVolumeR03
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

noncomputable section
namespace SbxASourceSetwiseDensityR05

/-- A density bound on a measurable window is equivalent to domination of
its restricted reference measure by the full density measure. -/
theorem ae_density_lower_iff_restrict_smul_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SigmaFinite ν] (B : Set α) (hB : MeasurableSet B)
    (a : ℝ≥0∞) (p : α → ℝ≥0∞) :
    (∀ᵐ y ∂ν.restrict B, a ≤ p y) ↔ a • ν.restrict B ≤ ν.withDensity p := by
  constructor
  · intro h
    calc
      a • ν.restrict B = (ν.restrict B).withDensity (fun _ => a) :=
        (withDensity_const _).symm
      _ ≤ (ν.restrict B).withDensity p := withDensity_mono h
      _ = (ν.withDensity p).restrict B := (restrict_withDensity hB p).symm
      _ ≤ ν.withDensity p := Measure.restrict_le_self
  · intro h
    have h' := Measure.restrict_mono_measure h B
    rw [Measure.restrict_smul, Measure.restrict_restrict hB, Set.inter_self,
      restrict_withDensity hB] at h'
    rw [← withDensity_const] at h'
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_const
    intro s hs _
    simpa only [withDensity_apply _ hs] using h' s

/-- On the actual full-duration staying-event endpoint measure, setwise
 domination is equivalent to the lower bound for any density representing it. -/
theorem source_endpoint_density_lower_iff_setwise {d : ℕ} (i : Fin d)
    (R a : ℝ) (Δ : ℝ≥0) (P : Measure (Path d)) (x : Vec d)
    (p : Vec d → ℝ≥0∞)
    (heq : (P.restrict {γ | ∀ t : ℝ≥0, t ≤ Δ →
      γ t ∈ couplingRegion i R x}).map (fun γ => γ Δ) = volume.withDensity p) :
    (∀ᵐ y ∂(volume : Measure (Vec d)).restrict (endpointBall i R x),
      ENNReal.ofReal a ≤ p y) ↔
    ENNReal.ofReal a • (volume : Measure (Vec d)).restrict (endpointBall i R x) ≤
      (P.restrict {γ | ∀ t : ℝ≥0, t ≤ Δ →
        γ t ∈ couplingRegion i R x}).map (fun γ => γ Δ) := by
  rw [heq]
  exact ae_density_lower_iff_restrict_smul_le volume _
    ((measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)) _ _

/-- Setwise domination of every actual full-duration staying-event endpoint
measure gives the source minorization with a fixed window coefficient. -/
theorem source_minorization_of_rescaled_setwise {d : ℕ} (i : Fin d) (l c : ℝ)
    (hl : 0 < l) (hc : 0 < c) :
    0 < SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c ∧
    SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c < 1 ∧
    ∀ (μ : ℝ), 0 < μ → ∀ (Δ : ℝ≥0) (P : Vec d → Measure (Path d)),
      (∀ x, ENNReal.ofReal (c * μ ^ d) •
          (volume : Measure (Vec d)).restrict (endpointBall i (l / μ) x) ≤
        ((P x).restrict {γ | ∀ t : ℝ≥0, t ≤ Δ →
          γ t ∈ couplingRegion i (l / μ) x}).map (fun γ => γ Δ)) →
      HasSourceMinorization P Δ (SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c)
        (l / μ) i := by
  let v : ℝ := (volume (endpointBall i l (0 : Vec d))).toReal
  have hv : 0 < v := ENNReal.toReal_pos (endpointBall_volume_pos i l hl 0).ne'
    (endpointBall_volume_ne_top i l hl 0)
  have hd0 : 0 < SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c := by
    change 0 < min (c * v / 4) (1 / 2)
    exact lt_min (by positivity) (by norm_num)
  have hd1 : SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨hd0, hd1, ?_⟩
  intro μ hμ Δ P hdom x A hA
  have h2 : 2 * SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c ≤ c * v := by
    have h := min_le_left (c * v / 4) (1 / 2)
    have hcv : 0 < c * v := mul_pos hc hv
    change 2 * min (c * v / 4) (1 / 2) ≤ c * v
    linarith
  have hv' : ENNReal.ofReal v = volume (endpointBall i l (0 : Vec d)) :=
    ENNReal.ofReal_toReal (endpointBall_volume_ne_top i l hl 0)
  have hscalar : ENNReal.ofReal (2 * SbxS14MinorizationVolumeR03.windowCoinCoefficient i l c) ≤
      ENNReal.ofReal (c * μ ^ d) * volume (endpointBall i (l / μ) 0) := by
    rw [SbxS14MinorizationAssemblyR03.scaled_endpoint_volume i l μ c hμ hc.le,
      ← hv', ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal h2
  have hle := hdom x A
  rw [Measure.smul_apply, Measure.restrict_apply hA, Set.inter_comm A,
    Measure.map_apply (continuous_eval_const _).measurable hA,
    Measure.restrict_apply ((continuous_eval_const _).measurable hA)] at hle
  rw [ProbabilityTheory.cond_apply' hA, endpointBall_volume_eq i (l / μ) x]
  calc
    _ ≤ (ENNReal.ofReal (c * μ ^ d) * volume (endpointBall i (l / μ) 0)) *
        (volume (endpointBall i (l / μ) 0))⁻¹ *
          volume (endpointBall i (l / μ) x ∩ A) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_right hscalar
        ((volume (endpointBall i (l / μ) 0))⁻¹ * volume (endpointBall i (l / μ) x ∩ A))
    _ = ENNReal.ofReal (c * μ ^ d) * volume (endpointBall i (l / μ) x ∩ A) := by
      calc
        _ = ENNReal.ofReal (c * μ ^ d) * (volume (endpointBall i (l / μ) 0) *
            (volume (endpointBall i (l / μ) 0))⁻¹) *
              volume (endpointBall i (l / μ) x ∩ A) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel (endpointBall_volume_pos i _ (div_pos hl hμ) 0).ne'
          (endpointBall_volume_ne_top i _ (div_pos hl hμ) 0), mul_one]
    _ ≤ _ := by
      apply le_trans hle
      apply measure_mono
      intro γ hγ
      exact ⟨hγ.2, hγ.1⟩

end SbxASourceSetwiseDensityR05
