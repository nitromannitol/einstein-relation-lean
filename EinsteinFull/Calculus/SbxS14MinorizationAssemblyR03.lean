import EinsteinFull.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.Calculus.SbxS3CleanKernelPatchingR02
import EinsteinFull.Blueprint.G1.Proofs.SbxS4SplitResidual

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

noncomputable section
namespace SbxS14MinorizationAssemblyR03

/-- Scaling the actual displaced endpoint window cancels the dimensional
power in a physical endpoint density lower bound. -/
theorem scaled_endpoint_volume {d : ℕ} (i : Fin d) (l μ c : ℝ)
    (hμ : 0 < μ) (hc : 0 ≤ c) :
    ENNReal.ofReal (c * μ ^ d) * volume (endpointBall i (l / μ) (0 : Vec d)) =
      ENNReal.ofReal c * volume (endpointBall i l 0) := by
  have hscale := EinsteinFull.Blueprint.sbxS4_endpointBall_volume_scale i l μ⁻¹
    (inv_pos.mpr hμ)
  rw [show μ⁻¹ * l = l / μ by ring] at hscale
  rw [hscale, ENNReal.ofReal_mul hc, inv_pow,
    ENNReal.ofReal_inv_of_pos (pow_pos hμ _)]
  calc
    _ = ENNReal.ofReal c * (ENNReal.ofReal (μ ^ d) *
        (ENNReal.ofReal (μ ^ d))⁻¹) * volume (endpointBall i l 0) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hμ _)) ENNReal.ofReal_ne_top, mul_one]

/-- The coefficient can be selected before the force and start: the factor
`2 * δ` is dominated by the lower-density coefficient times window volume. -/
theorem exists_uniform_window_coefficient {d : ℕ} (i : Fin d) (l c : ℝ)
    (hl : 0 < l) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ μ : ℝ, 0 < μ →
      ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal (c * μ ^ d) *
        volume (endpointBall i (l / μ) (0 : Vec d)) := by
  let v : ℝ := (volume (endpointBall i l (0 : Vec d))).toReal
  have hv : 0 < v := ENNReal.toReal_pos (endpointBall_volume_pos i l hl 0).ne'
    (endpointBall_volume_ne_top i l hl 0)
  let δ := min (c * v / 4) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h2 : 2 * δ ≤ c * v := by
    have hh := min_le_left (c * v / 4) (1 / 2)
    dsimp only [δ]
    linarith
  have hv' : ENNReal.ofReal v = volume (endpointBall i l (0 : Vec d)) :=
    ENNReal.ofReal_toReal (endpointBall_volume_ne_top i l hl 0)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro μ hμ
  rw [scaled_endpoint_volume i l μ c hμ hc.le, ← hv', ← ENNReal.ofReal_mul hc.le]
  exact ENNReal.ofReal_le_ofReal h2

/-- At one start, a lower density for the actual full-duration killed endpoint
row gives the source's normalized endpoint estimate, including `2 * δ`. This
is a measure-theoretic consumer; it does not assert the analytic density bound. -/
theorem source_window_bound_of_density {d : ℕ} (i : Fin d) (R δ a : ℝ)
    (hR : 0 < R) (Δ : ℝ≥0) (P : Measure (Path d)) (x : Vec d)
    (p : Vec d → ℝ≥0∞)
    (heq : (P.restrict {γ | ∀ t : ℝ≥0, t ≤ Δ →
        γ t ∈ couplingRegion i R x}).map (fun γ => γ Δ) = volume.withDensity p)
    (hlower : ∀ᵐ y ∂(volume : Measure (Vec d)).restrict (endpointBall i R x),
      ENNReal.ofReal a ≤ p y)
    (hscalar : ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal a *
      volume (endpointBall i R (0 : Vec d)))
    (A : Set (Vec d)) (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * δ) *
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R x) A ≤
      P {γ | (∀ t : ℝ≥0, t ≤ Δ → γ t ∈ couplingRegion i R x) ∧ γ Δ ∈ A} := by
  have hball : MeasurableSet (endpointBall i R x) :=
    (measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)
  have hle := lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset
    (Set.inter_subset_left : endpointBall i R x ∩ A ⊆ endpointBall i R x) hlower)
  rw [lintegral_const, Measure.restrict_apply_univ,
    ← withDensity_apply _ (hball.inter hA), ← heq,
    Measure.map_apply (continuous_eval_const _).measurable (hball.inter hA),
    Measure.restrict_apply ((continuous_eval_const _).measurable (hball.inter hA))] at hle
  rw [ProbabilityTheory.cond_apply' hA, endpointBall_volume_eq i R x]
  calc
    _ ≤ (ENNReal.ofReal a * volume (endpointBall i R 0)) *
        (volume (endpointBall i R 0))⁻¹ * volume (endpointBall i R x ∩ A) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_right hscalar
        ((volume (endpointBall i R 0))⁻¹ * volume (endpointBall i R x ∩ A))
    _ = ENNReal.ofReal a * volume (endpointBall i R x ∩ A) := by
      calc
        _ = ENNReal.ofReal a * (volume (endpointBall i R 0) *
            (volume (endpointBall i R 0))⁻¹) * volume (endpointBall i R x ∩ A) := by ac_rfl
        _ = _ := by rw [ENNReal.mul_inv_cancel (endpointBall_volume_pos i R hR 0).ne'
          (endpointBall_volume_ne_top i R hR 0), mul_one]
    _ ≤ _ := by
      apply le_trans hle
      apply measure_mono
      intro γ hγ
      exact ⟨hγ.2, hγ.1.2⟩

end SbxS14MinorizationAssemblyR03
