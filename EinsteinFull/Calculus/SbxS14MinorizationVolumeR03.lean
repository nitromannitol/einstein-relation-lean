import EinsteinFull.Calculus.SbxS14MinorizationAssemblyR03

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace SbxS14MinorizationVolumeR03

/-- The displaced endpoint window is a translation of the inverse-force
homothety of the fixed window. -/
theorem endpoint_window_translate_scale {d : ℕ} (i : Fin d) (l μ : ℝ)
    (hμ : 0 < μ) (x : Vec d) :
    endpointBall i (l / μ) x =
      (fun z : Vec d => x + z) '' (μ⁻¹ • endpointBall i l 0) := by
  have hs := EinsteinFull.Blueprint.sbxS4_endpointBall_smul i l μ⁻¹ (inv_pos.mpr hμ)
  rw [show μ⁻¹ * l = l / μ by ring] at hs
  rw [← hs]
  ext y
  constructor
  · intro hy
    refine ⟨y - x, ?_, by simp⟩
    change euclideanNorm (y - (x + (9 * (l / μ)) • unitVector i)) < l / μ at hy
    change euclideanNorm (y - x - (0 + (9 * (l / μ)) • unitVector i)) < l / μ
    simpa only [zero_add, sub_add_eq_sub_sub] using hy
  · rintro ⟨z, hz, rfl⟩
    change euclideanNorm (x + z - (x + (9 * (l / μ)) • unitVector i)) < l / μ
    change euclideanNorm (z - (0 + (9 * (l / μ)) • unitVector i)) < l / μ at hz
    simpa only [zero_add, add_sub_add_left_eq_sub] using hz

/-- Exact positive finite physical window volume, uniform over the start. -/
theorem endpoint_window_volume {d : ℕ} (i : Fin d) (l μ : ℝ)
    (hl : 0 < l) (hμ : 0 < μ) (x : Vec d) :
    volume (endpointBall i (l / μ) x) =
        ENNReal.ofReal ((μ⁻¹) ^ d) * volume (endpointBall i l 0) ∧
    0 < volume (endpointBall i (l / μ) x) ∧
    volume (endpointBall i (l / μ) x) ≠ ∞ := by
  refine ⟨?_, endpointBall_volume_pos i _ (div_pos hl hμ) x,
    endpointBall_volume_ne_top i _ (div_pos hl hμ) x⟩
  rw [endpointBall_volume_eq i (l / μ) x]
  have h := EinsteinFull.Blueprint.sbxS4_endpointBall_volume_scale i l μ⁻¹ (inv_pos.mpr hμ)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The explicit coin coefficient depends only on the fixed window and the
rescaled density lower constant. -/
def windowCoinCoefficient {d : ℕ} (i : Fin d) (l c : ℝ) : ℝ :=
  min (c * (volume (endpointBall i l (0 : Vec d))).toReal / 4) (1 / 2)

/-- A literal lower bound on each actual killed endpoint density gives the
source bridge minorization, with a coefficient selected before the force,
path laws, time and densities. The analytic density bound is an input. -/
theorem source_minorization_of_rescaled_density {d : ℕ} (i : Fin d) (l c : ℝ)
    (hl : 0 < l) (hc : 0 < c) :
    0 < windowCoinCoefficient i l c ∧ windowCoinCoefficient i l c < 1 ∧
    ∀ (μ : ℝ), 0 < μ → ∀ (Δ : ℝ≥0) (P : Vec d → Measure (Path d))
      (p : Vec d → Vec d → ℝ≥0∞),
      (∀ x, ((P x).restrict {γ | ∀ t : ℝ≥0, t ≤ Δ →
        γ t ∈ couplingRegion i (l / μ) x}).map (fun γ => γ Δ) =
        volume.withDensity (p x)) →
      (∀ x, ∀ᵐ y ∂(volume : Measure (Vec d)).restrict (endpointBall i (l / μ) x),
        ENNReal.ofReal (c * μ ^ d) ≤ p x y) →
      HasSourceMinorization P Δ (windowCoinCoefficient i l c) (l / μ) i := by
  let v : ℝ := (volume (endpointBall i l (0 : Vec d))).toReal
  have hv : 0 < v := ENNReal.toReal_pos (endpointBall_volume_pos i l hl 0).ne'
    (endpointBall_volume_ne_top i l hl 0)
  have hd0 : 0 < windowCoinCoefficient i l c := by
    change 0 < min (c * v / 4) (1 / 2)
    exact lt_min (by positivity) (by norm_num)
  have hd1 : windowCoinCoefficient i l c < 1 := by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨hd0, hd1, ?_⟩
  intro μ hμ Δ P p heq hlower x A hA
  have h2 : 2 * windowCoinCoefficient i l c ≤ c * v := by
    have h := min_le_left (c * v / 4) (1 / 2)
    have hcv : 0 < c * v := mul_pos hc hv
    change 2 * min (c * v / 4) (1 / 2) ≤ c * v
    linarith
  have hv' : ENNReal.ofReal v = volume (endpointBall i l (0 : Vec d)) :=
    ENNReal.ofReal_toReal (endpointBall_volume_ne_top i l hl 0)
  have hscalar : ENNReal.ofReal (2 * windowCoinCoefficient i l c) ≤
      ENNReal.ofReal (c * μ ^ d) * volume (endpointBall i (l / μ) 0) := by
    rw [SbxS14MinorizationAssemblyR03.scaled_endpoint_volume i l μ c hμ hc.le,
      ← hv', ← ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal h2
  exact SbxS14MinorizationAssemblyR03.source_window_bound_of_density i (l / μ)
    (windowCoinCoefficient i l c) (c * μ ^ d) (div_pos hl hμ) Δ (P x) x (p x)
    (heq x) (hlower x) hscalar A hA

end SbxS14MinorizationVolumeR03
