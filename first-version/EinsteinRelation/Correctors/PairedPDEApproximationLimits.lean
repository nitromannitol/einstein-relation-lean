import EinsteinRelation.Correctors.PairedPDEConvolutionClass
import EinsteinRelation.Correctors.PairedPDECutoffSpatialIbP
import EinsteinRelation.Correctors.PairedPDEConvolvedSpatialDerivative
import EinsteinRelation.Correctors.PairedPDERegularizedTimePairing

/-! # Actual approximation limits in the weak energy test

Source: `paper/main.tex:832–840`. The compact cutoff of the actual solution
and its product-rule gradient converge strongly under shrinking smooth
kernels. Temporal cancellation gives the scalar temporal pairing limit.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual compact cutoff solution is approximated in space-time L².
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_regularization_limit {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k)) :
    Tendsto (fun k => eLpNorm (fun z : ℝ × Vec d =>
      (∫ w : ℝ × Vec d, ζ w * u w * ρ k (z - w)) - ζ z * u z)
        2 volume) atTop (𝓝 0) :=
  paired_tendsto_compact_convolution_L2
    (parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol hζ.continuous hζc hζsupp)
    hζc.mul_right hρ hρc hρ0 hρ1 hε hsupp

/-- The actual spatial derivatives of the regularized cutoff converge to
its actual weak product-rule gradient. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_gradient_regularization_limit {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k)) (j : Fin d) :
    Tendsto (fun k => eLpNorm (fun z : ℝ × Vec d =>
      fderiv ℝ (fun y : ℝ × Vec d => ∫ w : ℝ × Vec d, ζ w * u w * ρ k (y - w))
        z (0, unitVector j) - (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)))
        2 volume) atTop (𝓝 0) := by
  let f := fun z => ζ z * u z
  let H := fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)
  have hf := parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol
    hζ.continuous hζc hζsupp
  have hH := parabolicSolution_cutoff_gradient_memLp_global hI hU hsol hζ hζc hζsupp j
  have hHc : HasCompactSupport H :=
    hζc.mul_right.add (hζc.fderiv_apply ℝ (0, unitVector j)).mul_left
  have hd (k : ℕ) (z : ℝ × Vec d) :
      fderiv ℝ (fun y : ℝ × Vec d => ∫ w : ℝ × Vec d, f w * ρ k (y - w))
        z (0, unitVector j) = ∫ w : ℝ × Vec d, H w * ρ k (z - w) := by
    have hh := paired_fderiv_convolution_of_spatial_weak_derivative hf j
      (fun φ hφ hφc => parabolicSolution_cutoff_spacetime_integration_by_parts
        hI hU hsol hζ hζc hζsupp hφ hφc j) (hρ k) (hρc k) z
    simpa only [f, H, mul_comm] using hh
  simpa only [f, ← hd, H] using
    paired_tendsto_compact_convolution_L2 hH hHc hρ hρc hρ0 hρ1 hε hsupp

/-- Actual even-kernel temporal pairings converge to the cutoff quadratic
energy; no time derivative or trace of the solution is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_regularized_time_pairing_limit {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    (heven : ∀ k z, ρ k (-z) = ρ k z)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k)) :
    Tendsto (fun k => ∫ z in I ×ˢ U, u z *
      fderiv ℝ (fun y : ℝ × Vec d => ζ y *
        ∫ w : ℝ × Vec d, ζ w * u w * ρ k (y - w)) z (1, 0)) atTop
      (𝓝 (∫ z in I ×ˢ U, ζ z * fderiv ℝ ζ z (1, 0) * (u z)^2)) := by
  let μ := volume.restrict (I ×ˢ U)
  let C := fun k (z : ℝ × Vec d) => ∫ w : ℝ × Vec d, ζ w * u w * ρ k (z - w)
  have hf := parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol
    hζ.continuous hζc hζsupp
  have hC (k : ℕ) : MemLp (C k) 2 μ :=
    (paired_compact_convolution_memLp hf hζc.mul_right (hρ k) (hρc k)).mono_measure
      Measure.restrict_le_self
  have hd : Continuous (fun z : ℝ × Vec d => fderiv ℝ ζ z (1, 0)) :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
  have hfixed : MemLp (fun z => u z * fderiv ℝ ζ z (1, 0)) 2 μ :=
    (hd.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (1, 0)) _).mul' hsol.1
  have hlim : Tendsto (fun k => eLpNorm (fun z => C k z - ζ z * u z) 2 μ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (parabolicSolution_cutoff_regularization_limit hI hU hsol hζ hζc hζsupp
        hρ hρc hρ0 hρ1 hε hsupp) (fun _ => zero_le _) (fun k => ?_)
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have ht := Entropy.tendsto_integral_mul_of_eLpNorm_two hfixed hC
    (hf.mono_measure Measure.restrict_le_self) hlim
  have heq (k : ℕ) := parabolicSolution_regularized_time_pairing hI hU.measurableSet
    hsol hζ hζc hζsupp (hρ k) (hρc k) (heven k)
  simp only [C, μ] at ht
  simp_rw [heq]
  convert ht using 2
  congr 1
  funext z
  ring

end EinsteinRelation.Correctors
