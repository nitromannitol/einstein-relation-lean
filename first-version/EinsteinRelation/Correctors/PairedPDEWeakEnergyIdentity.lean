import EinsteinRelation.Correctors.PairedPDEDoubleCutoffLimits
import EinsteinRelation.Correctors.PairedPDEEnergyTesting
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The energy identity for the actual weak parabolic solution

Source: `paper/main.tex:832–840`. Smooth compact even kernels are constructed
here. Their actual derivative and temporal pairing limits close the weak
equation, without a temporal derivative of the solution or an approximation
premise.
-/

open MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Testing the actual energy-class solution with a compact cutoff times
itself gives the energy identity. No smoothness of the solution, trace, or
approximation limit is a hypothesis. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_energy_identity {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U) :
    Integrable (fun z => dot ((A z.2).mulVec (G z))
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j)))
        (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, dot ((A z.2).mulVec (G z))
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j))) =
        ∫ z in I ×ˢ U, ζ z * fderiv ℝ ζ z (1, 0) * (u z)^2 := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let b : ℕ → ContDiffBump (0 : ℝ × Vec d) :=
    fun k => ⟨ε k / 2, ε k, half_pos (hεpos k), half_lt_self (hεpos k)⟩
  let ρ : ℕ → ℝ × Vec d → ℝ := fun k => (b k).normed volume
  have hρ (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ρ k) := (b k).contDiff_normed
  have hρc (k : ℕ) : HasCompactSupport (ρ k) := (b k).hasCompactSupport_normed
  have hρ0 (k : ℕ) (z : ℝ × Vec d) : 0 ≤ ρ k z := (b k).nonneg_normed z
  have hρ1 (k : ℕ) : (∫ z : ℝ × Vec d, ρ k z) = 1 := (b k).integral_normed
  have heven (k : ℕ) (z : ℝ × Vec d) : ρ k (-z) = ρ k z := (b k).normed_neg z
  have hsupp (k : ℕ) : Function.support (ρ k) ⊆ closedBall 0 (ε k) := by
    exact (subset_tsupport (ρ k)).trans (by rw [(b k).tsupport_normed_eq])
  have hζsupp' : tsupport ζ ⊆ I ×ˢ U :=
    hζsupp.trans (Set.prod_mono interior_subset Set.Subset.rfl)
  let ψ : ℕ → ℝ × Vec d → ℝ := fun k z =>
    ζ z * ∫ w : ℝ × Vec d, ζ w * u w * ρ k (z - w)
  have hψ (k : ℕ) := parabolicSolution_regularized_cutoff_test hK hI hU.measurableSet
    hsol hζ hζc hζsupp (hρ k) (hρc k)
  have hx (j : Fin d) := parabolicSolution_double_cutoff_gradient_limit hI hU hsol
    hζ hζc hζsupp' hρ hρc hρ0 hρ1 hε hsupp j
  have ht := parabolicSolution_regularized_time_pairing_limit hI hU hsol hζ hζc hζsupp'
    hρ hρc hρ0 hρ1 heven hε hsupp
  exact parabolicSolution_flux_test_of_pairing_approximation hK A hsol ψ
    (fun k => (hψ k).1) (fun k => (hψ k).2.1) (fun k => (hψ k).2.2.1)
    (fun j => (hx j).1) (fun j => (hx j).2) ht

/-- Locally agreeing coefficients give the actual paired energy identity,
with no smoothness assumption on either solution and no independence
assumption on the coefficient fields. Source: `paper/main.tex:822–840`. -/
theorem paired_cutoff_energy_identity {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A₁ A₂ : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U) (hA : Set.EqOn A₁ A₂ U)
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsParabolicSolution A₁ I U u₁ G₁)
    (h₂ : IsParabolicSolution A₂ I U u₂ G₂)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U) :
    let v := fun z => u₁ z - u₂ z
    let H := fun z => G₁ z - G₂ z
    Integrable (fun z => dot ((A₁ z.2).mulVec (H z))
      (fun j => ζ z ^ 2 * H z j + 2 * ζ z * v z * fderiv ℝ ζ z (0, unitVector j)))
        (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U, dot ((A₁ z.2).mulVec (H z))
      (fun j => ζ z ^ 2 * H z j + 2 * ζ z * v z * fderiv ℝ ζ z (0, unitVector j))) =
        ∫ z in I ×ˢ U, ζ z * fderiv ℝ ζ z (1, 0) * (v z)^2 := by
  exact parabolicSolution_cutoff_energy_identity hK hI hU
    (paired_parabolicSolution hK hI hU.measurableSet hA h₁ h₂) hζ hζc hζsupp

end EinsteinRelation.Correctors
