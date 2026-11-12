import EinsteinRelation.Correctors.PairedPDERegularizedEnergyLimit

/-! # The energy identity for the actual weak parabolic solution

Source: `paper/main.tex:832–840`. A shrinking sequence of normalized
even smooth kernels supplies every approximation premise internally.
The resulting identity uses only the stated weak energy class.
-/

open MeasureTheory Filter Metric
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Testing the actual weak equation by the square of a compact cutoff
and the solution gives the local energy identity. No smoothness or temporal
derivative of the solution, nor an energy identity, is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_regularized_cutoff_energy_identity {d : ℕ} {K : ℝ}
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
        ∫ z in I ×ˢ U, (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := one_div_pos.mpr (by positivity)
  let b (k : ℕ) : ContDiffBump (0 : ℝ × Vec d) :=
    ⟨ε k / 2, ε k, half_pos (hε k), half_lt_self (hε k)⟩
  let ρ := fun k => (b k).normed volume
  have hρsupp (k : ℕ) : Function.support (ρ k) ⊆ closedBall 0 (ε k) := by
    rw [← show tsupport (ρ k) = closedBall 0 (ε k) from (b k).tsupport_normed_eq]
    exact subset_tsupport _
  have hr := parabolicSolution_regularized_energy_limit hK hI hU hsol hζ hζc hζsupp
    (fun k => (b k).contDiff_normed) (fun k => (b k).hasCompactSupport_normed)
    (fun k => (b k).nonneg_normed) (fun k => (b k).integral_normed)
    (fun k => (b k).normed_neg)
    (show Tendsto ε atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat) hρsupp
  have hH (z : ℝ × Vec d) : (fun j => fderiv ℝ ζ z (0, unitVector j) * (ζ z * u z) +
      ζ z * (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j))) =
      fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j) := by
    funext j
    ring
  have hE : (fun z => (u z * fderiv ℝ ζ z (1, 0)) * (ζ z * u z)) =
      fun z => (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0) := by
    funext z
    ring
  simpa only [hH, hE] using hr

end EinsteinRelation.Correctors
