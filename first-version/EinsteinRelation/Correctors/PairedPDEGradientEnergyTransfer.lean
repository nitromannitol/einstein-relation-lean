import EinsteinRelation.Correctors.PairedPDEWeakEnergyComparison

/-! # Transfer from scalar energy to cutoff gradient energy

Source: `paper/main.tex:844–855`. Bounds on the actual cutoff derivatives
turn the proved weak Caccioppoli inequality into a scalar-energy estimate.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A bound on the cutoff's time and spatial errors transfers actual
scalar L² decay to weighted gradient energy. Source: `paper/main.tex:844–855`. -/
theorem parabolicSolution_cutoff_energy_le_scalar {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {B : ℝ} (hB : ∀ z ∈ I ×ˢ U, 2 * ζ z * fderiv ℝ ζ z (1, 0) +
      4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B) :
    (∫ z in I ×ˢ U, ζ z ^ 2 * euclideanSq (G z)) ≤
      B * ∫ z in I ×ˢ U, (u z)^2 := by
  let μ := volume.restrict (I ×ˢ U)
  let T := fun z => (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0)
  let E := fun z => (u z)^2 *
    euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j))
  have hζm : MemLp ζ ∞ μ := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hD : MemLp (fun z => fderiv ℝ ζ z (1, 0)) ∞ μ :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
      |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (1, 0)) _
  have huζ : MemLp (fun z => u z * ζ z) 2 μ := hζm.mul' hsol.1
  have huD : MemLp (fun z => u z * fderiv ℝ ζ z (1, 0)) 2 μ := hD.mul' hsol.1
  have hT : Integrable T μ := by
    convert huζ.integrable_mul huD using 1
    funext z
    simp only [T, Pi.mul_apply]
    ring
  have hc := parabolicSolution_cutoff_energy hK hI hU hsol hζ hζc hζsupp
  have hE : Integrable E μ := hc.2.1
  have hle : (∫ z, 2 * T z + 4 * K^2 * E z ∂μ) ≤
      ∫ z, B * (u z)^2 ∂μ := by
    apply integral_mono_ae ((hT.const_mul 2).add (hE.const_mul (4*K^2)))
      (hsol.1.integrable_sq.const_mul B)
    filter_upwards [ae_restrict_mem (hI.prod hU.measurableSet)] with z hz
    have h := mul_le_mul_of_nonneg_left (hB z hz) (sq_nonneg (u z))
    simp only [Pi.add_apply] at *
    dsimp only [T, E]
    nlinarith only [h]
  rw [integral_add (hT.const_mul 2) (hE.const_mul (4*K^2)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hle
  exact hc.2.2.trans hle

/-- The same transfer holds for the actual difference in two environments
whose coefficients agree locally. Source: `paper/main.tex:844–855`. -/
theorem paired_cutoff_energy_le_scalar {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A₁ A₂ : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U) (hA : Set.EqOn A₁ A₂ U)
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsParabolicSolution A₁ I U u₁ G₁)
    (h₂ : IsParabolicSolution A₂ I U u₂ G₂)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {B : ℝ} (hB : ∀ z ∈ I ×ˢ U, 2 * ζ z * fderiv ℝ ζ z (1, 0) +
      4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) ≤ B) :
    (∫ z in I ×ˢ U, ζ z ^ 2 * euclideanSq (G₁ z - G₂ z)) ≤
      B * ∫ z in I ×ˢ U, (u₁ z - u₂ z)^2 :=
  parabolicSolution_cutoff_energy_le_scalar hK hI hU
    (paired_parabolicSolution hK hI hU.measurableSet hA h₁ h₂) hζ hζc hζsupp hB

end EinsteinRelation.Correctors
