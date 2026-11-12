import EinsteinRelation.Correctors.PairedPDECutoffEnergyClass

/-! # Integrability of the spatially weighted energy flux

Source: `paper/main.tex:824–832`. The original parabolic energy class
makes the flux paired with a compact spatial multiplier times the
solution genuinely integrable before any temporal testing.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The flux in the weak time derivative of the spatial energy is
integrable on the original cylinder. Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_spatial_energy_flux_integrable {d : ℕ} {K : ℝ}
    (hK : 0 < K) (A : Coefficient d K) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => dot ((A z.2).mulVec (G z)) (fun j =>
      ψ z.2 ^ 2 * G z j + 2 * ψ z.2 * u z * coordinateDerivative j ψ z.2))
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hbounded {w : Vec d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
      MemLp (fun z : ℝ × Vec d => w z.2) ∞ μ := by
    obtain ⟨B, hB⟩ := hwc.exists_bound_of_continuous hw
    exact memLp_top_of_bound (hw.measurable.comp measurable_snd).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hB z.2)
  have hψm : MemLp (fun z : ℝ × Vec d => ψ z.2 ^ 2) ∞ μ :=
    hbounded (hψ.continuous.pow 2) (by simpa only [pow_two] using hψc.mul_right (f' := ψ))
  apply integrable_finset_sum Finset.univ
  intro j _
  have hflux := parabolicSolution_flux_coordinate_memLp hK A hsol j
  have hG := parabolicSolution_gradient_coordinate_memLp hsol j
  have hD : Continuous (coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
  have hwm : MemLp (fun z : ℝ × Vec d =>
      2 * ψ z.2 * coordinateDerivative j ψ z.2) ∞ μ :=
    hbounded ((continuous_const.mul hψ.continuous).mul hD)
      ((hψc.mul_left (f := fun _ => (2 : ℝ))).mul_right)
  have hweightedG : MemLp (fun z => ψ z.2 ^ 2 * G z j) 2 μ := hG.mul' hψm
  have hweightedU : MemLp (fun z =>
      (2 * ψ z.2 * coordinateDerivative j ψ z.2) * u z) 2 μ := hsol.1.mul' hwm
  have hi := hflux.integrable_mul (hweightedG.add hweightedU)
  convert hi using 1
  funext z
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

end EinsteinRelation.Correctors
