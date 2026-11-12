import EinsteinRelation.Correctors.PairedPDEPolarizedEnergy
import EinsteinRelation.Correctors.SpatialEnergyTimeIntegrability
import EinsteinRelation.Correctors.EnergyTimeFubini
import EinsteinRelation.Correctors.EnergyTensorDerivative
import EinsteinRelation.Correctors.EnergyTimeSelector

/-! # The weak time equation of the actual spatial energy

Source: `paper/main.tex:824–832`. Polarization with a compact temporal
reference cutoff removes the square restriction on the time test. Fubini
then identifies the literal spatial energy and its integrable flux.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual weak parabolic equation implies the distributional time
equation of every smooth compactly weighted spatial energy. No primitive
identity or temporal derivative of the solution is assumed.
Source: `paper/main.tex:824–832`. -/
theorem parabolicSolution_spatial_energy_weak_time_equation {d : ℕ} {K a b : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {U : Set (Vec d)} (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b, (∫ x in U, ψ x ^ 2 * u (t,x) ^ 2) * deriv η t) =
      -(∫ t in Set.Ioo a b,
        (-2 * ∫ x in U, dot ((A x).mulVec (G (t,x))) (fun j =>
          ψ x ^ 2 * G (t,x) j + 2 * ψ x * u (t,x) * coordinateDerivative j ψ x)) * η t) := by
  obtain ⟨ρ, hρ, hρc, hρs, hηρ, hηDρ, hρDη⟩ := exists_energy_time_selector hη hηc hηs
  let ζ : ℝ × Vec d → ℝ := fun z => η z.1 * ψ z.2
  let θ : ℝ × Vec d → ℝ := fun z => ρ z.1 * ψ z.2
  let P : ℝ × Vec d → ℝ := fun z => dot ((A z.2).mulVec (G z)) (fun j =>
    ψ z.2 ^ 2 * G z j + 2 * ψ z.2 * u z * coordinateDerivative j ψ z.2)
  let E : ℝ × Vec d → ℝ := fun z => ψ z.2 ^ 2 * u z ^ 2
  let μ := volume.restrict (Set.Ioo a b)
  let ν := volume.restrict U
  have hprod : volume.restrict (Set.Ioo a b ×ˢ U) = μ.prod ν := by
    simp only [μ, ν, Measure.volume_eq_prod, Measure.prod_restrict]
  have hsupp {β : ℝ → ℝ} (hs : tsupport β ⊆ Set.Ioo a b) :
      tsupport (fun z : ℝ × Vec d => β z.1 * ψ z.2) ⊆ Set.Ioo a b ×ˢ U := by
    refine (closure_minimal ?_ ((isClosed_tsupport β).prod (isClosed_tsupport ψ))).trans
      (Set.prod_mono hs hψs)
    intro z hz
    exact ⟨subset_tsupport β (fun h => hz (by simp only [h, zero_mul])),
      subset_tsupport ψ (fun h => hz (by simp only [h, mul_zero]))⟩
  have hcompact {β : ℝ → ℝ} (hc : HasCompactSupport β) :
      HasCompactSupport (fun z : ℝ × Vec d => β z.1 * ψ z.2) := by
    simpa only [pow_one, mul_one] using
      hasCompactSupport_tensor_cutoff hc hψc 1 (by decide) (fun _ => (1 : ℝ))
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (hη.comp contDiff_fst).mul (hψ.comp contDiff_snd)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := (hρ.comp contDiff_fst).mul (hψ.comp contDiff_snd)
  have hpol := parabolicSolution_polarized_cutoff_energy_identity hK
    measurableSet_Ioo hU hsol hζ hθ (hcompact hηc) (hcompact hρc)
    (by simpa only [interior_Ioo] using hsupp hηs)
    (by simpa only [interior_Ioo] using hsupp hρs)
  have hflux (z : ℝ × Vec d) :
      dot ((A z.2).mulVec (G z)) (fun j => ζ z * θ z * G z j + u z *
        (ζ z * fderiv ℝ θ z (0, unitVector j) + θ z * fderiv ℝ ζ z (0, unitVector j))) =
        η z.1 * P z := by
    simp only [ζ, θ, fderiv_energy_tensor hη hψ, fderiv_energy_tensor hρ hψ,
      dot, P, Finset.mul_sum, coordinateDerivative]
    apply Finset.sum_congr rfl
    intro j _
    have he := hηρ z.1
    change _ = _
    calc
      _ = (η z.1 * ρ z.1) * (((A z.2).mulVec (G z)) j *
          (ψ z.2 ^ 2 * G z j + 2 * ψ z.2 * u z * fderiv ℝ ψ z.2 (unitVector j))) := by ring
      _ = _ := by rw [he]
  have htime (z : ℝ × Vec d) :
      (ζ z * fderiv ℝ θ z (1,0) + θ z * fderiv ℝ ζ z (1,0)) * u z ^ 2 =
        deriv η z.1 * E z := by
    simp only [ζ, θ, fderiv_energy_tensor hη hψ, fderiv_energy_tensor hρ hψ,
      mul_one, map_zero, mul_zero, add_zero, E]
    calc
      _ = (η z.1 * deriv ρ z.1 + ρ z.1 * deriv η z.1) * (ψ z.2 ^ 2 * u z ^ 2) := by ring
      _ = _ := by rw [hηDρ, hρDη, zero_add]
  have hPi : Integrable P (μ.prod ν) := by
    rw [← hprod]
    exact parabolicSolution_spatial_energy_flux_integrable hK A hsol hψ hψc
  have hEi : Integrable E (μ.prod ν) := by
    rw [← hprod]
    exact parabolicSolution_spatial_energy_integrable hsol hψ hψc
  have he := hpol.2
  simp only [hflux, htime] at he
  rw [hprod,
    integral_time_mul_spatial_integral μ ν hPi hη.continuous hηc,
    integral_time_mul_spatial_integral μ ν hEi (hη.continuous_deriv (by norm_num)) hηc.deriv] at he
  change (∫ t, (∫ x, E (t,x) ∂ν) * deriv η t ∂μ) =
    -(∫ t, (-2 * ∫ x, P (t,x) ∂ν) * η t ∂μ)
  calc
    _ = ∫ t, deriv η t * (∫ x, E (t,x) ∂ν) ∂μ := by simp only [mul_comm]
    _ = 2 * ∫ t, η t * (∫ x, P (t,x) ∂ν) ∂μ := he.symm
    _ = _ := by rw [← integral_const_mul, ← integral_neg]; congr 1; funext t; ring

end EinsteinRelation.Correctors
