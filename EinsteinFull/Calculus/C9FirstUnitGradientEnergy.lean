import EinsteinFull.Work.W3.ForwardFullHorizonEnergySupport
import EinsteinFull.Calculus.C9RetainedTraceIdentity
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Uniform actual gradient energy on the first unit time interval. -/
theorem actual_first_unit_gradient_energy
    : ∀ (d : ℕ) (D : StructuralData d), ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
        (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
        (hP : IsComplexEnvironmentSemigroup Q i ζ P)
        (f : Lp ℂ 2 (reducedLaw Q)), ‖ζ‖ ≤ 2 →
      ∀ T : ℝ, 0 ≤ T → T ≤ 1 →
        IntegrableOn (fun s : ℝ => ∑ j : Fin d, ‖hP.gradientOrbit f s j‖^2) (Icc 0 T) ∧
        (∫ s in Icc (0 : ℝ) T, ∑ j : Fin d, ‖hP.gradientOrbit f s j‖^2) ≤ C * ‖f‖^2 := by
  intro d D
  obtain ⟨C₀, hC₀, henergy⟩ := forward_fullHorizon_gradient_energy d D.ellipticity
  refine ⟨C₀ * Real.exp (4 * C₀), mul_pos hC₀ (Real.exp_pos _), ?_⟩
  intro Q i ζ P hP f hζ T hT hT₁
  obtain ⟨hi, hb⟩ := henergy Q i ζ P hP f T hT
  have hsquare : ‖ζ‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg ζ]
  have hexponent : C₀ * ‖ζ‖ ^ 2 * T ≤ 4 * C₀ := calc
    C₀ * ‖ζ‖ ^ 2 * T ≤ C₀ * 4 * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hC₀.le) hT
    _ ≤ C₀ * 4 * 1 := mul_le_mul_of_nonneg_left hT₁ (by positivity)
    _ = 4 * C₀ := by ring
  have hb' := hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hC₀.le)
    (sq_nonneg ‖f‖))
  simpa only [PiLp.norm_sq_eq_of_L2] using And.intro hi hb'

end EinsteinFull.Blueprint
