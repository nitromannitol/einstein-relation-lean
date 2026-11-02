import EinsteinRelation.Sharpness.NoiseKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-! # Nondegeneracy of actual compact-test noise evaluations

AKM Definition 5.1 and Proposition 5.14, used at `paper/main.tex:1212–1216`.
A nonzero actual compact smooth test has positive L² mass. The generic Gaussian
characteristic law then excludes every almost-sure constant evaluation. This is
only a raw-noise prerequisite; nondegeneracy of the outer-convolved `h` remains
an internal obligation. No external existence statement is assumed in this file.
-/
open MeasureTheory
namespace EinsteinRelation.Sharpness

/-- Every nonzero actual compact test has strictly positive Gaussian variance. -/
theorem noiseTest_l2_mass_pos {d : ℕ} (f : NoiseTest d) (hf : f ≠ 0) :
    0 < ∫ y : Vec d, (f y)^2 := by
  have hex : ∃ y : Vec d, f y ≠ 0 := by
    by_contra h
    apply hf
    ext y
    exact not_not.mp (not_exists.mp h y)
  obtain ⟨y, hy⟩ := hex
  have hmul : HasCompactSupport ((f : Vec d → ℝ) * (f : Vec d → ℝ)) :=
    f.hasCompactSupport.mul_right
  have hsquare : HasCompactSupport (fun z : Vec d => (f z)^2) := by
    have h : (fun z : Vec d => (f z)^2) = (f : Vec d → ℝ) * (f : Vec d → ℝ) := by
      funext z
      simp only [pow_two, Pi.mul_apply]
    rw [h]
    exact hmul
  exact (f.contDiff.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hsquare (fun z => sq_nonneg (f z)) (pow_ne_zero 2 hy)

/-- A legitimate nonzero test evaluation of unit white noise is not almost surely constant. -/
theorem noise_evaluation_not_ae_constant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) (hf : f ≠ 0) (c : ℝ) :
    ¬ (∀ᵐ ω ∂P, W ω f = c) := by
  intro hc
  have hv := noiseTest_l2_mass_pos f hf
  have heq : (∫ ω, Complex.exp (Complex.I * (1 : ℂ) * (W ω f : ℂ)) ∂P) =
      Complex.exp (Complex.I * (1 : ℂ) * (c : ℂ)) := by
    calc
      _ = ∫ _ : Ω, Complex.exp (Complex.I * (1 : ℂ) * (c : ℂ)) ∂P := by
        apply integral_congr_ae
        filter_upwards [hc] with ω hω
        rw [hω]
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  have he := congrArg norm (heq.symm.trans (hwhite f 1))
  have hnorm : ‖Complex.exp (Complex.I * (1 : ℂ) * (c : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm, Complex.norm_exp] at he
  have hexp : Real.exp (-(1/2 : ℝ) * ∫ y : Vec d, (f y)^2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hreal : (((-(1/2 : ℝ)) * (1 : ℝ)^2 * ∫ y : Vec d, (f y)^2) : ℂ).re =
      -(1/2 : ℝ) * ∫ y : Vec d, (f y)^2 := by simp
  rw [hreal] at he
  linarith
end EinsteinRelation.Sharpness
