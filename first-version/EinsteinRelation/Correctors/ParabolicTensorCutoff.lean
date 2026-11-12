import EinsteinRelation.Correctors.PairedPDEGradientEnergyTransfer
import EinsteinRelation.Correctors.ParabolicTensorDerivatives

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Uniform derivative errors for tensor cutoffs in Caccioppoli.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem parabolic_tensor_cutoff_error_bound {d : ℕ} (K : ℝ)
    {η : ℝ → ℝ} {χ : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {M B : ℝ} (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hηb : ∀ t, |η t| ≤ 1) (hηD : ∀ t, |deriv η t| ≤ M)
    (hχb : ∀ x, |χ x| ≤ 1) (hχD : ∀ x, ‖gradient χ x‖ ≤ B) :
    let ζ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2
    ∀ z, 2 * ζ z * fderiv ℝ ζ z (1,0) +
      4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ z (0,unitVector j)) ≤
        2 * M + 4 * K^2 * d * B^2 := by
  intro ζ z
  rcases z with ⟨t, x⟩
  have h_fderiv_time : fderiv ℝ ζ (t, x) (1, 0) = deriv η t * χ x := by
    have h := parabolic_tensor_cutoff_derivative hη hχ (t,x) (1,0)
    simpa using h
  have h_fderiv_spatial (j : Fin d) : fderiv ℝ ζ (t, x) (0, unitVector j) = η t * fderiv ℝ χ x (unitVector j) := by
    have h := parabolic_tensor_cutoff_derivative hη hχ (t,x) (0,unitVector j)
    simpa using h
  have h_zeta : ζ (t, x) = η t * χ x := rfl
  rw [h_zeta, h_fderiv_time]
  have h_sq_η : (η t)^2 ≤ 1 := by
    have h_abs := hηb t
    rcases abs_le.mp h_abs with ⟨h_low, h_high⟩
    nlinarith
  have h_sq_χ : (χ x)^2 ≤ 1 := by
    have h_abs := hχb x
    rcases abs_le.mp h_abs with ⟨h_low, h_high⟩
    nlinarith
  have h_time_part : 2 * (η t * χ x) * (deriv η t * χ x) ≤ 2 * M := by
    have hprod : η t * deriv η t * (χ x)^2 ≤ M := by
      have h_abs_prod : |η t * deriv η t * (χ x)^2| ≤ M := by
        calc
          |η t * deriv η t * (χ x)^2| = |η t| * |deriv η t| * |(χ x)^2| := by
            simp [abs_mul]
          _ ≤ 1 * M * 1 := by
            have h1 : |η t| ≤ 1 := hηb t
            have h2 : |deriv η t| ≤ M := hηD t
            have h3 : |(χ x)^2| ≤ 1 := by
              have : |(χ x)^2| = (χ x)^2 := abs_of_nonneg (sq_nonneg (χ x))
              rw [this]
              exact h_sq_χ
            gcongr
          _ = M := by ring
      have h_le_abs : η t * deriv η t * (χ x)^2 ≤ |η t * deriv η t * (χ x)^2| := le_abs_self _
      nlinarith
    nlinarith
  have h_spatial_bound : euclideanSq (fun j => fderiv ℝ ζ (t, x) (0, unitVector j)) ≤ (d : ℝ) * B^2 := by
    rw [euclideanSq, dot]
    calc
      ∑ j : Fin d, (fderiv ℝ ζ (t, x) (0, unitVector j)) * (fderiv ℝ ζ (t, x) (0, unitVector j))
          = ∑ j : Fin d, (η t * fderiv ℝ χ x (unitVector j)) * (η t * fderiv ℝ χ x (unitVector j)) := by
            simp [h_fderiv_spatial]
      _ = ∑ j : Fin d, ((η t)^2 * ((fderiv ℝ χ x (unitVector j)) * (fderiv ℝ χ x (unitVector j)))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
      _ = (η t)^2 * ∑ j : Fin d, ((fderiv ℝ χ x (unitVector j)) * (fderiv ℝ χ x (unitVector j))) := by
            simp [Finset.mul_sum]
      _ ≤ 1 * ∑ j : Fin d, (B * B) := by
            have h_nonneg_sum : 0 ≤ ∑ j : Fin d, ((fderiv ℝ χ x (unitVector j)) * (fderiv ℝ χ x (unitVector j))) :=
              Finset.sum_nonneg fun j _ => by
                nlinarith [sq_nonneg (fderiv ℝ χ x (unitVector j))]
            have h_each (j : Fin d) : (fderiv ℝ χ x (unitVector j)) * (fderiv ℝ χ x (unitVector j)) ≤ B * B := by
              have h_coord_eq : fderiv ℝ χ x (unitVector j) = coordinateDerivative j χ x := rfl
              have h_grad_eq : coordinateDerivative j χ x = gradient χ x j := rfl
              rw [h_coord_eq, h_grad_eq]
              have h_abs_grad : |gradient χ x j| ≤ B := by
                have h_le_norm : |gradient χ x j| ≤ ‖gradient χ x‖ := by
                  simpa [Real.norm_eq_abs] using norm_le_pi_norm (gradient χ x) j
                exact h_le_norm.trans (hχD x)
              have h_sq_bound : (gradient χ x j)^2 ≤ B^2 := by
                rcases abs_le.mp h_abs_grad with ⟨h_low, h_high⟩
                nlinarith
              simpa [sq] using h_sq_bound
            have h_sum_le : ∑ j : Fin d, ((fderiv ℝ χ x (unitVector j)) * (fderiv ℝ χ x (unitVector j))) ≤
                ∑ j : Fin d, (B * B) :=
              Finset.sum_le_sum fun j _ => h_each j
            nlinarith
      _ = (d : ℝ) * (B * B) := by simp
      _ = (d : ℝ) * B^2 := by ring
  have h_spatial_part : 4 * K^2 * euclideanSq (fun j => fderiv ℝ ζ (t, x) (0, unitVector j)) ≤
      4 * K^2 * (d : ℝ) * B^2 := by
    nlinarith [h_spatial_bound, sq_nonneg K]
  nlinarith

end EinsteinRelation.Correctors
