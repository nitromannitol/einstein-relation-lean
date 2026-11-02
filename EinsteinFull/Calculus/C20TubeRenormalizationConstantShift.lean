import EinsteinFull.Calculus.C20TubeGeneralChainInstantiation
import EinsteinFull.Calculus.C20TubeConstantTimeTest
import EinsteinFull.Calculus.C18TubeFixedNonlinearIntegrability

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- Removing an integrable zero-mean constant multiple does not change the mean. -/
theorem c20_integral_constant_shift_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : X → ℝ) (c : ℝ)
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hcentered : (∫ x, A x - c * B x ∂μ) = 0)
    (hconstant : (∫ x, B x ∂μ) = 0) :
    (∫ x, A x ∂μ) = 0 := by
  rw [integral_sub hA (hB.const_mul c), integral_const_mul, hconstant, mul_zero,
    sub_zero] at hcentered
  exact hcentered

/-- Constant shifts preserve both derivatives used in the chain rule. -/
theorem c20_deriv_sub_value_zero (F : ℝ → ℝ) :
    deriv (fun r => F r - F 0) = deriv F ∧
    deriv (deriv (fun r => F r - F 0)) = deriv (deriv F) := by
  have h : deriv (fun r => F r - F 0) = deriv F := deriv_sub_const_fun (F 0)
  exact ⟨h, congrArg deriv h⟩

/-- The full weighted chain-rule pairing is unchanged by centering the nonlinearity.
The integrability premise concerns the actual uncentered three-term pairing. -/
theorem c20_weighted_renormalization_of_centered
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (F : ℝ → ℝ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hA : Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hcentered : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0) +
      deriv (fun r => F r - F 0) (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv (fun r => F r - F 0)) (u z) *
        dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1,0)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hD : Continuous D := (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ (1,0))
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  have hB : Integrable (fun z : ℝ × Vec d => -(ρ z.2 * D z)) μ := by
    have h := hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hρbound z.2)
    have h' := (h.integrableOn (s := Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)).neg
    apply h'.congr
    filter_upwards with z
    dsimp [D]
    ring
  have hzero : (∫ z, -(ρ z.2 * D z) ∂μ) = 0 := by
    simpa [μ, D] using c20_weighted_constant_time_test_integral_zero hκ ρ α hell 0 1 ψ hψ hψc hψs
  apply c20_integral_constant_shift_zero μ _ _ (F 0) hA hB _ hzero
  have hder := c20_deriv_sub_value_zero F
  convert hcentered using 1
  apply integral_congr_ae
  filter_upwards with z
  rw [hder.1]
  dsimp [D]
  ring

/-- Caloric data supply the full-pairing integrability required by the shift. -/
theorem c20_weighted_caloric_renormalization_of_centered
    {d : ℕ} {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R)
    (hcentered : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * (F (u z) - F 0)) * fderiv ℝ ψ z (1,0) +
      deriv (fun r => F r - F 0) (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv (fun r => F r - F 0)) (u z) *
        dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0) :
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  apply c20_weighted_renormalization_of_centered hκ ρ α hell u G F ψ hψ hψc hψs
    (c18_tested_nonlinear_pairing_integrable hκ hR hab ρ α hell 0 u G
      hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder ψ hψ hψc hψs)
  exact hcentered

end EinsteinFull.Calculus
