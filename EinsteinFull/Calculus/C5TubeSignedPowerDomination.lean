import EinsteinFull.Calculus.C5TubeSignedPowerEnergy

open MeasureTheory Set intervalIntegral
open PDE.Parabolic.LocalMax

namespace EinsteinFull.Calculus

noncomputable section

/-- The positive branch lies above its quadratic expansion at zero. -/
theorem c5_power_quadratic_le_of_nonneg {p ε N t : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (hN : 0 ≤ N) (ht : 0 ≤ t) :
    ε ^ p + (p * ε ^ (p - 1)) * t +
      (p * (p - 1) * ε ^ (p - 2)) * t ^ 2 / 2 ≤ powF p ε N t := by
  let a : ℝ := p * ε ^ (p - 1)
  let c : ℝ := p * (p - 1) * ε ^ (p - 2)
  have hc : ∀ r : ℝ, c ≤ powF2 p ε N r := by
    intro r
    have hb := le_powCap (p := p) (ε := ε) hN r
    have hpw := Real.rpow_le_rpow hε.le hb (sub_nonneg.mpr hp)
    exact mul_le_mul_of_nonneg_left hpw (mul_nonneg (by linarith) (by linarith))
  have hd : ∀ r : ℝ, 0 ≤ r → a + c * r ≤ powF1 p ε N r := by
    intro r hr
    have hi : (∫ _x in (0 : ℝ)..r, c) ≤ ∫ x in (0 : ℝ)..r, powF2 p ε N x := by
      exact integral_mono_on hr (intervalIntegrable_const) ((powF2_continuous hε hN).intervalIntegrable _ _)
        (fun x _ => hc x)
    rw [intervalIntegral.integral_const] at hi
    simp only [sub_zero, smul_eq_mul] at hi
    dsimp [powF1, a]
    linarith
  have hi : (∫ r in (0 : ℝ)..t, (a + c * r)) ≤ ∫ r in (0 : ℝ)..t, powF1 p ε N r := by
    refine integral_mono_on ht ((by fun_prop : Continuous fun r : ℝ => a + c * r).intervalIntegrable _ _)
      ((powF1_continuous hε hN).intervalIntegrable _ _) ?_
    intro r hr
    exact hd r hr.1
  have hv : ∫ r in (0 : ℝ)..t, (a + c * r) = a * t + c * t ^ 2 / 2 := by
    have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun r => a * r + c * r ^ 2 / 2) (a + c * r) r := by
      intro r _
      have h1 : HasDerivAt (fun r => a * r) a r := by simpa using (hasDerivAt_id' r).const_mul a
      have h2 : HasDerivAt (fun r => c * r ^ 2 / 2) (c * r) r :=
        ((((hasDerivAt_id' r).pow 2).const_mul c).div_const 2).congr_deriv (by simp; ring)
      exact h1.add h2
    rw [integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun r : ℝ => a + c * r).intervalIntegrable 0 t)]
    ring
  rw [hv] at hi
  change ε ^ p + a * t + c * t ^ 2 / 2 ≤ ε ^ p + ∫ r in (0 : ℝ)..t, powF1 p ε N r
  linarith

/-- The canonical truncated power is dominated by the absolute full power. -/
theorem c5_all_real_truncated_power_le_abs {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    powF p ε (n : ℝ) s ≤ Real.rpow (|s| + ε) p := by
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [Real.rpow_eq_pow]
  by_cases hs : 0 ≤ s
  · simpa only [abs_of_nonneg hs] using powF_le (by linarith : 1 < p) hε hN hs
  · have hs' : s ≤ 0 := le_of_not_ge hs
    have ht : 0 ≤ -s := neg_nonneg.mpr hs'
    have hquad := c5_power_quadratic_le_of_nonneg hp hε hN ht
    have hfull := powF_le (by linarith : 1 < p) hε hN ht
    have ha : 0 ≤ p * ε ^ (p - 1) := by positivity
    rw [c5_power_energy_of_nonpos hε hN hs', abs_of_nonpos hs']
    nlinarith [hquad, hfull, mul_nonpos_of_nonneg_of_nonpos ha hs']

end
end EinsteinFull.Calculus
