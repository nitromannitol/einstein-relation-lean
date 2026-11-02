import EllipticRegularity.Parabolic.LocalMax.PowerFamilyStruct

open MeasureTheory Set intervalIntegral

namespace EinsteinFull.Calculus

noncomputable section

/-- The power profile is constant on negative inputs. -/
theorem c5_power_cap_of_nonpos {p ε N s : ℝ} (hN : 0 ≤ N) (hs : s ≤ 0) :
    PDE.Parabolic.LocalMax.powCap p ε N s = ε := by
  have hm : max (s + ε) ε = ε := max_eq_right (by linarith)
  have hn : min ε (N + ε) = ε := min_eq_left (by linarith)
  simp [PDE.Parabolic.LocalMax.powCap, hm, hn]
/-- The derivative of the energy power is affine on negative inputs. -/
theorem c5_power_deriv_of_nonpos {p ε N s : ℝ} (hε : 0 < ε)
    (hN : 0 ≤ N) (hs : s ≤ 0) :
    deriv (PDE.Parabolic.LocalMax.powF p ε N) s =
      p * ε ^ (p - 1) + p * (p - 1) * ε ^ (p - 2) * s := by
  rw [PDE.Parabolic.LocalMax.deriv_powF hε hN]
  unfold PDE.Parabolic.LocalMax.powF1
  have hc : ∫ r in (0 : ℝ)..s, PDE.Parabolic.LocalMax.powF2 p ε N r =
      ∫ _r in (0 : ℝ)..s, p * (p - 1) * ε ^ (p - 2) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_ge hs] at hr
    simp [PDE.Parabolic.LocalMax.powF2, c5_power_cap_of_nonpos hN hr.2]
  rw [hc, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The energy power is quadratic on negative inputs. -/
theorem c5_power_energy_of_nonpos {p ε N s : ℝ} (hε : 0 < ε)
    (hN : 0 ≤ N) (hs : s ≤ 0) :
    PDE.Parabolic.LocalMax.powF p ε N s =
      ε ^ p + (p * ε ^ (p - 1)) * s +
        (p * (p - 1) * ε ^ (p - 2)) * s ^ 2 / 2 := by
  let a : ℝ := p * ε ^ (p - 1)
  let c : ℝ := p * (p - 1) * ε ^ (p - 2)
  have hc : ∫ r in (0 : ℝ)..s, PDE.Parabolic.LocalMax.powF1 p ε N r =
      ∫ r in (0 : ℝ)..s, (a + c * r) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_ge hs] at hr
    have h := c5_power_deriv_of_nonpos (p := p) hε hN hr.2
    rw [PDE.Parabolic.LocalMax.deriv_powF hε hN] at h
    simpa [a, c] using h
  have hv : ∫ r in (0 : ℝ)..s, (a + c * r) = a * s + c * s ^ 2 / 2 := by
    have hd : ∀ r ∈ Set.uIcc (0 : ℝ) s,
        HasDerivAt (fun r => a * r + c * r ^ 2 / 2) (a + c * r) r := by
      intro r _
      have h1 : HasDerivAt (fun r => a * r) a r := by simpa using (hasDerivAt_id' r).const_mul a
      have h2 : HasDerivAt (fun r => c * r ^ 2 / 2) (c * r) r :=
        ((((hasDerivAt_id' r).pow 2).const_mul c).div_const 2).congr_deriv (by simp; ring)
      exact h1.add h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun r : ℝ => a + c * r).intervalIntegrable 0 s)]
    ring
  unfold PDE.Parabolic.LocalMax.powF
  rw [hc, hv]
  dsimp [a, c]
  ring

/-- The signed negative branch of the canonical power has nonnegative energy and
curvature, with the derivative controlled by the energy. -/
theorem c5_power_energy_structure_of_nonpos {p ε N s : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (hN : 0 ≤ N) (hs : s ≤ 0) :
    let F := PDE.Parabolic.LocalMax.powF p ε N
    0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      (deriv F s)^2 ≤ (2+p/(p-1)) * deriv (deriv F) s * F s := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp2 : 0 ≤ p - 2 := sub_nonneg.mpr hp
  have ha : 0 < ε ^ (p - 2) := Real.rpow_pos_of_pos hε _
  obtain ⟨hpow1, hpow2, _, _⟩ := PDE.Parabolic.LocalMax.rpow_split hε p
  have hcurv : 0 ≤ p * (p - 1) * ε ^ (p - 2) := by positivity
  have hF : 0 ≤ ε ^ (p - 2) * (ε ^ 2 + p * ε * s + p * (p - 1) * s ^ 2 / 2) := by
    have hsq : 0 ≤ (ε + p / 2 * s) ^ 2 := sq_nonneg _
    have hrem : 0 ≤ p * (p - 2) * s ^ 2 / 4 := by positivity
    have heq : ε ^ 2 + p * ε * s + p * (p - 1) * s ^ 2 / 2 =
        (ε + p / 2 * s) ^ 2 + p * (p - 2) * s ^ 2 / 4 := by ring
    rw [heq]
    positivity
  have hdiff : 0 ≤ p * (p - 2) * (ε ^ (p - 2)) ^ 2 * ε ^ 2 := by positivity
  have hbound : (p * (ε ^ (p - 2) * ε) + p * (p - 1) * ε ^ (p - 2) * s) ^ 2 ≤
      2 * (p * (p - 1) * ε ^ (p - 2)) *
        (ε ^ (p - 2) * (ε ^ 2 + p * ε * s + p * (p - 1) * s ^ 2 / 2)) := by
    have heq : 2 * (p * (p - 1) * ε ^ (p - 2)) *
        (ε ^ (p - 2) * (ε ^ 2 + p * ε * s + p * (p - 1) * s ^ 2 / 2)) -
        (p * (ε ^ (p - 2) * ε) + p * (p - 1) * ε ^ (p - 2) * s) ^ 2 =
        p * (p - 2) * (ε ^ (p - 2)) ^ 2 * ε ^ 2 := by ring
    linarith
  have hK : 0 ≤ p / (p - 1) := div_nonneg hp0.le hp1.le
  dsimp only
  rw [c5_power_energy_of_nonpos hε hN hs, c5_power_deriv_of_nonpos hε hN hs,
    PDE.Parabolic.LocalMax.deriv_deriv_powF hε hN]
  simp only [PDE.Parabolic.LocalMax.powF2, c5_power_cap_of_nonpos hN hs]
  rw [hpow1, hpow2]
  have henergy : 0 ≤ ε ^ (p - 2) * ε ^ 2 + p * (ε ^ (p - 2) * ε) * s +
      p * (p - 1) * ε ^ (p - 2) * s ^ 2 / 2 := by
    convert hF using 1; ring
  refine ⟨henergy, hcurv, ?_⟩
  have hbound' : (p * (ε ^ (p - 2) * ε) + p * (p - 1) * ε ^ (p - 2) * s) ^ 2 ≤
      2 * (p * (p - 1) * ε ^ (p - 2)) *
        (ε ^ (p - 2) * ε ^ 2 + p * (ε ^ (p - 2) * ε) * s +
          p * (p - 1) * ε ^ (p - 2) * s ^ 2 / 2) := by
    convert hbound using 1; ring
  nlinarith [mul_nonneg hK (mul_nonneg hcurv henergy)]

end
end EinsteinFull.Calculus
