import EinsteinFull.Calculus.C5TubeSignedPowerEnergy
import EinsteinFull.Calculus.C11TubeWeightedLocalMax

namespace EinsteinFull.Calculus

noncomputable section

/-- The canonical truncated power energy has the structural inequalities on all of ℝ. -/
theorem c5_all_real_truncated_power_structure {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    let F := PDE.Parabolic.LocalMax.powF p ε (n : ℝ)
    0 ≤ F s ∧ 0 ≤ deriv (deriv F) s ∧
      (deriv F s)^2 ≤ (2+p/(p-1)) * deriv (deriv F) s * F s := by
  by_cases hs : s ≤ 0
  · exact c5_power_energy_structure_of_nonpos hp hε (Nat.cast_nonneg n) hs
  · have h := c11_truncated_power_energy_structure (by linarith : 1 < p) hε n s (le_of_not_ge hs)
    exact ⟨h.1, h.2.1, h.2.2.1⟩

end
end EinsteinFull.Calculus
