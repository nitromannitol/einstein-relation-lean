import EinsteinFull.Calculus.S2SmoothingForced
import EinsteinFull.Frozen.FluxIndex

/-!
# The flux homogeneous propagator against the averaging seminorm

`forcedFluxE` is the literal expression `E` of the force-replacement statement: half the sum of
the first derivative averages with the signed force, plus `ζ` times the homogeneous average of
the first component for velocity indices. It is bounded, after the factor `ρ^{d/2}` with
`ρ² = ε s / 4`, by `exp (K ‖ζ‖² s)` times the seminorm bound of the datum.
-/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- The propagator `E` of `p:endpoint-comparison#force-replacement`. -/
noncomputable def forcedFluxE (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (ν : FluxIndex d) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℂ) • (∑ j : Fin d, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs
      (ν.elim (fun _ => ζ) (fun _ => -ζ)) 1 (fun _ => j) (F j)) +
    ν.elim (fun _ => ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩))
      (fun _ => 0)

theorem norm_half_complex : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [norm_div, norm_one, Complex.norm_two]

theorem norm_forcedFluxE_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {s : ℝ} (hs : 0 < s)
    (hεs : 2 ≤ deconvEps Λ₀ * (s / 2)) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hsem : gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C) (ζ : ℂ)
    (ν : FluxIndex d) :
    Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖forcedFluxE hd Q s hs ζ ν F‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
        ((d : ℝ) / 2 * (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2)) + ‖ζ‖) *
          C := by
  have hρ : 0 ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hD : ∀ ξ : ℂ, ‖ξ‖ = ‖ζ‖ → ∀ j : Fin d,
      Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1 (fun _ => j) (F j)‖ ≤
      Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
        (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C) := by
    intro ξ hξ j
    have h := forced_derivative_le hd Q hs hεs F hC hsem ξ j j
    rwa [hξ] at h
  have hdnn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmain : ∀ ξ : ℂ, ‖ξ‖ = ‖ζ‖ →
      Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
        ‖(1 / 2 : ℂ) • ∑ j : Fin d, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1
          (fun _ => j) (F j)‖ ≤
      (d : ℝ) / 2 * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
        (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C)) := by
    intro ξ hξ
    calc _ = Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          (1 / 2 * ‖∑ j : Fin d, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1
            (fun _ => j) (F j)‖) := by rw [norm_smul, norm_half_complex]
      _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          (1 / 2 * ∑ j : Fin d, ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1
            (fun _ => j) (F j)‖) := by
        gcongr
        exact norm_sum_le _ _
      _ = 1 / 2 * ∑ j : Fin d, (Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ξ 1 (fun _ => j) (F j)‖) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 1 / 2 * ∑ _j : Fin d, (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
          (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C)) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hD ξ hξ j)
          (by norm_num)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  rcases ν with i | u
  · have h1 := hmain ζ rfl
    have h2 := forced_average_le hd Q hs hεs F hC hsem ζ ⟨0, by omega⟩
    unfold forcedFluxE
    simp only [Sum.elim_inl]
    calc _ ≤ Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
          (‖(1 / 2 : ℂ) • ∑ j : Fin d, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ 1
            (fun _ => j) (F j)‖ +
            ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hρ
      _ = Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
            ‖(1 / 2 : ℂ) • ∑ j : Fin d, homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ 1
              (fun _ => j) (F j)‖ +
          ‖ζ‖ * (Real.sqrt (deconvEps Λ₀ * (s / 2) / 2) ^ ((d : ℝ) / 2) *
            ‖homogeneousAverage Q ⟨0, by omega⟩ s hs ζ (F ⟨0, by omega⟩)‖) := by
        simp only [norm_smul]
        ring
      _ ≤ (d : ℝ) / 2 * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
            (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C)) +
          ‖ζ‖ * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) * C) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = _ := by ring
  · have h1 := hmain (-ζ) (norm_neg ζ)
    unfold forcedFluxE
    simp only [Sum.elim_inr, norm_zero, add_zero]
    calc _ ≤ (d : ℝ) / 2 * (Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
            (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2) * C)) := by
          exact h1
      _ ≤ _ := by
          have hnn : 0 ≤ Real.exp (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s) *
              (Real.sqrt (2 * sourceReducedBound Λ₀ * (s / 2)) / (s / 2)) * C := by
            have := hC
            positivity
          nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos
            (sourceReducedBound Λ₀ * ‖ζ‖ ^ 2 * s)).le (norm_nonneg ζ)) hC]

end EinsteinFull
