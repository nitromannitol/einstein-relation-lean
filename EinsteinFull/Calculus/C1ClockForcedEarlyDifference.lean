import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
import EinsteinFull.Calculus.S2ClockEarlySupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
theorem clock_forced_early_difference
    : ∀ (havg : node_e_u3A_clock_u2D_averageStmt)
      (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      ∀ (T : ℝ) (τ : ℝ≥0) (ht : 0 < T - (τ : ℝ)),
        t₀ ≤ (τ : ℝ) → 5 * (τ : ℝ) ≤ T →
      ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (τ : ℝ) ≤ 1 →
        ‖ζ • homogeneousAverage Q ⟨0, by omega⟩ (T - (τ : ℝ)) ht ζ
          (centeredComplexLp Q (P ζ τ μ) - centeredComplexLp Q (P 0 τ μ))‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1/2 + (d : ℝ)/4)) *
          Real.sqrt ((τ : ℝ)/T) := by
  intro havg d hd D
  obtain ⟨ε, Cc, t₀, _hε, hCc, ht₀, havg⟩ := havg d hd D
  let C := max (Cc * (4 : ℝ) ^ ((d : ℝ) / 4)) (|sourceReducedBound D.ellipticity| + 2)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hpref : Cc * (4 : ℝ) ^ ((d : ℝ) / 4) ≤ C := le_max_left _ _
  have hexpC : sourceReducedBound D.ellipticity + 1 ≤ C := by
    calc
      sourceReducedBound D.ellipticity + 1 ≤ |sourceReducedBound D.ellipticity| + 2 := by
        linarith [le_abs_self (sourceReducedBound D.ellipticity)]
      _ ≤ C := le_max_right _ _
  refine ⟨C, t₀, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP T τ ht hτ hτT ζ hζ
  obtain ⟨G, J, _hflux, havg⟩ := havg Q hQ a μ ha hμ P hP
  have hτ0 : 0 ≤ (τ : ℝ) := τ.property
  have hT : 0 < T := by linarith
  have hhalf : (τ : ℝ) ≤ T / 2 := by linarith
  have hscale : 2 * (τ : ℝ) ≤ (T - (τ : ℝ)) / 2 := by linarith
  have hg := ((havg τ hτ ((T - (τ : ℝ)) / 2) (half_pos ht) hscale).1 ζ hζ).2.2
  have hbound := EinsteinFull.clock_forced_difference_le hd Q hT hτ0 hhalf ht hCc.le
    (centeredComplexLp Q (P ζ τ μ) - centeredComplexLp Q (P 0 τ μ)) ζ hg
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
  apply mul_le_mul hpref _ (Real.exp_pos _).le hC.le
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexpC (sq_nonneg ‖ζ‖)) hT.le)
end EinsteinFull.Blueprint
