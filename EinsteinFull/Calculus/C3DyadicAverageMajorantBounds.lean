import EinsteinFull.Calculus.C1DyadicActualMajorants
import EinsteinFull.Calculus.C15DyadicAverageMajorantFinite

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c3_dyadic_named_average_majorant_bounds (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T b : ℝ) (hT : 1 ≤ T) (hb : 0 < b) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ growth : ℝ, 0 ≤ growth → 1 ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) ∧ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) ≤ C ∧ ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ∀ s : ℝ, b*(t : ℝ) ≤ s → ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) * (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4))) := by
  obtain ⟨C, hC, hbound⟩ := c15_dyadic_actual_average_majorant_finite hlocal d hd D T b hT hb
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  obtain ⟨_, _, _, hsup, havg⟩ := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  refine ⟨le_max_left _ _, max_le hC hsup, ?_⟩
  intro t ht htT s hbs hs
  exact (havg t ht htT s hbs hs).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end EinsteinFull.Blueprint
