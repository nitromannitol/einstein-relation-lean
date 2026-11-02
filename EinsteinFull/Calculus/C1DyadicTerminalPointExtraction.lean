import EinsteinFull.Calculus.C1DyadicActualMajorants
import EinsteinFull.Calculus.ScalarWeightSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c1_dyadic_point_decay_of_actual_majorant (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) : ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖*Real.sqrt (t : ℝ) ≤ 1 → ∀ growth K : ℝ, 0 ≤ growth → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (t : ℝ) ≤ K → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ (2*K*Real.exp growth) * (t : ℝ)^(-(1/2+(d : ℝ)/4)) := by
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hforce growth K hg hK
  have htpos : 0 < (t : ℝ) := by linarith
  have hsqrt : 1 ≤ Real.sqrt (t : ℝ) := by
    simpa using Real.sqrt_le_sqrt ht
  have hζ : ‖ζ‖ ≤ 2 := by
    have := norm_nonneg ζ
    nlinarith [mul_nonneg this (sub_nonneg.mpr hsqrt)]
  obtain ⟨C, hC, hb⟩ := c1_dyadic_named_point_majorant_bounds hlocal d hd D (t : ℝ) ht
  obtain ⟨hmajor, _, hpoint⟩ := hb Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hg
  have hKpos : 0 ≤ K := by linarith
  have hsquare : ‖ζ‖^2 * (t : ℝ) ≤ 1 := by
    have hs := Real.sq_sqrt htpos.le
    have hm : 0 ≤ ‖ζ‖ * Real.sqrt (t : ℝ) := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (1 - ‖ζ‖ * Real.sqrt (t : ℝ))]
  have hexp : Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) ≤ Real.exp growth := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hg (sub_nonneg.mpr hsquare)]
  have hw := scalar_decay_weight_le_of_force_bound d ‖ζ‖ (t : ℝ) 1 htpos hforce
  norm_num only [one_add_one_eq_two] at hw
  have hwpos : 0 ≤ (t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4) := by positivity
  have hp := hpoint t ht le_rfl
  have hweight : Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) ≤ Real.exp growth * (2 * (t : ℝ) ^ (-(1/2+(d : ℝ)/4))) := by
    calc
      _ ≤ Real.exp growth * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := mul_le_mul_of_nonneg_right hexp hwpos
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
  calc
    _ ≤ _ := hp
    _ ≤ K * (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ K * (Real.exp growth * (2 * (t : ℝ) ^ (-(1/2+(d : ℝ)/4)))) := mul_le_mul_of_nonneg_left hweight hKpos
    _ = _ := by ring

end EinsteinFull.Blueprint
