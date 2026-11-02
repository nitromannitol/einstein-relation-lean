import EinsteinFull.Calculus.C3DyadicAverageMajorantBounds
import EinsteinFull.Calculus.C7DyadicPointImprovement

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint

theorem c4_dyadic_point_majorant_recurrence (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (bmax : ℝ) (hbmax : 0 < bmax) : ∃ b Ca : ℝ, 0 < b ∧ b ≤ min bmax (1/16) ∧ 0 ≤ Ca ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ growth T : ℝ, 0 ≤ growth → 8 ≤ T → ‖ζ‖ * Real.sqrt (2*T) ≤ 1 → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (2*T) ≤ max (dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (T)) (Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*T) + dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (T)/2) := by
  obtain ⟨b, Ca, hb, hbsmall, hCa, himprove⟩ :=
    c7_dyadic_point_improvement hlocal d hd D bmax hbmax
  refine ⟨b, Ca, hb, hbsmall, hCa, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν growth T hgrowth hT hforce
  have hT1 : 1 ≤ T := by linarith
  have h2T1 : 1 ≤ 2*T := by linarith
  have hsqrt : 1 ≤ Real.sqrt (2*T) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2*T by linarith)
    simpa using this
  have hz : ‖ζ‖ ≤ 2 := by nlinarith [norm_nonneg ζ]
  obtain ⟨_, _, hpoint⟩ := c1_dyadic_named_point_majorant_bounds hlocal d hd D T hT1
  obtain ⟨_, _, havg⟩ := c3_dyadic_named_average_majorant_bounds hlocal d hd D (2*T) b h2T1 hb
  obtain ⟨hK, _, hKpoint⟩ := hpoint Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hz growth hgrowth
  obtain ⟨hA, _, hApoint⟩ := havg Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hz growth hgrowth
  let K := dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T
  let A := dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*T)
  change max 1 (sSup _) ≤ max K (Ca*A+K/2)
  apply max_le (le_trans hK (le_max_left _ _))
  apply csSup_le
  · exact ⟨_, ⟨1, by norm_num, by simpa using h2T1, rfl⟩⟩
  · rintro z ⟨t, ht, ht2, rfl⟩
    have htpos : 0 < (t : ℝ) := by linarith
    have hweight : 0 < Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) *
        ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by positivity
    apply (div_le_iff₀ hweight).2
    by_cases htT : (t : ℝ) ≤ T
    · exact (hKpoint t ht htT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hweight.le)
    · have ht8 : 1 ≤ ((t/8 : ℝ≥0) : ℝ) := by simp; linarith
      have ht8T : ((t/8 : ℝ≥0) : ℝ) ≤ T := by simp; linarith
      have hzt : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 := by
        have hs := Real.sqrt_le_sqrt ht2
        nlinarith [mul_le_mul_of_nonneg_left hs (norm_nonneg ζ)]
      have hbt : 0 < b*(t : ℝ) := mul_pos hb htpos
      have hsmall := hKpoint (t/8) ht8 ht8T
      have haverage := hApoint t ht ht2 (b*(t : ℝ)) le_rfl hbt
      have hnew := himprove Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hzt growth K A hgrowth (by linarith) (by linarith) (by simpa [K, mul_assoc] using hsmall) hbt (by simpa [A, mul_assoc] using haverage)
      exact (by simpa [mul_assoc] using hnew : _ ≤ (Ca*A+K/2) * _).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hweight.le)

end EinsteinFull.Blueprint
