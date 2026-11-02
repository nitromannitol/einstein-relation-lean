import EinsteinFull.Calculus.C3DyadicAverageMajorantBounds
import EinsteinFull.Calculus.C14DyadicActualAverageImprovement

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c2_dyadic_average_majorant_recurrence (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (b : ℝ) (hb : 0 < b) : ∃ ε growth₀ T₀ E : ℝ, 0 < ε ∧ 0 < growth₀ ∧ 8 ≤ T₀ ∧ 0 ≤ E ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ growth T : ℝ, growth₀ ≤ growth → T₀ ≤ T → ‖ζ‖ * Real.sqrt (2*T) ≤ 1 → dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (2*T) ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) + E*T^(-ε)*dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (T) := by
  obtain ⟨ε, growth₀, T₀, E, hε, hg₀, hT₀, hE, himprove⟩ :=
    c14_dyadic_actual_average_improvement hlocal d hd D b hb
  refine ⟨ε, growth₀, T₀, E, hε, hg₀, hT₀, hE, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν growth T hg hT hforce
  have hTone : 1 ≤ T := by linarith
  have hgrowth : 0 ≤ growth := le_trans (le_of_lt hg₀) hg
  have hsqrt : 1 ≤ Real.sqrt (2*T) := by
    have h := Real.sq_sqrt (show 0 ≤ 2*T by linarith)
    have hn := Real.sqrt_nonneg (2*T)
    nlinarith
  have hζ : ‖ζ‖ ≤ 2 := by nlinarith [norm_nonneg ζ]
  obtain ⟨C, hC, hpoint⟩ := c1_dyadic_named_point_majorant_bounds hlocal d hd D T hTone
  obtain ⟨C', hC', havg⟩ := c3_dyadic_named_average_majorant_bounds hlocal d hd D T b hTone hb
  obtain ⟨hKp, _, hpoint⟩ := hpoint Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  obtain ⟨hK, _, havg⟩ := havg Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  have herr : 0 ≤ E*T^(-ε)*dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T := by positivity
  conv_lhs => unfold dyadicAverageMajorant
  apply max_le
  · linarith [hK]
  · apply csSup_le
    · refine ⟨_, ⟨1, b, hb, by norm_num, ?_, by simp, rfl⟩⟩
      simpa using (show (1 : ℝ) ≤ 2*T by linarith)
    · rintro z ⟨t, s, hs, ht, ht2, hbs, rfl⟩
      have hden : 0 < Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := by positivity
      apply (div_le_iff₀ hden).2
      by_cases htT : (t : ℝ) ≤ T
      · have h := havg t ht htT s hbs hs
        exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hden.le)
      · have htT' : T ≤ (t : ℝ) := le_of_not_ge htT
        have htpos : 0 ≤ (t : ℝ) := t.coe_nonneg
        have htforce : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 :=
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht2) (norm_nonneg ζ)).trans hforce
        have hhalf : 1 ≤ (((t : ℝ)/2).toNNReal : ℝ) := by
          rw [Real.coe_toNNReal _ (by positivity)]
          linarith
        have hhalfT : (((t : ℝ)/2).toNNReal : ℝ) ≤ T := by
          rw [Real.coe_toNNReal _ (by positivity)]
          linarith
        have hbs' : b * (((t : ℝ)/2).toNNReal : ℝ) ≤ s := by
          rw [Real.coe_toNNReal _ (by positivity)]
          nlinarith
        have hinit := havg ((t : ℝ)/2).toNNReal hhalf hhalfT s hbs' hs
        have himp := himprove Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν T t growth _ _ hT htT' ht2 htforce hg hK hKp hpoint s hbs hs (by
          simpa [Real.coe_toNNReal _ (show 0 ≤ (t : ℝ)/2 by positivity), mul_assoc] using hinit)
        simpa [Real.toNNReal_coe, mul_assoc] using himp

end EinsteinFull.Blueprint
