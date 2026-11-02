import EinsteinFull.Calculus.C1DyadicActualMajorants

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c7_dyadic_uniform_initial_invariant (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (Tmax lowerCa : ℝ) (hTmax : 1 ≤ Tmax) : ∃ Ca : ℝ, 1 ≤ Ca ∧ lowerCa ≤ Ca ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ b growth T : ℝ, 0 ≤ growth → 1 ≤ T → T ≤ Tmax → dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth (T) ≤ 2*Ca*dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) := by
  obtain ⟨C, hC, hbound⟩ := c1_dyadic_actual_point_majorant_finite hlocal d hd D Tmax hTmax
  refine ⟨max C lowerCa, le_trans hC (le_max_left _ _), le_max_right _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ b growth T hg hT hTT
  obtain ⟨_, hbounded, _, hsup, _⟩ := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hg
  have hmono : dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T ≤
      dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth Tmax := by
    unfold dyadicPointMajorant
    apply max_le_max_left
    apply csSup_le_csSup hbounded
    · exact ⟨_, ⟨1, by norm_num, by simpa using hT, rfl⟩⟩
    · rintro z ⟨t, ht, htT, rfl⟩
      exact ⟨t, ht, le_trans htT hTT, rfl⟩
  have hp : dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth Tmax ≤ C := by
    unfold dyadicPointMajorant
    exact max_le hC hsup
  have ha1 : 1 ≤ dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth T := le_max_left _ _
  have hc : 0 ≤ max C lowerCa := by linarith [le_max_left C lowerCa]
  have hm := mul_le_mul_of_nonneg_left ha1 hc
  linarith [le_max_left C lowerCa]

end EinsteinFull.Blueprint
