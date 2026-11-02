import EinsteinFull.Calculus.C15DyadicAverageMajorantFinite
import EinsteinFull.Calculus.C1DyadicActualMajorants

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c15_dyadic_uniform_initial_average_majorant (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (Tmax b : ℝ) (hTmax : 1 ≤ Tmax) (hb : 0 < b) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ growth T : ℝ, 0 ≤ growth → 1 ≤ T → T ≤ Tmax → dyadicAverageMajorant d hd D Q ν ζ P Pdag β a μ b growth (T) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := c15_dyadic_actual_average_majorant_finite hlocal d hd D Tmax b hTmax hb
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ growth T hg hT hTT
  obtain ⟨_, hbdd, _, hsup, _⟩ := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ growth hg
  unfold dyadicAverageMajorant
  apply max_le hC
  apply le_trans _ hsup
  apply csSup_le
  · exact ⟨_, ⟨1, b, hb, by norm_num, by simpa using hT, by simp, rfl⟩⟩
  · intro z hz
    apply le_csSup hbdd
    obtain ⟨t, s, hs, ht, htT, hbs, hz⟩ := hz
    exact ⟨t, s, hs, ht, le_trans htT hTT, hbs, hz⟩

end EinsteinFull.Blueprint
