import EinsteinFull.Calculus.C19DyadicBootstrapClosure
import EinsteinFull.Calculus.C1DyadicTerminalPointExtraction

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

theorem c4_dyadic_transpose_endpoint_decay (hlocal : node_l_u3A_forced_u2D_localStmt) : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖*Real.sqrt (t : ℝ) ≤ 1 → ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ≤ A*(t : ℝ)^(-(1/2+(d : ℝ)/4)) := by
  intro d hd D
  obtain ⟨b, growth, C, hb, hbmax, hgrowth, hC, hmajor⟩ :=
    c19_dyadic_uniform_majorants hlocal d hd D
  have hexp : 1 ≤ Real.exp growth := by
    simpa using Real.add_one_le_exp growth |>.trans' (by linarith : (1 : ℝ) ≤ growth + 1)
  refine ⟨2*C*Real.exp growth, ?_, ?_⟩
  · nlinarith [mul_nonneg (show 0 ≤ C-1 by linarith) (show 0 ≤ Real.exp growth-1 by linarith)]
  · intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hforce
    have hm := (hmajor Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag (Sum.inr true) t ht hforce).1
    have hp := c1_dyadic_point_decay_of_actual_majorant hlocal d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag (Sum.inr true) t ht hforce growth C (le_of_lt hgrowth) hm
    simpa only [indexedEndpoint] using hp

end EinsteinFull.Blueprint
