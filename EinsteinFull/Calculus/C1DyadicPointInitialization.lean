import EinsteinFull.Calculus.C7UnitInitializationSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

 theorem c1_dyadic_bounded_time_point_decay (hlocal : node_e_u3A_forced_u2D_localityStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 1 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ C * (t : ℝ) ^ (-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C, hC, hbound⟩ := UnitInitialization.point_bound hlocal d hd D T (by linarith)
  let α : ℝ := 1 / 2 + (d : ℝ) / 4
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hpow : 1 ≤ T ^ α := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hα
  refine ⟨C * T ^ α, by nlinarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht htT
  have hb := (hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t htT 2).2
  rw [← Lp.norm_def] at hb
  have hmono : T ^ (-α) ≤ (t : ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) htT (by linarith)
  have hpos : 0 < T ^ α := Real.rpow_pos_of_pos (by linarith) _
  have hcancel : T ^ α * T ^ (-α) = 1 := by
    rw [Real.rpow_neg (by linarith : 0 ≤ T), mul_inv_cancel₀ (ne_of_gt hpos)]
  calc
    ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ C := hb
    _ = (C * T ^ α) * T ^ (-α) := by rw [mul_assoc, hcancel, mul_one]
    _ ≤ (C * T ^ α) * (t : ℝ) ^ (-α) :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg (by linarith) (le_of_lt hpos))

end EinsteinFull.Blueprint
