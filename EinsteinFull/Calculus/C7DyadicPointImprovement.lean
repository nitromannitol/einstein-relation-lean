import EinsteinFull.Calculus.C19DyadicForceScaleAveraging

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
namespace EinsteinFull.Blueprint

theorem c7_dyadic_point_improvement (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (bmax : ℝ) (hbmax : 0 < bmax) : ∃ b Ca : ℝ, 0 < b ∧ b ≤ min bmax (1/16) ∧ 0 ≤ Ca ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ∀ growth K A : ℝ, 0 ≤ growth → 0 ≤ K → 0 ≤ A → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8)‖ ≤ K * Real.exp (growth*‖ζ‖^2*((t : ℝ)/8)) * (((t : ℝ)/8) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * ((t : ℝ)/8) ^ (-(d : ℝ)/4)) → ∀ hbt : 0 < b*(t : ℝ), ‖gaussianAverage hd Q (b*(t : ℝ)) hbt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((b*(t : ℝ)) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (b*(t : ℝ)) ^ (-(d : ℝ)/4)) → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ (Ca*A+K/2) * Real.exp (growth*‖ζ‖^2*(t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)) := by
  obtain ⟨b, hb, hbsmall, hrec⟩ :=
    c19_dyadic_adjustable_point_majorant_recovery hlocal d hd D bmax hbmax
  refine ⟨b, b ^ (-(1/2+(d : ℝ)/4)), hb, hbsmall, (Real.rpow_pos_of_pos hb _).le, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K A hgrowth hK hA hU hbt hgauss
  apply hrec Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hz growth K
    (b ^ (-(1/2+(d : ℝ)/4)) * A) hgrowth hK
    (mul_nonneg (Real.rpow_pos_of_pos hb _).le hA) hU hbt
  have htpos : 0 < (t : ℝ) := by linarith
  have hb1 : b ≤ 1 := by have := hbsmall.trans (min_le_right bmax (1/16)); linarith
  have hw := scalar_decay_weight_mul_le b (t : ℝ) ‖ζ‖ (1/2+(d : ℝ)/4)
    ((d : ℝ)/4) hb hb1 htpos (norm_nonneg _) (by linarith)
  rw [← neg_div] at hw
  calc
    _ ≤ A * Real.exp (growth*‖ζ‖^2*(t : ℝ)) *
        (b ^ (-(1/2+(d : ℝ)/4)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))) :=
      hgauss.trans (mul_le_mul_of_nonneg_left hw (mul_nonneg hA (Real.exp_pos _).le))
    _ = _ := by ring

end EinsteinFull.Blueprint
