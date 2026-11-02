import EinsteinFull.Calculus.C2DyadicUniformDensityConsumer
import EinsteinFull.Calculus.C1DyadicPointInitialization
import EinsteinFull.Calculus.C19FirstUnitGradientProjection

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint

/-- The unit force window suffices for the dyadic density increment. -/
theorem c2_dyadic_density_from_unit_window_endpoint (hlocal : node_l_u3A_forced_u2D_localStmt) (hendpoint : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 → ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ≤ A * (t : ℝ) ^ (-(1/2+(d : ℝ)/4))) : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
      ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 →
    let := reducedLaw_probability Q
    ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) - Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ ≤
      C * (s : ℝ) ^ (-(d : ℝ) / 4) := by
  apply c2_dyadic_density_of_uniform_endpoint_decay
  intro d hd D
  obtain ⟨A, hA, hunit⟩ := hendpoint d hd D
  obtain ⟨B, hB, hshort⟩ := c1_dyadic_bounded_time_point_decay
    (c19_dyadic_locality_input_of_forced_local hlocal) d hd D 4 (by norm_num)
  let α : ℝ := 1 / 2 + (d : ℝ) / 4
  let E : ℝ := Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
    ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2)
  let C : ℝ := max B (E * E * A * 4 ^ α)
  refine ⟨C, le_trans hB (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd t ht hz
  have htpos : 0 < (t : ℝ) := by linarith
  have hζ : ‖ζ‖ ≤ 2 := by
    have hs : 1 ≤ Real.sqrt (t : ℝ) := by
      simpa using Real.sqrt_le_sqrt ht
    nlinarith [norm_nonneg ζ]
  by_cases hsmall : (t : ℝ) ≤ 4
  · have hb := hshort Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd (.inr true) hζ t ht hsmall
    change ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ≤ B * (t : ℝ) ^ (-α) at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left B _) (Real.rpow_nonneg t.coe_nonneg _))
  · let s : ℝ≥0 := t / 4
    let v : ℝ≥0 := t / 2
    have hs : (s : ℝ) = (t : ℝ) / 4 := by simp [s]
    have hv : (v : ℝ) = (t : ℝ) / 2 := by simp [v]
    have hsone : 1 ≤ (s : ℝ) := by rw [hs]; linarith
    have hsv : s ≤ v := by exact_mod_cast (show (s : ℝ) ≤ (v : ℝ) by rw [hs, hv]; linarith)
    have hvs : v ≤ 2 * s := by exact_mod_cast (show (v : ℝ) ≤ (2 * s : ℝ≥0) by simp only [NNReal.coe_mul, NNReal.coe_ofNat, hs, hv]; linarith)
    have hvt : v ≤ t := by exact_mod_cast (show (v : ℝ) ≤ (t : ℝ) by rw [hv]; linarith)
    have htv : t ≤ 2 * v := by exact_mod_cast (show (t : ℝ) ≤ (2 * v : ℝ≥0) by simp only [NNReal.coe_mul, NNReal.coe_ofNat, hv]; linarith)
    have hsqr : Real.sqrt (t : ℝ) = 2 * Real.sqrt (s : ℝ) := by
      rw [hs, Real.sqrt_div (le_of_lt htpos)]
      norm_num
      ring
    have hunitforce : ‖ζ‖ * Real.sqrt (s : ℝ) ≤ 1 := by nlinarith [norm_nonneg ζ, Real.sqrt_nonneg (s : ℝ)]
    have hforce1 : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 := by
      exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by rw [hs]; linarith)) (norm_nonneg ζ)).trans hz
    have hforce2 : ‖ζ‖ * Real.sqrt (2 * (v : ℝ)) ≤ 2 := by
      rw [show 2 * (v : ℝ) = (t : ℝ) by rw [hv]; ring]
      exact hz
    have hp1 := c2_transpose_endpoint_propagation_window hP hPd β s v (by linarith) hsv hvs hforce1
    have hp2 := c2_transpose_endpoint_propagation_window hP hPd β v t (by rw [hv]; linarith) hvt htv hforce2
    have he : 0 ≤ E := le_of_lt (Real.exp_pos _)
    have hdec := hunit Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd s hsone hunitforce
    have hpow : (s : ℝ) ^ (-α) = 4 ^ α * (t : ℝ) ^ (-α) := by
      rw [hs, Real.div_rpow (by positivity : 0 ≤ (t : ℝ)) (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      ring_nf
      simp only [inv_inv]
    calc
      ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ≤ E * ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β v‖ := hp2
      _ ≤ E * (E * ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β s‖) := mul_le_mul_of_nonneg_left hp1 he
      _ ≤ E * (E * (A * (s : ℝ) ^ (-α))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdec he) he
      _ = (E * E * A * 4 ^ α) * (t : ℝ) ^ (-α) := by rw [hpow]; ring
      _ ≤ C * (t : ℝ) ^ (-α) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg t.coe_nonneg _)

end EinsteinFull.Blueprint
