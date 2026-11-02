import EinsteinFull.Calculus.C10DyadicActualHalfStep

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

theorem c10_dyadic_weighted_average_step (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t))
    (s : ℝ) (hs : 0 < s) (t T growth ε K Kp E : ℝ) (hT : 0 < T) (hTt : T ≤ t) (hg : 0 ≤ growth) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hKp : 0 ≤ Kp) (hE : 0 ≤ E) (hcoef : |homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩| ≤ growth) (hinit : ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ (t/2).toNNReal)‖ ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t/2)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4))) (hfluxbound : ∀ r ∈ Set.Ioo (t/2) t, ‖c3BootstrapFluxVector hd Q ν ζ J s hs t r‖ ≤ E * Kp * Real.exp (growth * ‖ζ‖ ^ 2 * t) * (t/2) ^ (-1-ε) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4))) : ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal)‖ ≤ (K + 2 ^ ε * E * T ^ (-ε) * Kp) * Real.exp (growth * ‖ζ‖ ^ 2 * t) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4)) := by
  let w : ℝ := s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)
  let g : ℝ := growth * ‖ζ‖ ^ 2
  let A : ℝ := ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 *
    homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2
  have ht : 0 < t := hT.trans_le hTt
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hsign : ‖(endpointDriftSign ν : ℂ) * ζ‖ = ‖ζ‖ := by
    rcases ν with j | v
    · simp only [endpointDriftSign, Complex.ofReal_one, one_mul]
    · cases v <;> simp only [endpointDriftSign, Complex.ofReal_one, one_mul,
        Complex.ofReal_neg, neg_mul, norm_neg]
  have him : ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 ≤ ‖ζ‖ ^ 2 := by
    rw [← hsign]
    nlinarith only [Complex.sq_norm_sub_sq_im ((endpointDriftSign ν : ℂ) * ζ),
      sq_nonneg (((endpointDriftSign ν : ℂ) * ζ).re)]
  have hAg : A ≤ g := by
    dsimp [A, g]
    have h1 := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hcoef)
      (sq_nonneg (((endpointDriftSign ν : ℂ) * ζ).im))
    have h2 := mul_le_mul_of_nonneg_left him hg
    nlinarith only [h1, h2, mul_nonneg hg (sq_nonneg ‖ζ‖)]
  have hh := c10_dyadic_actual_half_step hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux s hs t ht
    (K * Real.exp (g * (t/2)) * w)
    (E * Kp * Real.exp (g * t) * (t/2) ^ (-1-ε) * w)
    (by positivity) (by simpa [g, w] using hinit) (by simpa [g, w] using hfluxbound)
  have hhom := c3Bootstrap_homogeneous_weight A g t K w hAg ht.le hK hw
  have herr := c3Bootstrap_half_error_le t T ε Kp E 0 1 w 0 0 hT hTt hε hKp hE
    (by norm_num) (by norm_num) hw (by norm_num) (by norm_num)
  have herr' : (t/2) * (E * Kp * Real.exp (g*t) * (t/2)^(-1-ε) * w) ≤
      (2^ε * E * T^(-ε) * Kp) * Real.exp (g*t) * w := by
    simp only [zero_mul, one_mul, add_zero] at herr
    have h := mul_le_mul_of_nonneg_left herr (Real.exp_pos (g*t)).le
    nlinarith only [h]
  have hresult := add_le_add hhom herr'
  have heq : ((endpointDriftSign ν : ℂ) * ζ).im ^ 2 * (t / 2) *
      homogenizedCoefficient Q ⟨0, by omega⟩ ⟨0, by omega⟩ / 2 = A * (t/2) := by
    dsimp [A]; ring
  rw [heq] at hh
  calc
    _ ≤ _ := hh
    _ ≤ _ := hresult
    _ = _ := by dsimp [g, w]; ring

end EinsteinFull.Blueprint
