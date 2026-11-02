import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Calculus.C1ClockBackwardVariation
import EinsteinFull.Calculus.C8InitialDriftGaussianDecay
import EinsteinFull.Calculus.C7GaussianDerivativeApproximants
import EinsteinFull.Calculus.C7UnforcedCoefficientProductApproximants
import EinsteinFull.Calculus.C6UnforcedDriftProductApproximants
import EinsteinFull.Calculus.C4GaussianCoefficientRowWeakProduct
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.UnitInitialization

private instance probability {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

/-- The actual drift has zero reduced-law mean, by its weak divergence formula. -/
theorem c8_integral_drift_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : (∫ ω, β j ω ∂reducedLaw Q) = 0 := by
  have h := hβ.integral_mul j (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β j ω * Lp.const 2 (reducedLaw Q) (1 : ℂ) ω ∂reducedLaw Q) =
      ∫ ω, β j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k : Fin d, (ω.1 0 k j : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  rw [hl, hr, mul_zero] at h
  exact h

/-- At zero force the forward drift orbit is already centered. -/
theorem c8_centered_unforced_drift {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (t : ℝ≥0) (j : Fin d) :
    centeredComplexLp Q (P t (β j)) = P t (β j) := by
  have hforward : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 Pdag := by
    refine ⟨hPdag.zero hP, hPdag.add hP, hPdag.continuous_apply hP, ?_⟩
    intro f g
    exact (hPdag.tendsto_slope_iff hP f g).trans
      (isComplexTransposeGeneratorPair_zero_iff Q ⟨0, by omega⟩ f g)
  have he : Pdag = P := hforward.unique hP
  have hm := hPdag.integral_eq hP t (β j)
  rw [he, c8_integral_drift_zero hβ j] at hm
  change P t (β j) - Lp.const 2 (reducedLaw Q) _ = _
  rw [hm, map_zero, sub_zero]

/-- The required drift decay at scales at most one follows from the uniform
point estimate and contraction of the actual Gaussian average. -/
theorem c8_unforced_drift_gaussian_decay_small_scale
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ (j : Fin d) (s : ℝ) (hs : 0 < s), s ≤ 1 →
      ‖gaussianAverage hd Q s hs (P t (β j))‖ ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C, hC, hb⟩ := point_bound hlocal d hd D T hT
  refine ⟨C, lt_of_lt_of_le zero_lt_one hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht j s hs hs1
  have h := (hb Q hQ β a μ hβ ha hμ 0 P Pdag hP hPdag (.inl j)
    (by norm_num) t ht 2).2
  simp only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero,
    c8_centered_unforced_drift hd hβ hP hPdag] at h
  change (eLpNorm (P t (β j)) 2 (reducedLaw Q)).toReal ≤ C at h
  rw [← Lp.norm_def] at h
  have hc : ‖gaussianAverage hd Q s hs (P t (β j))‖ ≤ ‖P t (β j)‖ := by
    simpa only [homogeneousAverage, gaussianAverage, Complex.zero_im,
      zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div, Real.exp_zero, one_mul] using
      norm_homogeneousAverage_le Q ⟨0, by omega⟩ s hs 0 (P t (β j))
  have hpow : 1 ≤ s ^ (-(1/2+(d : ℝ)/4)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (neg_nonpos.mpr (by positivity))
  exact (hc.trans h).trans (le_mul_of_one_le_right (by linarith) hpow)

/-- At time zero the required decay is the actual initial drift estimate. -/
theorem c8_unforced_drift_gaussian_decay_zero_time
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ (j : Fin d) (s : ℝ) (hs : 0 < s),
      ‖gaussianAverage hd Q s hs (P 0 (β j))‖ ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C, hC, hb⟩ := initial_drift_gaussian_decay d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hQ β hβ P hP j s hs
  simpa only [hP.1, ContinuousLinearMap.id_apply] using hb Q hQ β hβ j s hs

/-- Both graph inputs give bounded centered local approximants for the actual
unforced drift orbit at every time of the prescribed horizon. -/
theorem c8_unforced_drift_local_approximants
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B R c : ℝ, 1 ≤ B ∧ 1 ≤ R ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ j : Fin d,
      (∀ᵐ ω ∂reducedLaw Q, ‖P 0 t (β j) ω‖ ≤ B) ∧
      ∀ ρ : ℝ, R ≤ ρ → ∃ K : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ K ∧ (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
        (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
        ‖P 0 t (β j) - K‖ ≤ 2 * R * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨B, hB, hbound⟩ := ae_point_bound_on_four hlocal d hd D T hT
  have hpacket := hends d hd D 2 (by norm_num) T 1 hT (by norm_num)
  obtain ⟨R, c, hR, hc, hp⟩ := hpacket
  refine ⟨B, R, c, hB, hR, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht j
  have hcenter := c8_centered_unforced_drift hd hβ (hP 0) (hPdag 0) t j
  have hU : indexedEndpoint hd Q (.inl j) 0 (P 0) (Pdag 0) β a μ t =
      P 0 t (β j) := by
    simp only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero, hcenter]
  have hUB := hbound Q hQ β a μ hβ ha hμ 0 (P 0) (Pdag 0)
    (hP 0) (hPdag 0) (.inl j) (by norm_num) t ht
  rw [hU] at hUB
  refine ⟨hUB, ?_⟩
  obtain ⟨E, H, he, _, _, _, _, happ⟩ :=
    hp Q hQ β a μ hβ ha hμ P Pdag hP hPdag (.inl j) t ht
  have hE : (E 0 : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P 0 t (β j) := by
    simpa only [hU] using he 0
  have hm : (∫ ω, P 0 t (β j) ω ∂reducedLaw Q) = 0 := by
    rw [← hcenter]
    exact integral_centeredComplexLp Q _
  intro ρ hρ
  obtain ⟨L, K, L₂, K₂, hLK, _, _, _, _, herror, _⟩ := happ ρ hρ
  have hnorm : ‖P 0 t (β j) - L₂ 0‖ = ‖E 0 - L 0‖ := by
    calc
      _ = (eLpNorm (fun ω => E 0 ω - L 0 ω) 2 (reducedLaw Q)).toReal := by
        rw [Lp.norm_def]
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_ae
        filter_upwards [Lp.coeFn_sub (P 0 t (β j)) (L₂ 0), hE, (hLK 0).1]
          with ω hsub hEω hLω
        simpa only [hsub, Pi.sub_apply, hEω, hLω]
      _ = (eLpNorm (fun ω => E 0 ω - L 0 ω) (ENNReal.ofReal 2)
          (reducedLaw Q)).toReal := congrArg
            (fun p => (eLpNorm (fun ω => E 0 ω - L 0 ω) p (reducedLaw Q)).toReal)
              (by norm_num : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ))
      _ = ‖E 0 - L 0‖ := by
        rw [Lp.norm_def]
        exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub (E 0) (L 0)).symm)
  have herr : ‖P 0 t (β j) - L₂ 0‖ ≤ R * Real.exp (-c * ρ ^ 2) :=
    hnorm.trans_le (herror 0 (by norm_num)).2.2
  obtain ⟨V, hV, hVm, hVB, hVe⟩ := exists_bounded_centered_local_projection_norm
    Q ρ (P 0 t (β j)) (L₂ 0) hUB hm (hLK 0).2.2.1 herr
  refine ⟨V, hV, hVm, hVB, ?_⟩
  simpa only [mul_assoc] using hVe

/-- Summing the genuine local approximants gives the full finite-range
averaging power for the actual drift orbit, uniformly down to time zero. -/
theorem c8_unforced_drift_gaussian_average_bound
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ (j : Fin d) (s : ℝ) (hs : 0 < s),
      ‖gaussianAverage hd Q s hs (P 0 t (β j))‖ ≤ C * s ^ (-(d : ℝ)/4) := by
  obtain ⟨B, R, c, hB, hR, hc, hb⟩ :=
    c8_unforced_drift_local_approximants hlocal hends d hd D T hT
  let : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hpacket := exists_gaussian_average_of_gaussian_norm_approximants
    d D.ellipticity D.dependenceRange R B (2 * R) c 2 (by linarith)
    (by linarith) (by linarith) hc (by norm_num)
  simp only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] at hpacket
  obtain ⟨C, hC, hbound⟩ := hpacket
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht j s hs
  obtain ⟨_, hloc⟩ := hb Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht j
  choose K hK using fun n : ℕ => hloc (R + n)
    (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have herr (n : ℕ) : ‖P 0 t (β j) - K n‖ ≤ 2 * R * Real.exp (-c * (n : ℝ) ^ 2) := by
    have hsq : (n : ℝ) ^ 2 ≤ (R + n) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hK n).2.2.2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (by linarith))) (by linarith))
  have h := hbound hd Q (Localization.finiteRange_map_reduce Q.measure Q.finiteRange)
    (P 0 t (β j)) K (fun n => (hK n).2.2.1) (fun n => (hK n).1)
    (fun n => (hK n).2.1) herr s hs
  simpa only [Lp.norm_def] using h.2

/-- A continuous-radius localization estimate supplies the first two actual
Gaussian derivative bounds, with the constant chosen before the environment. -/
theorem c8_local_approximants_derivative_bound
    (d : ℕ) (D : StructuralData d) (B R L c : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hL : 0 ≤ L) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (hd : 2 ≤ d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (H : Lp ℂ 2 (reducedLaw Q)),
      (∀ ρ : ℝ, R ≤ ρ → ∃ K : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ K ∧ (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
        (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
        ‖H-K‖ ≤ L * Real.exp (-c * ρ^2)) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ (dirs : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
      ‖gaussianDerivativeAverage hd Q s hs k dirs H‖ ≤
        C * s ^ (-((k : ℝ)/2 + (d : ℝ)/4)) := by
  obtain ⟨C, hC, hb⟩ := gaussian_derivative_of_local_approximants
    d D R B L c 2 hR hB hL hc (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro hd Q H hloc k hk₁ hk₂ dirs s hs
  choose K hK using fun n : ℕ => hloc (R + n)
    (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have herr (n : ℕ) : ‖H-K n‖ ≤ L * Real.exp (-c * (n : ℝ)^2) := by
    have hsq : (n : ℝ)^2 ≤ (R+n)^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hK n).2.2.2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (by linarith))) hL)
  have h := (hb hd Q H K (fun n => (hK n).2.2.1) (fun n => (hK n).1)
    (fun n => (hK n).2.1) herr k hk₁ hk₂ dirs s hs).2
  simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num, Lp.norm_def] using h

/-- The actual centered coefficient products along the drift orbit have the
first and second Gaussian derivative decay needed in the weak flux identity. -/
theorem c8_unforced_coefficient_product_derivative_bound
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ (m l j : Fin d) (k : ℕ), 1 ≤ k → k ≤ 2 →
    ∀ (dirs : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
      ‖gaussianDerivativeAverage hd Q s hs k dirs
          (centeredComplexLp Q (complexCoefficientMul Q l j (P 0 t (β m))))‖ ≤
        C * s ^ (-((k : ℝ)/2 + (d : ℝ)/4)) := by
  obtain ⟨B, R, L, c, hB, hR, hL, hc, hloc⟩ :=
    unforced_coefficient_product_local_approximants hlocal hends d hd D T hT
  obtain ⟨C, hC, hb⟩ := c8_local_approximants_derivative_bound
    d D B R L c (by linarith) (by linarith) hL.le hc
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l j k hk₁ hk₂ dirs s hs
  exact hb hd Q _ (hloc Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l j).2
    k hk₁ hk₂ dirs s hs

/-- Differentiating the first Gaussian average gives its literal two-direction
kernel derivative, retaining the order of the horizontal directions. -/
theorem c8_gaussian_first_derivative_has_derivative
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) (l k : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f)
      (gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k)) f) := by
  obtain ⟨g, hg, hg₂⟩ := UnforcedIdentification.homogeneousAverage_hasHorizontalJet_two
    Q ⟨0, by omega⟩ s hs 0 (Fin.cases l (fun _ => k)) f
  have hg₁ : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k
      (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 f)
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f) := by
    rw [c3GaussianDerivativeAverage_one_eq_gradient]
    exact homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 f k
  have he : g = gaussianDerivativeAverage hd Q s hs 1 (fun _ => k) f := by
    exact hg.unique hg₁
  rw [he] at hg₂
  simpa only [Fin.cases_zero, homogeneousDerivativeAverage, neg_zero,
    gaussianDerivativeAverage] using hg₂

/-- The second Gaussian derivative annihilates the subtracted mean exactly. -/
theorem c8_gaussian_second_derivative_centered
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) (l k : Fin d) :
    gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
        (centeredComplexLp Q f) =
      gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k)) f := by
  have h := c8_gaussian_first_derivative_has_derivative hd Q s hs (centeredComplexLp Q f) l k
  rw [gaussianDerivativeAverage_one_centered] at h
  exact h.unique (c8_gaussian_first_derivative_has_derivative hd Q s hs f l k)

/-- Differentiated coefficient-row integration by parts replaces the gradient
of the orbit by two kernel derivatives and the actual drift product. -/
theorem c8_gaussian_coefficient_row_derivative
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (u : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (l : Fin d) (H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * u ω)
    (s : ℝ) (hs : 0 < s) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) H =
      (∑ k : Fin d, gaussianDerivativeAverage hd Q s hs 2
        (Fin.cases j (fun _ => k)) (complexCoefficientMul Q l k u)) -
      (2 : ℂ) • gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) R := by
  classical
  have havg (f : Lp ℂ 2 (reducedLaw Q)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (gaussianAverage hd Q s hs f)
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f) := by
    rw [c3GaussianDerivativeAverage_one_eq_gradient]
    exact homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 f j
  have hsum (S : Finset (Fin d)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 1 (fun _ => k)
          (complexCoefficientMul Q l k u))
        (∑ k ∈ S, gaussianDerivativeAverage hd Q s hs 2
          (Fin.cases j (fun _ => k)) (complexCoefficientMul Q l k u)) := by
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) j
    | @insert k S hk ih =>
      simpa only [Finset.sum_insert hk] using
        (c8_gaussian_first_derivative_has_derivative hd Q s hs
          (complexCoefficientMul Q l k u) j k).add ih
  have hright := (hsum Finset.univ).add ((havg R).smul (-2 : ℂ))
  simp only [neg_smul, ← sub_eq_add_neg] at hright
  rw [← gaussian_coefficient_row_weak_product hd D Q hQ β hβ u G hG l H R hH hR s hs]
    at hright
  exact (havg H).unique hright

/-- The centered drift products have the same uniform first and second kernel
derivative bounds; the representative is tied to the literal physical product. -/
theorem c8_unforced_drift_product_derivative_bound
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ m l : Fin d,
      ∃ H : Lp ℂ 2 (reducedLaw Q),
        ((H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
          β l ω * P 0 t (β m) ω - ∫ η, β l η * P 0 t (β m) η ∂reducedLaw Q) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∀ (dirs : Fin k → Fin d) (s : ℝ) (hs : 0 < s),
          ‖gaussianDerivativeAverage hd Q s hs k dirs H‖ ≤
            C * s ^ (-((k : ℝ)/2 + (d : ℝ)/4)) := by
  obtain ⟨B, R, L, c, hB, hR, hL, hc, hloc⟩ :=
    unforced_drift_product_local_approximants hlocal hends d hd D T hT
  obtain ⟨C, hC, hb⟩ := c8_local_approximants_derivative_bound
    d D B R L c (by linarith) (by linarith) hL.le hc
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l
  obtain ⟨H, hH, _, hK⟩ := hloc Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l
  exact ⟨H, hH, hb hd Q H hK⟩

/-- A bounded operator commutes with the finite-time primitive, so a uniform
orbit estimate integrates with exactly the length of the prescribed interval. -/
theorem c8_norm_operator_orbit_integral_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (f : ℝ≥0 → E) (hf : Continuous f) (t : ℝ≥0) (M : ℝ)
    (hb : ∀ r : ℝ≥0, r ≤ t → ‖A (f r)‖ ≤ M) :
    ‖A (∫ r in Icc (0 : ℝ) (t : ℝ), f r.toNNReal)‖ ≤ M * (t : ℝ) := by
  rw [← A.integral_comp_comm (integrableOn_comp_toNNReal_Icc f hf (t : ℝ))]
  have h := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)))
    (fun r (hr : r ∈ Icc (0 : ℝ) (t : ℝ)) =>
      hb r.toNNReal (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
        exact hr.2))
  simpa using h

/-- The averaged orbit is its initial drift plus the differentiated integral
of its actual coefficient flux. -/
theorem c8_unforced_gaussian_flux_increment
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (t : ℝ≥0) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    gaussianAverage hd Q s hs (P t (β j)) = gaussianAverage hd Q s hs (β j) +
      (1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1 (fun _ => l)
        (∫ r in Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k)) := by
  have hzero := unforced_gaussian_centered_flux hd hP hβ ha 0 j s hs
  simp [hP.1, gaussianDerivativeAverage_one_centered] at hzero
  rw [unforced_gaussian_centered_flux hd hP hβ ha t j s hs]
  simp only [gaussianDerivativeAverage_one_centered]
  have hadd (l : Fin d) (f g : Lp ℂ 2 (reducedLaw Q)) :
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (f+g) =
        gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) f +
        gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) g := by
    simpa only [gaussianDerivativeAverageCLM_apply] using
      (gaussianDerivativeAverageCLM hd Q s hs 1 (fun _ => l)).map_add f g
  simp_rw [hadd]
  simp only [one_div] at hzero ⊢
  rw [Finset.sum_add_distrib, smul_add, ← hzero]

/-- Literal centered and uncentered product representatives have identical
first Gaussian derivatives. -/
theorem c8_gaussian_product_derivative_of_representatives
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f g H R : Lp ℂ 2 (reducedLaw Q))
    (hH : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      f ω * g ω - ∫ η, f η * g η ∂reducedLaw Q)
    (hR : (R : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => f ω * g ω)
    (s : ℝ) (hs : 0 < s) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) H =
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) R := by
  have he : H = centeredComplexLp Q R := by
    apply Lp.ext
    have hi := integral_congr_ae hR
    filter_upwards [hH, centeredComplexLp_ae Q R, hR] with ω hHω hcω hRω
    rw [hHω, hcω, hRω, hi]
  rw [he, gaussianDerivativeAverage_one_centered]

/-- Centering may be removed before integrating the second derivative of an
actual coefficient product along any continuous orbit. -/
theorem c8_coefficient_primitive_second_derivative_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : ℝ≥0 → Lp ℂ 2 (reducedLaw Q)) (hf : Continuous f) (t : ℝ≥0)
    (l k : Fin d) (s : ℝ) (hs : 0 < s) (M : ℝ)
    (hb : ∀ r : ℝ≥0, r ≤ t →
      ‖gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
        (centeredComplexLp Q (complexCoefficientMul Q l k (f r)))‖ ≤ M) :
    ‖gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
      (complexCoefficientMul Q l k (∫ r in Icc (0 : ℝ) (t : ℝ), f r.toNNReal))‖ ≤
        M * (t : ℝ) := by
  let A := (gaussianDerivativeAverageCLM hd Q s hs 2 (Fin.cases l (fun _ => k))).comp
    (complexCoefficientMul Q l k)
  have hbA (r : ℝ≥0) (hr : r ≤ t) : ‖A (f r)‖ ≤ M := by
    have he := congrArg norm (c8_gaussian_second_derivative_centered hd Q s hs
      (complexCoefficientMul Q l k (f r)) l k)
    have hraw := he.symm.trans_le (hb r hr)
    simpa only [A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using hraw
  simpa only [A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using
    c8_norm_operator_orbit_integral_le A f hf t M hbA

/-- Uniform Gaussian drift decay throughout the prescribed finite time horizon. -/
theorem unforced_drift_gaussian_decay
    : ∀ (hlocal : node_e_u3A_forced_u2D_localityStmt)
        (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
        (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ), 0 ≤ T →
      ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
        (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (i : Fin d) (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs (P 0 t (β i))‖ ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
  intro hlocal hends d hd D T hT
  obtain ⟨Cs, hCs, hsmall⟩ := c8_unforced_drift_gaussian_decay_small_scale hlocal d hd D T hT
  obtain ⟨Ci, hCi, hinit⟩ := initial_drift_gaussian_decay d hd D
  obtain ⟨Cc, hCc, hcoef⟩ :=
    c8_unforced_coefficient_product_derivative_bound hlocal hends d hd D T hT
  obtain ⟨Cr, hCr, hdrift⟩ :=
    c8_unforced_drift_product_derivative_bound hlocal hends d hd D T hT
  let C := Cs + Ci + (d : ℝ) * T * ((d : ℝ) * Cc + 2 * Cr) + 1
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht i s hs
  have hpow : 0 ≤ s ^ (-(1/2+(d : ℝ)/4)) := Real.rpow_nonneg hs.le _
  by_cases hs₁ : s ≤ 1
  · exact (hsmall Q hQ β a μ hβ ha hμ (P 0) (Pdag 0) (hP 0) (hPdag 0)
      t ht i s hs hs₁).trans (mul_le_mul_of_nonneg_right (by
        have hnonneg : 0 ≤ (d : ℝ) * T * ((d : ℝ) * Cc + 2 * Cr) := by positivity
        dsimp only [C]
        linarith) hpow)
  have hs₁ : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
  have hpow₂ : s ^ (-((2 : ℝ)/2+(d : ℝ)/4)) ≤ s ^ (-(1/2+(d : ℝ)/4)) :=
    Real.rpow_le_rpow_of_exponent_le hs₁ (by norm_num; linarith)
  let U : Lp ℂ 2 (reducedLaw Q) := ∫ r in Icc (0 : ℝ) (t : ℝ), P 0 r.toNNReal (β i)
  have hcoefU (l k : Fin d) :
      ‖gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
        (complexCoefficientMul Q l k U)‖ ≤ (Cc * s ^ (-(1/2+(d : ℝ)/4))) * (t : ℝ) := by
    apply c8_coefficient_primitive_second_derivative_bound hd Q (fun r => P 0 r (β i))
      ((hP 0).2.2.1 (β i)) t l k s hs
    intro r hr
    have hc := hcoef Q hQ β a μ hβ ha hμ P Pdag hP hPdag r
      ((show (r : ℝ) ≤ t from hr).trans ht) i l k 2 (by decide) (by decide)
        (Fin.cases l (fun _ => k)) s hs
    exact hc.trans (mul_le_mul_of_nonneg_left hpow₂ hCc)
  obtain ⟨K, _, hobs⟩ := EndpointFiniteP.observation_bounds d D
  have hβB := (hobs Q hQ β a μ hβ ha hμ).1
  have hβtop (l : Fin d) : MemLp (β l : FieldPair d → ℂ) ∞ (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp _).aestronglyMeasurable K (hβB l)
  let M (l : Fin d) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2 ((hβtop l).toLp (β l))
  have hM (l : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
      (M l f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * f ω := by
    filter_upwards [(hβtop l).coeFn_toLp,
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((hβtop l).toLp (β l)) f]
      with ω h1 h2
    simpa only [M, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply', h1] using h2
  have hdriftU (l : Fin d) :
      ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (M l U)‖ ≤
        (Cr * s ^ (-(1/2+(d : ℝ)/4))) * (t : ℝ) := by
    let A := (gaussianDerivativeAverageCLM hd Q s hs 1 (fun _ => l)).comp (M l)
    have hb (r : ℝ≥0) (hr : r ≤ t) :
        ‖A (P 0 r (β i))‖ ≤ Cr * s ^ (-(1/2+(d : ℝ)/4)) := by
      obtain ⟨H, hH, hHb⟩ := hdrift Q hQ β a μ hβ ha hμ P Pdag hP hPdag r
        ((show (r : ℝ) ≤ t from hr).trans ht) i l
      have he := c8_gaussian_product_derivative_of_representatives hd Q
        (β l) (P 0 r (β i)) H (M l (P 0 r (β i))) hH (hM l _) s hs l
      have hraw := (congrArg norm he).symm.trans_le
        (hHb 1 (by decide) (by decide) (fun _ => l) s hs)
      simpa only [A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply,
        Nat.cast_one] using hraw
    simpa only [U, A, ContinuousLinearMap.comp_apply, gaussianDerivativeAverageCLM_apply] using
      c8_norm_operator_orbit_integral_le A (fun r => P 0 r (β i)) ((hP 0).2.2.1 (β i))
        t (Cr * s ^ (-(1/2+(d : ℝ)/4))) hb
  let V := ∫ r in Icc (0 : ℝ) (t : ℝ), (hP 0).gradientOrbit (β i) r
  let H (l : Fin d) := ∑ k, complexCoefficientMul Q l k (V k)
  have hHG (l : Fin d) : (H l : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∑ k : Fin d, (ω.1 0 l k : ℂ) * V k ω := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => complexCoefficientMul Q l k (V k)),
      ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q l k (V k))] with ω hsum hcoeff
    simpa only [H, Finset.sum_apply, hcoeff] using hsum
  have hrow (l : Fin d) :
      ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l)
        (∫ r in Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k ((hP 0).gradientOrbit (β i) r k))‖ ≤
      ((d : ℝ) * Cc + 2 * Cr) * (t : ℝ) * s ^ (-(1/2+(d : ℝ)/4)) := by
    rw [(hP 0).integral_flux_gradientOrbit]
    change ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (H l)‖ ≤ _
    rw [c8_gaussian_coefficient_row_derivative hd D Q hQ β hβ U (fun k => V k)
      ((hP 0).integral_orbit_gradient (β i) t) l (H l) (M l U) (hHG l) (hM l U) s hs l]
    calc
      _ ≤ (∑ k, ‖gaussianDerivativeAverage hd Q s hs 2 (Fin.cases l (fun _ => k))
            (complexCoefficientMul Q l k U)‖) +
          2 * ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (M l U)‖ := by
        exact (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _)
          (by simp only [norm_smul, Complex.norm_ofNat]; exact le_rfl))
      _ ≤ (∑ _k : Fin d, (Cc * s ^ (-(1/2+(d : ℝ)/4))) * (t : ℝ)) +
          2 * ((Cr * s ^ (-(1/2+(d : ℝ)/4))) * (t : ℝ)) :=
        add_le_add (Finset.sum_le_sum (fun k _ => hcoefU l k))
          (mul_le_mul_of_nonneg_left (hdriftU l) (by norm_num))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsum : ‖∑ l, gaussianDerivativeAverage hd Q s hs 1 (fun _ => l)
      (∫ r in Icc (0 : ℝ) (t : ℝ), ∑ k,
        complexCoefficientMul Q l k ((hP 0).gradientOrbit (β i) r k))‖ ≤
      (d : ℝ) * (((d : ℝ) * Cc + 2 * Cr) * (t : ℝ) * s ^ (-(1/2+(d : ℝ)/4))) := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun l _ => hrow l)).trans_eq
      (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]))
  have hhalf (x : Lp ℂ 2 (reducedLaw Q)) : ‖(1/2 : ℝ) • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    nlinarith [norm_nonneg x]
  rw [c8_unforced_gaussian_flux_increment hd (hP 0) hβ ha t i s hs]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hinit Q hQ β hβ i s hs) ((hhalf _).trans hsum)).trans
  have htbound : (d : ℝ) * (((d : ℝ) * Cc + 2 * Cr) * (t : ℝ) * s ^ (-(1/2+(d : ℝ)/4))) ≤
      ((d : ℝ) * T * ((d : ℝ) * Cc + 2 * Cr)) * s ^ (-(1/2+(d : ℝ)/4)) := by
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (show 0 ≤ (d : ℝ) * ((d : ℝ) * Cc + 2 * Cr) by positivity)) hpow
    nlinarith only [hb]
  calc
    _ ≤ Ci * s ^ (-(1/2+(d : ℝ)/4)) +
        ((d : ℝ) * T * ((d : ℝ) * Cc + 2 * Cr)) * s ^ (-(1/2+(d : ℝ)/4)) :=
      add_le_add (le_refl _) htbound
    _ ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
      rw [← add_mul]
      apply mul_le_mul_of_nonneg_right _ hpow
      dsimp only [C]
      linarith

end EinsteinFull.Blueprint
