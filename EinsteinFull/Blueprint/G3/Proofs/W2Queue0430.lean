import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_pairing
import EinsteinFull.Blueprint.G3.node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identification
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_early
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.G3.node_e_u3A_test_u2D_clt
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Blueprint.G3.Proofs.W2Queue0420_1

/-! Exact splitting and force-time moments for the endpoint pairing reduction.
The elementary centering proof follows G1.Proofs.W1Queue0240; no decay
or comparison assertion is assumed by the splitting lemmas. -/

open MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual reduced drift has zero mean. -/
theorem w2Pairing_drift_mean_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i : Fin d) : (∫ ω, β i ω ∂reducedLaw Q) = 0 := by
  letI := reducedLaw_probability Q
  have hh := hβ.integral_mul i (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const _ (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β i ω * Lp.const 2 (reducedLaw Q) 1 ω ∂reducedLaw Q) =
      ∫ ω, β i ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k, (ω.1 0 k i : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simpa only [hl, hr, mul_zero] using! hh

/-- Scalar multiplication commutes with centering the actual clock orbit. -/
theorem w2Pairing_clock_centered {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    clockEndpoint Q ζ P μ T = centeredComplexLp Q (P T (ζ • μ)) := by
  letI := reducedLaw_probability Q
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul ζ (centeredComplexLp Q (P T μ)),
    coeFn_centeredComplexLp Q (P T μ),
    coeFn_centeredComplexLp Q (P T (ζ • μ)),
    Lp.coeFn_smul ζ (P T μ)] with ω h1 h2 h3 h4
  have hi : (∫ ω, P T (ζ • μ) ω ∂reducedLaw Q) =
      ζ * ∫ ω, P T μ ω ∂reducedLaw Q := by
    rw [map_smul, integral_congr_ae (Lp.coeFn_smul ζ (P T μ))]
    exact integral_smul ζ _
  change (ζ • centeredComplexLp Q (P T μ)) ω = _
  rw [h1, Pi.smul_apply, h2, h3, hi, map_smul, h4, Pi.smul_apply]
  change ζ * (_ - _) = ζ * _ - ζ * _
  ring

/-- Bilinear splitting with a centered second endpoint. -/
theorem w2Pairing_split {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexTransposeSemigroup Q P R)
    (b f : Lp ℂ 2 (reducedLaw Q)) (hb : (∫ ω, b ω ∂reducedLaw Q) = 0)
    (T t : ℝ≥0) (ht : 2 * T ≤ t) :
    (∫ ω, b ω * P t f ω ∂reducedLaw Q) =
      ∫ ω, R T b ω * P (t - 2 * T) (centeredComplexLp Q (P T f)) ω
        ∂reducedLaw Q := by
  letI := reducedLaw_probability Q
  let m := ∫ ω, P T f ω ∂reducedLaw Q
  have hTt : T ≤ t := (le_add_of_nonneg_right T.property).trans (by simpa only [two_mul] using! ht)
  have hTT : T ≤ t - T := (le_tsub_iff_right hTt).mpr (by simpa only [two_mul] using! ht)
  have he : P (t - 2 * T) (centeredComplexLp Q (P T f)) =
      P (t - T) f - Lp.const 2 (reducedLaw Q) m := by
    unfold centeredComplexLp
    rw [map_sub, hP.map_const]
    have ht' : t - 2 * T + T = t - T := by
      rw [two_mul, ← tsub_tsub, tsub_add_cancel_of_le hTT]
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, ht']
  rw [he]
  have hmean := hR.integral_eq hP T b
  rw [hb] at hmean
  calc
    _ = ∫ ω, P (t - T) f ω * R T b ω ∂reducedLaw Q := by
      rw [← hR T (P (t - T) f) b]
      have htt : T + (t - T) = t := add_tsub_cancel_of_le hTt
      rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, htt]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => mul_comm _ _
    _ = ∫ ω, R T b ω * (P (t - T) f ω - m) ∂reducedLaw Q := by
      rw [show (fun ω => R T b ω * (P (t - T) f ω - m)) =
        (fun ω => R T b ω * P (t - T) f ω - R T b ω * m) by
          funext ω; ring]
      rw [integral_sub (integrable_complexLp_mul Q _ _)
        ((integrable_complexLp Q _).mul_const m), integral_mul_const, hmean,
        zero_mul, sub_zero]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => mul_comm _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (P (t - T) f) (Lp.const 2 (reducedLaw Q) m),
        Lp.coeFn_const 2 (reducedLaw Q) m] with ω hs hc
      simp only [hs, Pi.sub_apply, hc, Function.const_apply]


/-- Both physical correlations split into the actual half-time endpoints,
with the true bilinear transpose and zero transpose mean. -/
theorem w2Pairing_correlations {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) (ζ : ℂ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (T : ℝ≥0) :
    (∫ ω, transposeEndpoint Q i Pdag β T ω ∂reducedLaw Q) = 0 ∧
    (∀ j, velocityCorrelation Q i j ζ P β a (2 * T) =
      ∫ ω, transposeEndpoint Q i Pdag β T ω *
        velocityEndpoint Q i j ζ P β a T ω ∂reducedLaw Q) ∧
    clockCorrelation Q i ζ P β μ (2 * T) =
      ∫ ω, transposeEndpoint Q i Pdag β T ω *
        clockEndpoint Q ζ P μ T ω ∂reducedLaw Q := by
  have hb := w2Pairing_drift_mean_zero hβ i
  refine ⟨(hPdag.integral_eq hP T _).trans hb, ?_, ?_⟩
  · intro j
    simpa only [tsub_self, hP.1, ContinuousLinearMap.id_apply,
      velocityCorrelation, transposeEndpoint, velocityEndpoint] using!
      w2Pairing_split hP hPdag (β i) (β j + ζ • a i j) hb T (2 * T) le_rfl
  · simpa only [tsub_self, hP.1, ContinuousLinearMap.id_apply,
      clockCorrelation, transposeEndpoint, w2Pairing_clock_centered] using!
      w2Pairing_split hP hPdag (β i) (ζ • μ) hb T (2 * T) le_rfl

/-- The entire finite-p moment clause of the pairing contract follows from
scalar decay at the literal inverse-square signed-force time. -/
theorem w2Pairing_force_time_moments (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      ∀ lam : ℝ, 0 < |lam| → |lam| ≤ 1 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (lam : ℂ) P →
      IsComplexTransposeSemigroup Q P Pdag →
      let T := ((|lam| ^ 2)⁻¹ : ℝ).toNNReal
      (∀ U ∈ endpointCollection Q ⟨0, by omega⟩ (lam : ℂ) P Pdag β a μ T,
        MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧
      endpointMomentSum hd Q p (lam : ℂ) P Pdag β a μ T ≤
        Cp * |lam| ^ (1 + (d : ℝ) / 2) := by
  intro p hp
  obtain ⟨a₀, η₀, _, _, _, hs⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, _, _, _, hs⟩ := hs p hp
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ _Z hβ ha hμ _hZ lam hlam hsmall P Pdag hP hPdag
  let T : ℝ≥0 := ((|lam| ^ 2)⁻¹ : ℝ).toNNReal
  have hT : (T : ℝ) = (|lam| ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hTone : 1 ≤ (T : ℝ) := by
    rw [hT]
    exact (one_le_inv₀ (by positivity)).mpr (by nlinarith [abs_nonneg lam])
  have hsqrt : Real.sqrt (T : ℝ) = |lam|⁻¹ := by
    rw [hT, Real.sqrt_inv, Real.sqrt_sq (abs_nonneg lam)]
  have hforce : ‖(lam : ℂ)‖ * Real.sqrt (T : ℝ) ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hsqrt, mul_inv_cancel₀ hlam.ne']
    norm_num
  obtain ⟨hmem, hbound⟩ := (hs Q hQ β a μ hβ ha hμ (lam : ℂ) P Pdag hP hPdag).1
    T hTone hforce
  have hpower : (T : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) =
      |lam| ^ (1 + (d : ℝ) / 2) := by
    rw [hT, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_natCast_mul (abs_nonneg lam)]
    congr 1
    ring
  rw [hpower] at hbound
  exact ⟨hmem, hbound⟩

/-- Cauchy--Schwarz for the bilinear complex convention, without conjugating
one of the source's endpoints. -/
theorem w2Pairing_cauchy_schwarz {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, f ω * g ω ∂reducedLaw Q‖ ≤ ‖f‖ * ‖g‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hB : ‖B‖ ≤ 1 := B.opNorm_le_bound₂ zero_le_one (fun x y => by
    simp only [B, ContinuousLinearMap.mul_apply', norm_mul, one_mul, le_refl])
  have he : (∫ ω, f ω * g ω ∂reducedLaw Q) =
      L1.integral (B.holder 1 f g) := by
    rw [L1.integral_eq_integral]
    exact (integral_congr_ae (B.coeFn_holder f g)).symm
  rw [he]
  exact (L1.norm_integral_le _).trans ((B.norm_holder_apply_apply_le f g).trans
    (by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hB (norm_nonneg f)) (norm_nonneg g)
      simpa only [one_mul] using! hm))

/-- Comparing each of two L2 factors controls their literal bilinear product. -/
theorem w2Pairing_product_error {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f g f₀ g₀ : Lp ℂ 2 (reducedLaw Q)) :
    ‖(∫ ω, f ω * g ω ∂reducedLaw Q) -
      ∫ ω, f₀ ω * g₀ ω ∂reducedLaw Q‖ ≤
      ‖f - f₀‖ * ‖g‖ + ‖f₀‖ * ‖g - g₀‖ := by
  have he : (∫ ω, f ω * g ω ∂reducedLaw Q) -
      (∫ ω, f₀ ω * g₀ ω ∂reducedLaw Q) =
      (∫ ω, (f - f₀) ω * g ω ∂reducedLaw Q) +
      (∫ ω, f₀ ω * (g - g₀) ω ∂reducedLaw Q) := by
    rw [← integral_sub (integrable_complexLp_mul Q f g)
      (integrable_complexLp_mul Q f₀ g₀),
      ← integral_add (integrable_complexLp_mul Q (f - f₀) g)
        (integrable_complexLp_mul Q f₀ (g - g₀))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f f₀, Lp.coeFn_sub g g₀] with ω hf hg
    simp only [hf, hg, Pi.sub_apply]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (w2Pairing_cauchy_schwarz Q _ _) (w2Pairing_cauchy_schwarz Q _ _))

/-- Test CLT and the proved Gaussian Schwartz bounds control every model
endpoint uniformly before the law, scale and complex force are chosen. -/
theorem w2Pairing_model_bounds (htest : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ (R : ℝ) (hR : 0 < R), 2 ≤ R → ∀ (z : ℂ) (ν : EndpointIndex d),
      ‖(match ν with
        | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ)))‖ ≤
      C * Real.exp (C * (1 + ‖z‖) ^ 2) *
        (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  let N := 2 * d + 11
  obtain ⟨A, hA, ha⟩ := htest d hd D N (by dsimp [N]; omega)
  obtain ⟨B, hB, hb⟩ := w2ProfileTests_norm_bound d hd N D.ellipticity D.one_le_ellipticity
  let C := 1 + A * B + B
  have hC : 0 < C := by dsimp [C]; positivity
  have hABC : A * B ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; nlinarith [mul_pos hA hB]
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR hR2 z ν
  have hmodel := congrArg norm (w2ProfileTests_model hd Q Z R hR z ν)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hR _)] at hmodel
  apply hmodel.trans_le
  have hclt := ha Q hQ Z hZ R (by linarith) (w2ProfileTests hd Q z ν)
  have hnorm := hb D.dependenceRange Q z ν
  have hpair : ‖scaledJointPairing Q R hR Z (w2ProfileTests hd Q z ν)‖ ≤
      C * Real.exp (C * (1 + ‖z‖) ^ 2) := by
    calc
      _ ≤ A * schwartzTestNorm N (w2ProfileTests hd Q z ν) := hclt
      _ ≤ A * (B * Real.exp (B * (1 + ‖z‖) ^ 2)) :=
        mul_le_mul_of_nonneg_left hnorm hA.le
      _ = (A * B) * Real.exp (B * (1 + ‖z‖) ^ 2) := by ring
      _ ≤ _ := mul_le_mul hABC
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBC (sq_nonneg _)))
        (Real.exp_pos _).le hC.le
  have hscale : R ^ (-1 - (d : ℝ) / 2) ≤
      (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
    calc
      _ = (R ^ 2) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
        rw [← Real.rpow_natCast_mul hR.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity)
        (by nlinarith [sq_nonneg R]) (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  calc
    _ ≤ R ^ (-1 - (d : ℝ) / 2) * (C * Real.exp (C * (1 + ‖z‖) ^ 2)) :=
      mul_le_mul_of_nonneg_left hpair (Real.rpow_nonneg hR.le _)
    _ ≤ (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) *
        (C * Real.exp (C * (1 + ‖z‖) ^ 2)) :=
      mul_le_mul_of_nonneg_right hscale (mul_pos hC (Real.exp_pos _)).le
    _ = _ := mul_comm _ _

/-- The three exact identity clauses at the contract's literal parabolic scale. -/
theorem w2Pairing_scaled_correlations {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (R : ℝ) (z : ℂ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    let U := fun ν => indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ
      (R ^ 2 / 2).toNNReal
    (∫ ω, U (.inr true) ω ∂reducedLaw Q) = 0 ∧
    (∀ i, velocityCorrelation Q ⟨0, by omega⟩ i (z / (R : ℂ)) P β a
      (R ^ 2).toNNReal = ∫ ω, U (.inr true) ω * U (.inl i) ω ∂reducedLaw Q) ∧
    clockCorrelation Q ⟨0, by omega⟩ (z / (R : ℂ)) P β μ (R ^ 2).toNNReal =
      (∫ ω, U (.inr true) ω * U (.inr false) ω ∂reducedLaw Q) := by
  have ht : 2 * (R ^ 2 / 2).toNNReal = (R ^ 2).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_ofNat,
      Real.coe_toNNReal _ (by positivity : 0 ≤ R ^ 2 / 2),
      Real.coe_toNNReal _ (sq_nonneg R)]
    ring
  have h := w2Pairing_correlations a μ hβ ⟨0, by omega⟩ (z / (R : ℂ)) hP hPdag
    (R ^ 2 / 2).toNNReal
  rw [ht] at h
  exact h

/-- On the fixed complex disc scalar decay bounds every actual endpoint at
all scales R ≥ 2, with a single structural constant. -/
theorem w2Pairing_disc_actual_bounds (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
      ∀ (R : ℝ), 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ 2 →
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
      ∀ ν, ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ (R ^ 2 / 2).toNNReal‖ ≤
        C * (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  obtain ⟨a₀, η₀, _, _, _, hs⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, _, _, _, hs⟩ := hs 2 le_rfl
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ R hR2 z hz P Pdag hP hPdag ν
  have hR : 0 < R := by linarith
  let T := (R ^ 2 / 2).toNNReal
  have hT : (T : ℝ) = R ^ 2 / 2 := Real.coe_toNNReal _ (by positivity)
  have hTone : 1 ≤ (T : ℝ) := by rw [hT]; nlinarith
  have hsqrt : Real.sqrt (T : ℝ) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hR.le, by rw [hT]; nlinarith [sq_nonneg R]⟩
  have hforce : ‖z / (R : ℂ)‖ * Real.sqrt (T : ℝ) ≤ 2 := by
    calc
      _ ≤ ‖z / (R : ℂ)‖ * R := mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)
      _ = ‖z‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
          div_mul_cancel₀ _ hR.ne']
      _ ≤ 2 := hz
  have hb := ((hs Q hQ β a μ hβ ha hμ (z / (R : ℂ)) P Pdag hP hPdag).1
    T hTone hforce).2
  norm_num only [ENNReal.ofReal_ofNat] at hb
  simp only [← Lp.norm_def] at hb
  change ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β T‖ +
    (∑ j : Fin d, ‖velocityEndpoint Q ⟨0, by omega⟩ j (z / (R : ℂ)) P β a T‖) +
    ‖clockEndpoint Q (z / (R : ℂ)) P μ T‖ ≤ _ at hb
  rw [hT] at hb
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
    norm_nonneg (velocityEndpoint Q ⟨0, by omega⟩ j (z / (R : ℂ)) P β a T))
  cases ν with
  | inl i =>
    have hi := Finset.single_le_sum
      (f := fun j : Fin d => ‖velocityEndpoint Q ⟨0, by omega⟩ j (z / (R : ℂ)) P β a T‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    change ‖velocityEndpoint Q ⟨0, by omega⟩ i (z / (R : ℂ)) P β a T‖ ≤ _
    linarith only [hb, hi, norm_nonneg (transposeEndpoint Q ⟨0, by omega⟩ Pdag β T),
      norm_nonneg (clockEndpoint Q (z / (R : ℂ)) P μ T)]
  | inr b =>
    cases b
    · change ‖clockEndpoint Q (z / (R : ℂ)) P μ T‖ ≤ _
      linarith only [hb, hsum, norm_nonneg (transposeEndpoint Q ⟨0, by omega⟩ Pdag β T)]
    · change ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β T‖ ≤ _
      linarith only [hb, hsum, norm_nonneg (clockEndpoint Q (z / (R : ℂ)) P μ T)]

/-- The clock coordinate of the actual joint field is the centered clock class. -/
theorem w2Pairing_joint_clock {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {μ : Lp ℂ 2 (reducedLaw Q)}
    {Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)}
    (hμ : IsReducedClockObservation Q μ) (hZ : IsJointObservation Q Z) :
    Z (.inr ()) = centeredComplexLp Q μ := by
  have hi : (∫ ω, μ ω ∂reducedLaw Q) =
      ((∫ ω, ω.2 0 ∂reducedLaw Q : ℝ) : ℂ) := by
    rw [integral_congr_ae hμ, integral_complex_ofReal]
  apply Lp.ext
  filter_upwards [hZ.2, coeFn_centeredComplexLp Q μ, hμ] with ω hZω hc hμω
  rw [hZω, hc, hμω, hi, Complex.ofReal_sub]

/-- Extract the velocity/transpose comparisons for arbitrary actual semigroups,
using the constructed complete force family and uniqueness. -/
theorem w2Pairing_velocity_comparison
    (hu : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain : ℝ, 0 < gain ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ z : ℂ,
      (‖z‖ ≤ 2 ∨ ∃ x : ℝ, z = (x : ℂ) ∧
        |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ν : FluxIndex d,
      ‖indexedEndpoint hd Q (ν.elim Sum.inl (fun _ => Sum.inr true)) (z / (R : ℂ))
          P Pdag β a μ (R ^ 2 / 2).toNNReal -
        ν.elim (fun k => modelVelocityEndpoint hd Q Z k (R ^ 2 / 2) (by positivity)
          (z / (R : ℂ))) (fun _ => modelTransposeEndpoint hd Q Z (R ^ 2 / 2)
          (by positivity) (z / (R : ℂ)))‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
  obtain ⟨ε, gain, _, hg, hs⟩ := hu d hd D
  refine ⟨gain, hg, ?_⟩
  intro C₀ hC₀
  obtain ⟨C, R₀, hC, hR₀, hs⟩ := hs C₀ hC₀
  refine ⟨C, R₀, hC, hR₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ Z hZ R hR hRR z hz P Pdag hP hPdag ν
  let Pf := forcedComplexEvolution Q ⟨0, by omega⟩
  let Pt := fun w t => complexL2Transpose (reducedLaw Q) (Pf w t)
  have hPf := fun w => isComplexEnvironmentSemigroup_forcedComplexEvolution Q
    (⟨0, by omega⟩ : Fin d) w
  have hPt := fun w => isComplexTransposeSemigroup_complexL2Transpose Q (Pf w)
  obtain ⟨G, F, _, ht, hT, H, X, _, _, _, he⟩ :=
    hs Q hQ β a μ hβ ha hμ Z hZ R hR hRR z hz Pf Pt hPf hPt
  have hp : P = Pf (z / (R : ℂ)) := hP.eq_forcedComplexEvolution
  have hpt : Pdag = Pt (z / (R : ℂ)) := by
    rw [hPdag.eq_complexL2Transpose, hp]
  rw [hp, hpt]
  exact (he ν).2.2.2

/-- Extract the clock comparison for arbitrary actual semigroups and identify
its homogeneous datum with the clock coordinate of the joint field. -/
theorem w2Pairing_clock_comparison (hc : node_e_u3A_clock_u2D_earlyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain : ℝ, 0 < gain ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ T : ℝ, T₀ ≤ T → ∀ hT : 0 < T, ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ x : ℝ, ζ = (x : ℂ) ∧
        |x| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      ‖clockEndpoint Q ζ P μ T.toNNReal - modelClockEndpoint hd Q Z T hT ζ‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
  obtain ⟨gain, C, t₀, hg, _, _, hs⟩ := hc d hd D
  refine ⟨gain, hg, ?_⟩
  intro C₀ hC₀
  obtain ⟨Cw, T₀, hCw, hT₀, hs⟩ := hs C₀ hC₀
  refine ⟨Cw, T₀, hCw, hT₀, ?_⟩
  intro Q hQ a μ ha hμ Z hZ T hTT hT ζ hζ P hP
  have hPf := fun w => isComplexEnvironmentSemigroup_forcedComplexEvolution Q
    (⟨0, by omega⟩ : Fin d) w
  obtain ⟨_, ht, _, _, _, _, _, he⟩ :=
    (hs Q hQ a μ ha hμ (forcedComplexEvolution Q ⟨0, by omega⟩) hPf).2 T hTT ζ hζ
  rw [hP.eq_forcedComplexEvolution, modelClockEndpoint, w2Pairing_joint_clock hμ hZ]
  exact he

/-- The parabolic rescaling sends both endpoint windows into the clock window. -/
theorem w2Pairing_scaled_force (R : ℝ) (hR2 : 2 ≤ R) (z : ℂ) :
    R ≤ R ^ 2 / 2 ∧
    ‖z / (R : ℂ)‖ * Real.sqrt (R ^ 2 / 2) ≤ ‖z‖ ∧
    ‖z / (R : ℂ)‖ ^ 2 * (R ^ 2 / 2) ≤ (1 + ‖z‖) ^ 2 ∧
    Real.log R ^ (1 / 4 : ℝ) ≤ Real.log (R ^ 2 / 2) ^ (1 / 4 : ℝ) := by
  have hR : 0 < R := by linarith
  have hRT : R ≤ R ^ 2 / 2 := by nlinarith
  have hsqrt : Real.sqrt (R ^ 2 / 2) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hR.le, by nlinarith [sq_nonneg R]⟩
  have hn : ‖z / (R : ℂ)‖ = ‖z‖ / R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  refine ⟨hRT, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖z / (R : ℂ)‖ * R := mul_le_mul_of_nonneg_left hsqrt (norm_nonneg _)
      _ = ‖z‖ := by rw [hn, div_mul_cancel₀ _ hR.ne']
  · rw [hn]
    have he : (‖z‖ / R) ^ 2 * (R ^ 2 / 2) = ‖z‖ ^ 2 / 2 := by
      field_simp
    rw [he]
    nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
  · exact Real.rpow_le_rpow (Real.log_nonneg (by linarith))
      (Real.log_le_log hR hRT) (by norm_num)

/-- Constants may increase and a positive decay gain may decrease uniformly. -/
theorem w2Pairing_envelope_mono {A B T h g g' : ℝ} (hA : 0 ≤ A)
    (hAB : A ≤ B) (hT : 1 ≤ T) (hgg : g' ≤ g) (z : ℂ) :
    A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-h - g) ≤
      B * Real.exp (B * (1 + ‖z‖) ^ 2) * T ^ (-h - g') := by
  apply mul_le_mul
  · exact mul_le_mul hAB (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))) (Real.exp_pos _).le
      (hA.trans hAB)
  · exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  · exact Real.rpow_nonneg (by linarith) _
  · exact mul_nonneg (hA.trans hAB) (Real.exp_pos _).le

/-- Clock comparison after the endpoint rescaling, on both force windows. -/
theorem w2Pairing_scaled_clock_comparison (hc : node_e_u3A_clock_u2D_earlyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain : ℝ, 0 < gain ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ z : ℂ,
      (‖z‖ ≤ 2 ∨ ∃ x : ℝ, z = (x : ℂ) ∧
        |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      ‖clockEndpoint Q (z / (R : ℂ)) P μ (R ^ 2 / 2).toNNReal -
          modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
  obtain ⟨gain, hg, hs⟩ := w2Pairing_clock_comparison hc d hd D
  refine ⟨gain, hg, ?_⟩
  intro C₀ hC₀
  obtain ⟨C, T₀, hC, hT₀, hs⟩ := hs C₀ hC₀
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro Q hQ a μ ha hμ Z hZ R hR hRR z hz P hP
  have hR2 : 2 ≤ R := hT₀.trans hRR
  obtain ⟨hRT, hforce, hquad, hlog⟩ := w2Pairing_scaled_force R hR2 z
  have hw : ‖z / (R : ℂ)‖ * Real.sqrt (R ^ 2 / 2) ≤ 2 ∨
      ∃ x : ℝ, z / (R : ℂ) = (x : ℂ) ∧
        |x| * Real.sqrt (R ^ 2 / 2) ≤ C₀ * Real.log (R ^ 2 / 2) ^ (1 / 4 : ℝ) := by
    rcases hz with hz | ⟨x, rfl, hx⟩
    · exact Or.inl (hforce.trans hz)
    · refine Or.inr ⟨x / R, by push_cast; rfl, ?_⟩
      have hn : ‖(x : ℂ) / (R : ℂ)‖ = |x / R| := by
        rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
      rw [hn, Complex.norm_real, Real.norm_eq_abs] at hforce
      exact hforce.trans (hx.trans (mul_le_mul_of_nonneg_left hlog hC₀.le))
  have he := hs Q hQ a μ ha hμ Z hZ (R ^ 2 / 2) (hRR.trans hRT)
    (by positivity) (z / (R : ℂ)) hw P hP
  refine he.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _))
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hquad hC.le]

/-- Indexing abbreviation for the three literal frozen model endpoints. -/
noncomputable def w2Pairing_modelEndpoint {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R : ℝ) (hR : 0 < R) (z : ℂ) (ν : EndpointIndex d) : Lp ℂ 2 (reducedLaw Q) :=
  match ν with
  | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
  | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
  | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))

/-- A single structural gain controls every actual/model endpoint difference
on both windows, once the structural or window-dependent scale is large. -/
theorem w2Pairing_large_comparison
    (hu : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt)
    (hc : node_e_u3A_clock_u2D_earlyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain : ℝ, 0 < gain ∧
    ∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ z : ℂ,
      (‖z‖ ≤ 2 ∨ ∃ x : ℝ, z = (x : ℂ) ∧
        |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ν : EndpointIndex d,
      ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ (R ^ 2 / 2).toNNReal -
          w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain) := by
  obtain ⟨gu, hgu, hu⟩ := w2Pairing_velocity_comparison hu d hd D
  obtain ⟨gc, hgc, hc⟩ := w2Pairing_scaled_clock_comparison hc d hd D
  refine ⟨min gu gc, lt_min hgu hgc, ?_⟩
  intro C₀ hC₀
  obtain ⟨Cu, Ru, hCu, hRu, hu⟩ := hu C₀ hC₀
  obtain ⟨Cc, Rc, hCc, hRc, hc⟩ := hc C₀ hC₀
  refine ⟨max Cu Cc, max Ru Rc, hCu.trans_le (le_max_left _ _),
    hRu.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ Z hZ R hR hRR z hz P Pdag hP hPdag ν
  have hRRu := (le_max_left Ru Rc).trans hRR
  have hRRc := (le_max_right Ru Rc).trans hRR
  have hT : 1 ≤ R ^ 2 / 2 := by nlinarith [hRu.trans hRRu]
  have heu := hu Q hQ β a μ hβ ha hμ Z hZ R hR hRRu z hz P Pdag hP hPdag
  have hec := hc Q hQ a μ ha hμ Z hZ R hR hRRc z hz P hP
  cases ν with
  | inl i =>
    exact (heu (.inl i)).trans (w2Pairing_envelope_mono hCu.le
      (le_max_left _ _) hT (min_le_left _ _) z)
  | inr b =>
    cases b
    · exact hec.trans (w2Pairing_envelope_mono hCc.le
        (le_max_right _ _) hT (min_le_right _ _) z)
    · exact (heu (.inr ())).trans (w2Pairing_envelope_mono hCu.le
        (le_max_left _ _) hT (min_le_left _ _) z)

/-- Endpoint error and model norm bounds control the actual norms, the full
endpoint error sum and both bilinear bridge errors. -/
theorem w2Pairing_errors {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (R : ℝ) (hR : 0 < R) (z : ℂ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (E N : ℝ) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (he : ∀ ν, ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ
        (R ^ 2 / 2).toNNReal - w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤ E)
    (hn : ∀ ν, ‖w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤ N) :
    (∀ ν, ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ
      (R ^ 2 / 2).toNNReal‖ ≤ E + N) ∧
    endpointComparisonError hd Q R hR z P Pdag β a μ Z ≤ ((d : ℝ) + 2) * E ∧
    ∀ i, forcedComparisonError hd Q R hR z i P β a μ Z ≤ 2 * E * (E + 2 * N) := by
  let U := fun ν => indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ
    (R ^ 2 / 2).toNNReal
  let M := w2Pairing_modelEndpoint hd Q Z R hR z
  have hu (ν) : ‖U ν‖ ≤ E + N := by
    calc
      _ = ‖(U ν - M ν) + M ν‖ := by rw [sub_add_cancel]
      _ ≤ ‖U ν - M ν‖ + ‖M ν‖ := norm_add_le _ _
      _ ≤ E + N := add_le_add (he ν) (hn ν)
  refine ⟨hu, ?_, ?_⟩
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      he (.inl i))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    change ‖U (.inr true) - M (.inr true)‖ +
      (∑ i, ‖U (.inl i) - M (.inl i)‖) + ‖U (.inr false) - M (.inr false)‖ ≤ _
    linarith only [he (.inr true), he (.inr false), hs]
  · intro i
    obtain ⟨_, hv, hc⟩ := w2Pairing_scaled_correlations hd a μ hβ R z hP hPdag
    have hp (ν : EndpointIndex d) :
        ‖(∫ ω, U (.inr true) ω * U ν ω ∂reducedLaw Q) -
          ∫ ω, M (.inr true) ω * M ν ω ∂reducedLaw Q‖ ≤ E * (E + 2 * N) := by
      calc
        _ ≤ ‖U (.inr true) - M (.inr true)‖ * ‖U ν‖ +
            ‖M (.inr true)‖ * ‖U ν - M ν‖ := w2Pairing_product_error Q _ _ _ _
        _ ≤ E * (E + N) + N * E := add_le_add
          (mul_le_mul (he (.inr true)) (hu ν) (norm_nonneg _) hE)
          (mul_le_mul (hn (.inr true)) (he ν) (norm_nonneg _) hN)
        _ = E * (E + 2 * N) := by ring
    change ‖velocityCorrelation Q _ i _ P β a _ - _‖ +
      ‖clockCorrelation Q _ _ P β μ _ - _‖ ≤ _
    rw [hv i, hc]
    exact (add_le_add (hp (.inl i)) (hp (.inr false))).trans_eq (by ring)

/-- Uniform scalar constants for endpoint sums and the bridge after parabolic
rescaling; the same positive gain works in both conclusions. -/
theorem w2Pairing_numeric_envelopes (d : ℕ) (gain A : ℝ) (hg : 0 ≤ gain) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 2 ≤ R → ∀ z : ℂ,
      let T := R ^ 2 / 2
      let h := 1 / 2 + (d : ℝ) / 4
      let N := A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-h)
      let E := A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-h - gain)
      E ≤ N ∧
      E + N ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-h) ∧
      ((d : ℝ) + 2) * E ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-h - gain) ∧
      2 * E * (E + 2 * N) ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) *
        R ^ (-(d : ℝ) - 2 - 2 * gain) := by
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  let K := 6 * A ^ 2 * (2 : ℝ) ^ (2 * h + gain)
  let C := max (2 * A) (max (((d : ℝ) + 2) * A) K)
  have h2AC : 2 * A ≤ C := le_max_left _ _
  have hdAC : ((d : ℝ) + 2) * A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hKC : K ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hAC : A ≤ C := (by linarith : A ≤ 2 * A).trans h2AC
  have hC : 0 < C := hA.trans_le hAC
  refine ⟨C, hC, ?_⟩
  intro R hR2 z
  have hR : 0 < R := by linarith
  let T := R ^ 2 / 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := by dsimp [T]; nlinarith
  let q := (1 + ‖z‖) ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  let N := A * Real.exp (A * q) * T ^ (-h)
  let E := A * Real.exp (A * q) * T ^ (-h - gain)
  change E ≤ N ∧ E + N ≤ C * Real.exp (C * q) * T ^ (-h) ∧
    ((d : ℝ) + 2) * E ≤ C * Real.exp (C * q) * T ^ (-h - gain) ∧
    2 * E * (E + 2 * N) ≤ C * Real.exp (C * q) * R ^ (-(d : ℝ) - 2 - 2 * gain)
  have hEN : E ≤ N := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
    (mul_nonneg hA.le (Real.exp_pos _).le)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨hEN, ?_, ?_, ?_⟩
  · calc
      E + N ≤ 2 * N := by linarith only [hEN]
      _ = (2 * A) * Real.exp (A * q) * T ^ (-h) := by dsimp [N]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul h2AC (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAC hq))
          (Real.exp_pos _).le hC.le) (Real.rpow_nonneg hT.le _)
  · calc
      ((d : ℝ) + 2) * E = (((d : ℝ) + 2) * A) * Real.exp (A * q) *
          T ^ (-h - gain) := by dsimp [E]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hdAC (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAC hq))
          (Real.exp_pos _).le hC.le) (Real.rpow_nonneg hT.le _)
  · have hscale : T ^ (-h - gain) * T ^ (-h) =
        (2 : ℝ) ^ (2 * h + gain) * R ^ (-(d : ℝ) - 2 - 2 * gain) := by
      rw [← Real.rpow_add hT]
      change (R ^ 2 / 2) ^ (-h - gain + -h) = _
      rw [Real.div_rpow (sq_nonneg R) (by norm_num), ← Real.rpow_natCast_mul hR.le]
      norm_num only [Nat.cast_ofNat]
      have hex : (2 : ℝ) * (-h - gain + -h) = -(d : ℝ) - 2 - 2 * gain := by
        dsimp [h]; ring
      have hey : -h - gain + -h = -(2 * h + gain) := by ring
      rw [hex, hey, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]
    calc
      2 * E * (E + 2 * N) ≤ 6 * E * N := by nlinarith only [mul_le_mul_of_nonneg_left hEN hE]
      _ = K * Real.exp ((2 * A) * q) * R ^ (-(d : ℝ) - 2 - 2 * gain) := by
        dsimp [E, N, K]
        rw [show 2 * A * q = A * q + A * q by ring, Real.exp_add]
        calc
          _ = 6 * A ^ 2 * (Real.exp (A * q) * Real.exp (A * q)) *
              (T ^ (-h - gain) * T ^ (-h)) := by ring
          _ = _ := by rw [hscale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hKC (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2AC hq))
          (Real.exp_pos _).le hC.le) (Real.rpow_nonneg hR.le _)

/-- Increasing the coefficient absorbs a bounded range of parabolic scales. -/
theorem w2Pairing_bounded_scale (Ca Cm R₀ gain h : ℝ)
    (hCa : 0 < Ca) (hCm : 0 < Cm) (hg : 0 ≤ gain) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → R ≤ R₀ → ∀ z : ℂ,
      Ca * (R ^ 2 / 2) ^ (-h) + Cm * Real.exp (Cm * (1 + ‖z‖) ^ 2) *
        (R ^ 2 / 2) ^ (-h) ≤
      C * Real.exp (C * (1 + ‖z‖) ^ 2) * (R ^ 2 / 2) ^ (-h - gain) := by
  let B := Ca + Cm
  let S := (R₀ ^ 2 / 2) ^ gain
  let C := max (B * S) B
  have hB : 0 < B := add_pos hCa hCm
  have hBC : B ≤ C := le_max_right _ _
  have hsC : B * S ≤ C := le_max_left _ _
  have hC : 0 < C := hB.trans_le hBC
  refine ⟨C, hC, ?_⟩
  intro R hR2 hRR z
  have hR : 0 < R := by linarith only [hR2]
  have hT : 0 < R ^ 2 / 2 := by positivity
  have hCmB : Cm ≤ B := le_add_of_nonneg_left hCa.le
  have hq := sq_nonneg (1 + ‖z‖)
  have hex : 1 ≤ Real.exp (B * (1 + ‖z‖) ^ 2) :=
    Real.one_le_exp (mul_nonneg hB.le hq)
  have hsmall : (R ^ 2 / 2) ^ gain ≤ S := Real.rpow_le_rpow hT.le
    (by nlinarith only [hR2, hRR, sq_nonneg (R₀ - R)]) hg
  have hpow : (R ^ 2 / 2) ^ (-h) =
      (R ^ 2 / 2) ^ gain * (R ^ 2 / 2) ^ (-h - gain) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  calc
    _ ≤ B * Real.exp (B * (1 + ‖z‖) ^ 2) * (R ^ 2 / 2) ^ (-h) := by
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex hCa.le)
        (Real.rpow_nonneg hT.le (-h))
      have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCmB hq)) hCm.le)
        (Real.rpow_nonneg hT.le (-h))
      dsimp [B]
      nlinarith only [h1, h2]
    _ = (B * (R ^ 2 / 2) ^ gain) * Real.exp (B * (1 + ‖z‖) ^ 2) *
        (R ^ 2 / 2) ^ (-h - gain) := by rw [hpow]; ring
    _ ≤ (B * S) * Real.exp (B * (1 + ‖z‖) ^ 2) *
        (R ^ 2 / 2) ^ (-h - gain) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hB.le)
        (Real.exp_pos _).le) (Real.rpow_nonneg hT.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hsC (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBC hq))
        (Real.exp_pos _).le hC.le) (Real.rpow_nonneg hT.le _)

/-- A bounded pair of vectors gives the corresponding difference bound. -/
theorem w2Pairing_sub_bound {F : Type*} [SeminormedAddCommGroup F]
    (f g : F) {x y t : ℝ} (hf : ‖f‖ ≤ x) (hg : ‖g‖ ≤ y) (hxy : x + y ≤ t) :
    ‖f - g‖ ≤ t :=
  (norm_sub_le f g).trans ((add_le_add hf hg).trans hxy)

/-- Complete endpoint comparisons on the fixed disc, including its bounded
scale range, and on the growing real window with a shared structural gain. -/
theorem w2Pairing_comparison
    (hu : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt)
    (hc : node_e_u3A_clock_u2D_earlyStmt) (hscalar : node_p_u3A_scalarStmt)
    (htest : node_e_u3A_test_u2D_cltStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain C : ℝ, 0 < gain ∧ 0 < C ∧
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ R : ℝ, ∀ hR : 0 < R, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ 2 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ν : EndpointIndex d,
      ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ (R ^ 2 / 2).toNNReal -
          w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) ∧
    (∀ C₀ : ℝ, 0 < C₀ → ∃ C R₀ : ℝ, 0 < C ∧ 2 ≤ R₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ z : ℝ,
      |z| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ((z : ℂ) / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ν : EndpointIndex d,
      ‖indexedEndpoint hd Q ν ((z : ℂ) / (R : ℂ)) P Pdag β a μ (R ^ 2 / 2).toNNReal -
          w2Pairing_modelEndpoint hd Q Z R hR (z : ℂ) ν‖ ≤
        C * Real.exp (C * (1 + ‖(z : ℂ)‖) ^ 2) *
          (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) := by
  obtain ⟨gain, hg, hl⟩ := w2Pairing_large_comparison hu hc d hd D
  obtain ⟨Ca, hCa, ha⟩ := w2Pairing_disc_actual_bounds hscalar d hd D
  obtain ⟨Cm, hCm, hm⟩ := w2Pairing_model_bounds htest d hd D
  obtain ⟨Cl, R₀, hCl, hR₀, hdisc⟩ := hl 1 (by norm_num)
  obtain ⟨Cs, hCs, hsmall⟩ := w2Pairing_bounded_scale Ca Cm R₀ gain
    (1 / 2 + (d : ℝ) / 4) hCa hCm hg.le
  let C := max Cl Cs
  have hlC : Cl ≤ C := le_max_left _ _
  have hsC : Cs ≤ C := le_max_right _ _
  have hC : 0 < C := hCl.trans_le hlC
  refine ⟨gain, C, hg, hC, ?_, ?_⟩
  · intro Q hQ β a μ hβ hcoeff hμ Z hZ R hR hR2 z hz P Pdag hP hPdag ν
    have hT1 : 1 ≤ R ^ 2 / 2 := by nlinarith only [hR2]
    by_cases hRR : R₀ ≤ R
    · exact (hdisc Q hQ β a μ hβ hcoeff hμ Z hZ R hR hRR z (Or.inl hz)
        P Pdag hP hPdag ν).trans
        (w2Pairing_envelope_mono hCl.le hlC hT1 le_rfl z)
    · have han : ‖indexedEndpoint hd Q ν (z / (R : ℂ)) P Pdag β a μ
          (R ^ 2 / 2).toNNReal‖ ≤ Ca * (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) :=
        ha Q hQ β a μ hβ hcoeff hμ R hR2 z hz P Pdag hP hPdag ν
      have hmn : ‖w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
          Cm * Real.exp (Cm * (1 + ‖z‖) ^ 2) * (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) :=
        hm Q hQ Z hZ R hR hR2 z ν
      exact w2Pairing_sub_bound _ _ han hmn ((hsmall R hR2 (not_le.mp hRR).le z).trans
        (w2Pairing_envelope_mono hCs.le hsC hT1 le_rfl z))
  · intro C₀ hC₀
    obtain ⟨Cw, Rw, hCw, hRw, hw⟩ := hl C₀ hC₀
    refine ⟨Cw, Rw, hCw, hRw, ?_⟩
    intro Q hQ β a μ hβ ha hμ Z hZ R hR hRR z hz P Pdag hP hPdag ν
    exact hw Q hQ β a μ hβ ha hμ Z hZ R hR hRR (z : ℂ)
      (Or.inr ⟨z, rfl, hz⟩) P Pdag hP hPdag ν

/-- Assemble the literal pairing conclusion at any scale from the individual
endpoint comparisons and model norm bounds, with constants chosen uniformly. -/
theorem w2Pairing_at_scale (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (gain A : ℝ) (hg : 0 ≤ gain) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ R : ℝ, ∀ hR : 0 < R, 2 ≤ R → ∀ z : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ (z / (R : ℂ)) P →
      IsComplexTransposeSemigroup Q P Pdag →
      let T : ℝ := R ^ 2 / 2
      let hT : 0 < T := by positivity
      let ζ := z / (R : ℂ)
      let U := fun ν => indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal
      (∀ ν, ‖U ν - w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
        A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain)) →
      (∀ ν, ‖w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
        A * Real.exp (A * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4))) →
      (∫ ω, U (.inr true) ω ∂reducedLaw Q) = 0 ∧
      (∀ i, velocityCorrelation Q ⟨0, by omega⟩ i ζ P β a (R ^ 2).toNNReal =
        ∫ ω, U (.inr true) ω * U (.inl i) ω ∂reducedLaw Q) ∧
      clockCorrelation Q ⟨0, by omega⟩ ζ P β μ (R ^ 2).toNNReal =
        (∫ ω, U (.inr true) ω * U (.inr false) ω ∂reducedLaw Q) ∧
      (∀ ν, ‖U ν‖ ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) *
        T ^ (-(1 / 2 + (d : ℝ) / 4))) ∧
      (∀ i, ‖modelVelocityEndpoint hd Q Z i T hT ζ‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4))) ∧
      ‖modelTransposeEndpoint hd Q Z T hT ζ‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) ∧
      ‖modelClockEndpoint hd Q Z T hT ζ‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4)) ∧
      endpointComparisonError hd Q R hR z P Pdag β a μ Z ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * T ^ (-(1 / 2 + (d : ℝ) / 4) - gain) ∧
      ∀ i : Fin d, forcedComparisonError hd Q R hR z i P β a μ Z ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * R ^ (-(d : ℝ) - 2 - 2 * gain) := by
  obtain ⟨C, hC, hnum⟩ := w2Pairing_numeric_envelopes d gain A hg hA
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ Z hβ R hR hR2 z P Pdag hP hPdag
  dsimp only
  intro he hn
  let N := A * Real.exp (A * (1 + ‖z‖) ^ 2) *
    (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4))
  let E := A * Real.exp (A * (1 + ‖z‖) ^ 2) *
    (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4) - gain)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  obtain ⟨hu, hs, hf⟩ := w2Pairing_errors hd a μ Z hβ R hR z hP hPdag E N hE hN he hn
  obtain ⟨_, hnorm, hsum, hbridge⟩ := hnum R hR2 z
  obtain ⟨hmean, hv, hc⟩ := w2Pairing_scaled_correlations hd a μ hβ R z hP hPdag
  have hm (ν) := (hn ν).trans ((le_add_of_nonneg_left hE).trans hnorm)
  exact ⟨hmean, hv, hc, fun ν => (hu ν).trans hnorm,
    fun i => hm (.inl i), hm (.inr true), hm (.inr false), hs.trans hsum,
    fun i => (hf i).trans hbridge⟩

/-- Bilinear endpoint pairing, both force windows and all finite-p force-time
moments, from exactly the five prescribed graph dependencies. -/
theorem node_p_u3A_endpoint_u2D_comparison_u23_pairing_of_deps
    (hu : node_p_u3A_endpoint_u2D_comparison_u23_unforced_u2D_identificationStmt)
    (hc : node_e_u3A_clock_u2D_earlyStmt)
    (hclockaverage : node_e_u3A_clock_u2D_averageStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (htest : node_e_u3A_test_u2D_cltStmt) :
    node_p_u3A_endpoint_u2D_comparison_u23_pairingStmt := by
  intro d hd D
  obtain ⟨εavg, Cavg, tavg, _, _, _, _⟩ := hclockaverage d hd D
  obtain ⟨gain, Ce, hg, hCe, he, hw⟩ := w2Pairing_comparison hu hc hscalar htest d hd D
  obtain ⟨Cm, hCm, hm⟩ := w2Pairing_model_bounds htest d hd D
  let A := max Ce Cm
  have hA : 0 < A := hCe.trans_le (le_max_left _ _)
  obtain ⟨C, hC, hassemble⟩ := w2Pairing_at_scale d hd D gain A hg.le hA
  refine ⟨gain, C, hg, hC, ?_, ?_, w2Pairing_force_time_moments hscalar d hd D⟩
  · intro Q hQ β a μ Z hβ ha hμ hZ R hR hR2 z hz P Pdag hP hPdag
    have hT : 1 ≤ R ^ 2 / 2 := by nlinarith
    apply hassemble Q hQ β a μ Z hβ R hR hR2 z P Pdag hP hPdag
    · intro ν
      exact (he Q hQ β a μ hβ ha hμ Z hZ R hR hR2 z hz P Pdag hP hPdag ν).trans
        (w2Pairing_envelope_mono hCe.le (le_max_left _ _) hT le_rfl z)
    · intro ν
      have hmodel : ‖w2Pairing_modelEndpoint hd Q Z R hR z ν‖ ≤
          Cm * Real.exp (Cm * (1 + ‖z‖) ^ 2) * (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) :=
        hm Q hQ Z hZ R hR hR2 z ν
      apply hmodel.trans
      simpa only [sub_zero] using! w2Pairing_envelope_mono (g := 0) (g' := 0)
        hCm.le (le_max_right Ce Cm) hT le_rfl z
  · intro C₀ hC₀
    obtain ⟨Cw, R₀, hCw, hR₀, hw⟩ := hw C₀ hC₀
    let Aw := max Cw Cm
    have hAw : 0 < Aw := hCw.trans_le (le_max_left _ _)
    obtain ⟨Cout, hCout, hassemble⟩ := w2Pairing_at_scale d hd D gain Aw hg.le hAw
    -- Keep the growing-window scales beyond the structural early clock interval.
    refine ⟨Cout, max R₀ tavg, hCout, hR₀.trans (le_max_left _ _), ?_⟩
    intro Q hQ β a μ Z hβ ha hμ hZ R hR hRR z hz P Pdag hP hPdag
    have hRR₀ := (le_max_left R₀ tavg).trans hRR
    have hR2 := hR₀.trans hRR₀
    have hT : 1 ≤ R ^ 2 / 2 := by nlinarith
    apply hassemble Q hQ β a μ Z hβ R hR hR2 (z : ℂ) P Pdag hP hPdag
    · intro ν
      exact (hw Q hQ β a μ hβ ha hμ Z hZ R hR hRR₀ z hz P Pdag hP hPdag ν).trans
        (w2Pairing_envelope_mono hCw.le (le_max_left _ _) hT le_rfl (z : ℂ))
    · intro ν
      have hmodel : ‖w2Pairing_modelEndpoint hd Q Z R hR (z : ℂ) ν‖ ≤
          Cm * Real.exp (Cm * (1 + ‖(z : ℂ)‖) ^ 2) *
            (R ^ 2 / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) :=
        hm Q hQ Z hZ R hR hR2 (z : ℂ) ν
      apply hmodel.trans
      simpa only [sub_zero] using! w2Pairing_envelope_mono (g := 0) (g' := 0)
        hCm.le (le_max_right Cw Cm) hT le_rfl (z : ℂ)

end EinsteinFull.Blueprint
