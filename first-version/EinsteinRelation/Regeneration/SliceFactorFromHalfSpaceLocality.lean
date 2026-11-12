import EinsteinRelation.Regeneration.FirstSlicePastLocality
import EinsteinRelation.Regeneration.KilledFutureLocalityTransport
import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.CorrectedHalfSpaceIndependence
import EinsteinRelation.Regeneration.RenewalFromSliceFactor

/-!
# Slice factorization from coupled half-space locality

Source `paper/main.tex:389–415`. The deterministic restart and endpoint
calculation, Fubini, finite-range independence, spatial stationarity and
normalization give the exact slice factorization. Coupled past locality,
killed joint-future locality and covariance remain internal premises;
this module does not promote them to literature inputs.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- The source's spatial product integral factors once its two local
versions are available. Only spatial-a.e. future versions are required. -/
theorem integral_firstSlicePastIntegral_mul_eq_of_local_versions {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) (hgap : r₀ < 2 * R)
    (hpast : HasPastHalfSpaceVersions Q.measure Δ i R K)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (B : Vec d × FieldPair d → ℝ)
    (hlocal : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B' ∧
      (fun ω => B (y, ω)) =ᵐ[Q.measure] B')
    (b : ℝ) (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, B (y, ω) ∂Q.measure) = b) :
    (∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω) ∂Q.measure) =
      b * ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) ∂Q.measure := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hlocal, hmean] with y hy hm
  obtain ⟨B', hB', hBe⟩ := hy
  obtain ⟨A', hA', hAe⟩ := exists_firstSlicePastIntegral_local_version Q.measure K Δ hΔ
    lam R hlam hR i hpast m H hH hbH y
  rw [integral_mul_eq_of_corrected_halfSpace_versions Q i (y i) R hgap
    (fun ω => firstSlicePastIntegral Δ lam R i m K H (y, ω)) (fun ω => B (y, ω))
    A' B' hA' hB' hAe hBe, hm, mul_comm]

/-- Before normalization, a slice integral is the mean killed future
times a past-only spatial integral (`paper/main.tex:405–411`). -/
theorem firstRegeneration_slice_integral_factor_of_locality {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (hlam : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam hlam.le h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d) (hgap : r₀ < 2 * R)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (hpast : HasPastHalfSpaceVersions Q.measure Δ i R K)
    (hcov : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      (K xω).map (recenterSample xω.1) = K (0, translate xω.1 xω.2))
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ)
    (A : FieldPair d → ℝ)
    (hA : Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] A)
    (hAo : ∀ᵐ ω ∂Q.measure, A ω = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω))
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) :
    (∫ p in {p : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R p.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
      H p.2 * Φ (iteratedRecord Δ lam R i 1 p) ∂annealedCoupledLaw Q.measure K) =
      (∫ ω, A ω ∂Q.measure) *
        ((δ / (volume (endpointBall i R (0 : Vec d))).toReal) *
          ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) ∂Q.measure) := by
  obtain ⟨C, _, B, hB, hbB, hBo, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q.measure K hK R i Φ hΦ hb
  have hlocal := exists_killed_future_local_versions_of_covariance Q.measure Q.stationary
    K R i Φ hΦ B hBp A hA hAo hcov
  have hmean := integral_killed_future_version_eq_origin_of_covariance Q.measure Q.stationary
    K R i Φ hΦ B hB hBo hBp hcov
  have hzero : (∫ ω, B (0, ω) ∂Q.measure) = ∫ ω, A ω ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [hBo, hAo] with ω hω ha
    exact hω.trans ha.symm
  simp_rw [hzero] at hmean
  rw [firstRegeneration_slice_integral_eq hd Q lam hlam.le h1 P K hK hpath hP Δ hΔ δ R hR i
      hRestart hUniform Φ hΦ hb B hB ⟨C, hbB⟩ hBp m H hH hbH,
    integral_firstSlicePastIntegral_mul_eq_of_local_versions Q K Δ hΔ lam R hlam hR i
      hgap hpast m H hH hbH B hlocal _ hmean]
  ring

/-- The exact internal slice target follows from coupled half-space
locality and spatial-a.e. covariance. Its future-locality premise concerns
the full restricted record and remains an internal proof obligation. -/
theorem firstRegenerationSliceFactor_of_halfSpace_locality {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (hlam : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam hlam.le h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d) (hgap : r₀ < 2 * R)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (hpast : HasPastHalfSpaceVersions Q.measure Δ i R K)
    (hcov : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      (K xω).map (recenterSample xω.1) = K (0, translate xω.1 xω.2))
    (hfuture : ∀ (Φ : FutureState d i R → ℝ), Measurable Φ → BoundedRealTest Φ →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] A ∧
        ∀ᵐ ω ∂Q.measure, A ω = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω))
    (hD : annealedCoupledLaw Q.measure K {p | NoBacktracking R p.2.1 i} ≠ 0) :
    FirstRegenerationSliceFactor Q.measure K Δ lam R i := by
  let μ := annealedCoupledLaw Q.measure K
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond μ {p | NoBacktracking R p.2.1 i}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  have hstart := ae_origin_start_of_isGMPReducedKernel hd Q lam hlam.le h1 P K hK hpath hP
  intro Φ hΦ hb m H hH hbH
  obtain ⟨A, hA, hAo⟩ := hfuture Φ hΦ hb
  obtain ⟨A1, hA1, hA1o⟩ := hfuture (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
  have hfac := firstRegeneration_slice_integral_factor_of_locality hd Q lam hlam h1 P K hK
    hpath hP Δ hΔ δ R hR i hgap hRestart hUniform hpast hcov Φ hΦ hb A hA hAo m H hH hbH
  have hone := firstRegeneration_slice_integral_factor_of_locality hd Q lam hlam h1 P K hK
    hpath hP Δ hΔ δ R hR i hgap hRestart hUniform hpast hcov (fun _ => 1) measurable_const
    ⟨1, fun _ => by norm_num⟩ A1 hA1 hA1o m H hH hbH
  simp only [mul_one] at hone
  have hmean := integral_killed_future_origin_eq_condIntegral Q.measure K hK hstart Δ lam R i hD
    Φ hΦ hb (fun p => A p.2) hAo
  have hmean1 := integral_killed_future_origin_eq_condIntegral Q.measure K hK hstart Δ lam R i hD
    (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩ (fun p => A1 p.2) hA1o
  change (∫ ω, A1 ω ∂Q.measure) = (μ {p | NoBacktracking R p.2.1 i}).toReal *
    ∫ p, (1 : ℝ) ∂ProbabilityTheory.cond μ {p | NoBacktracking R p.2.1 i} at hmean1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmean1
  rw [hfac, hone, hmean, hmean1]
  ring


end EinsteinRelation.Regeneration
