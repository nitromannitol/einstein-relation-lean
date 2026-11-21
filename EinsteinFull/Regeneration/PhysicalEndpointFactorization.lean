import EinsteinFull.Regeneration.PhysicalEndpointRestart
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion
import EinsteinRelation.Regeneration.EndpointBallVolume

/-!
# The regeneration factorization with the last bridge displacement

GMP 2012, Theorem 5.6, and Shen 2003, Theorem 2.5: the cycle variables contain the displacement
`X(τ₁) − X(0)`, which includes the displacement over the last bridge `[τ₁ − λ⁻², τ₁]`. On a
slice `τ₁ = nλ⁻²`, the future after `τ₁` is independent of the past through `(n − 1)λ⁻²`
together with the bridge displacement: the factorization of the source (paper
`app:factorization`, Step 3) integrates the uniform endpoint `y`, and a function of `y − z`,
`z` the position at the start of the bridge, is part of the past factor for each fixed `y`.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

namespace EinsteinFull.Blueprint

/-- The supplied physical path laws are invariant under recentering at almost every shift. -/
theorem physical_path_recenter_covariance {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)),
      (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p := by
  have hall := c6_s3_all_start_recenter_of_requested_identification_phys
    (fun hd Λ hΛ ω hω lam h0 h1 r I =>
      EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I)
    d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  filter_upwards [hall] with a ha
  constructor
  · filter_upwards [ha] with η hη
    exact hη 0
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae ha] with p hp
    exact hp p.1

open Classical in
/-- The factorization at a first regeneration slice with a factor of the last bridge
displacement: for nonnegative bounded tests `H` of the history through `mλ⁻²`, `g` of the
displacement over `[mλ⁻², (m + 1)λ⁻²]` and `Φ` of the record at the regeneration time,
the slice integral of `H · g · Φ` factors into the slice integral of `H · g` and the conditioned
mean of `Φ` at time zero. -/
theorem physical_slice_factorization_endpoint
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (hfuture : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (hslices : node_app_u3A_factorization_u23_slicesStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) (hΦ0 : ∀ r, 0 ≤ Φ r) :
    (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
        q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
        Φ (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 q)
        ∂annealedCoupledLaw Q.measure K) =
      (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) ∂annealedCoupledLaw Q.measure K) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hR : 0 < l / lam := div_pos hl h₀
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h₀
  have hR0 : volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0) ≠ ⊤ :=
    endpointBall_volume_ne_top _ _ hR 0
  have hRpos : volume (endpointBall (Renewal.forceCoord hd) (l / lam) 0) ≠ 0 :=
    (endpointBall_volume_pos _ _ hR 0).ne'
  have hP := physical_path_recenter_covariance hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
  have : IsProbabilityMeasure (annealedCoupledLaw Q.measure K) :=
    annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have : IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK.1 hD) :=
    ProbabilityTheory.cond_isProbabilityMeasure hD
  let A : Vec d → FieldPair d → ℝ := fun y ω =>
    ∫ z, ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd)
      m).indicator H) z * g (y - z.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
      (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
        (z.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0) ∂K (0, ω)
  let Hy : Vec d → CoupledSample d → ℝ := fun y z =>
    H z * g (y - z.1 ((m : ℝ≥0) * Renewal.regenDelta lam))
  have hHy : ∀ y, Measurable[finiteHistorySigma (Renewal.regenDelta lam) m] (Hy y) := fun y =>
    hH.mul (hg.comp (measurable_const.sub
      (EinsteinFull.Regeneration.measurable_path_finiteHistorySigma _ m _ le_rfl)))
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨Cg, hCg⟩ := hbg
  have hbHy : ∀ y, BoundedRealTest (Hy y) := fun y => ⟨max CH 0 * max Cg 0, fun z => by
    rw [abs_mul]
    exact mul_le_mul ((hCH _).trans (le_max_left _ _)) ((hCg _).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)⟩
  have hA : ∀ y ω, A y ω = 1 * firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) m K (Hy y) (y, ω) := by
    intro y ω
    rw [one_mul]
    simp only [A, firstSlicePastIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
      (Renewal.forceCoord hd) m
    · simp only [Set.indicator_of_mem hz, Hy]
    · simp only [Set.indicator_of_notMem hz, zero_mul]
  have hper : ∀ Ψ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ, Measurable Ψ →
      BoundedRealTest Ψ → ∀ B : Vec d × FieldPair d → ℝ,
      (∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
        B xω = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ (xω, z) ∂K xω) →
      ∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, A y ω * B (y, ω) ∂Q.measure) =
        (∫ ω, A y ω ∂Q.measure) *
          ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
            ∫ q, Ψ (regenerationRecord hd lam l 0 q)
              ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
    intro Ψ hΨ hbΨ B hBp
    have hBy := Measure.ae_ae_of_ae_prod hBp
    filter_upwards [hBy,
      EndpointAverageTransport.killed_future_eq_shifted_origin_assuming_path_laws_phys
        hd Q lam h₀ h₁ l δ P K hK hP Ψ] with y hy hshift
    have hy' : (fun ω => B (y, ω)) =ᵐ[Q.measure] fun ω =>
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((y, ω), z) ∂K (y, ω) := hy
    have hB0 := hy'.trans hshift
    have hcongr : (fun ω => A y ω * B (y, ω)) =ᵐ[Q.measure] fun ω => A y ω *
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ ((0, translate y ω), z)
          ∂K (0, translate y ω) := hB0.mono fun ω hω => by
      simp only at hω ⊢
      rw [hω]
    rw [integral_congr_ae hcongr]
    by_cases hyi : 10 * (l / lam) ≤ y (Renewal.forceCoord hd)
    · have hfac := sbxS5_firstSlicePast_shiftedOriginFuture_factorization_phys hd Q lam h₀ h₁
        l δ hl hsep hδ₀ hδ₁ P K hK hpast hfuture hD Ψ hΨ hbΨ (fun _ => 1)
        measurable_const m (Hy y) (hHy y) (hbHy y) y hyi
      simp_rw [hA]
      exact hfac
    · have hz := sbxS5_firstSlicePast_zero_phys hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
        hslices (m + 1) (by omega) (Hy y) y (lt_of_not_ge hyi)
      simp only [Nat.add_sub_cancel] at hz
      have hAz : ∀ᵐ ω ∂Q.measure, A y ω = 0 := by
        filter_upwards [hz] with ω hω
        simp only [Pi.zero_apply] at hω
        rw [hA, hω, mul_zero]
      have h1 : (∫ ω, A y ω ∂Q.measure) = 0 :=
        integral_eq_zero_of_ae (hAz.mono fun ω h => by simp only [Pi.zero_apply, h])
      have h2 : (∫ ω, A y ω * ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ
          ((0, translate y ω), z) ∂K (0, translate y ω) ∂Q.measure) = 0 :=
        integral_eq_zero_of_ae (hAz.mono fun ω h => by simp only [Pi.zero_apply, h, zero_mul])
      rw [h1, h2, zero_mul]
  have hver : ∀ Ψ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ, Measurable Ψ →
      BoundedRealTest Ψ → (∀ r, 0 ≤ Ψ r) → ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧
        BoundedRealTest B ∧ (∀ p, 0 ≤ B p) ∧
        ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
          B xω = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ (xω, z) ∂K xω := by
    intro Ψ hΨ hbΨ hΨ0
    obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
      exists_globally_bounded_measurable_killed_future_version Q.measure K hK.1 (l / lam)
        (Renewal.forceCoord hd) Ψ hΨ hbΨ
    refine ⟨fun p => max (B p) 0, hB.max measurable_const,
      ⟨max C 0, fun p => ?_⟩, fun p => le_max_right _ _, ?_⟩
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le_max ((le_abs_self _).trans (hbB p)) le_rfl
    · filter_upwards [hBp] with p hp
      change B p = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ (p, z) ∂K p at hp
      have hnn : 0 ≤ ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) Ψ (p, z) ∂K p := by
        apply integral_nonneg
        intro z
        dsimp only
        unfold killedFutureTest
        split_ifs
        · exact hΨ0 _
        · exact le_rfl
      change max (B p) 0 = _
      rw [hp, max_eq_left hnn]
  have hslice : ∀ Ψ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ, Measurable Ψ →
      BoundedRealTest Ψ → (∀ r, 0 ≤ Ψ r) →
      (∫ q in {q : FieldPair d × CoupledSample d |
          firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
            (Renewal.forceCoord hd) =
            ((((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        H q.2 * g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam) -
          q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam)) *
          Ψ (iteratedRecord (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) 1 q)
          ∂annealedCoupledLaw Q.measure K) =
        (δ / (volume (endpointBall (Renewal.forceCoord hd) (l / lam) (0 : Vec d))).toReal) *
          (∫ y, ∫ ω, A y ω ∂Q.measure) *
          ((annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal *
            ∫ q, Ψ (regenerationRecord hd lam l 0 q)
              ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) := by
    intro Ψ hΨ hbΨ hΨ0
    obtain ⟨B, hB, hbB, hB0, hBp⟩ := hver Ψ hΨ hbΨ hΨ0
    rw [EinsteinFull.Regeneration.firstRegeneration_slice_integral_endpoint_eq_phys hd Q lam
      h₀.le h₁ P K hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ δ (l / lam) hR
      (Renewal.forceCoord hd) hδ₀.le hR0 hRpos hK.2.2.2.2.1 hK.2.2.2.2.2.2.1 Ψ hΨ hbΨ hΨ0
      B hB hbB hB0 hBp m H hH ⟨CH, hCH⟩ hH0 g hg ⟨Cg, hCg⟩ hg0]
    rw [integral_congr_ae (hper Ψ hΨ hbΨ B hBp), integral_mul_const, mul_assoc]
  have hΦs := hslice Φ hΦ hbΦ hΦ0
  have h1s := hslice (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
    (fun _ => zero_le_one)
  have hone : (∫ _q, (1 : ℝ) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) = 1 := by simp
  simp only [mul_one, hone] at h1s
  rw [hΦs, h1s]
  ring

end EinsteinFull.Blueprint
