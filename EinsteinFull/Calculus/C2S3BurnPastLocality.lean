import EinsteinFull.Calculus.C2S3PastAssembly
import EinsteinFull.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinRelation.Regeneration.EndpointGap
import EinsteinRelation.Regeneration.OneIntervalLocality

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration

theorem c2_s3_burn_past_local_of_requested_locality (requested_s3_past_supplied_stopped_locality : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) (v : ℝ), let R := l / lam
      let i := Renewal.forceCoord hd
      let Δ := Renewal.regenDelta lam
      ∀ (ω ω' : FieldPair d) (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω)) (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω')) (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1) (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y) → (∀ y : Vec d, P (y, ω') = r'.pathLaw y) → (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → ∀ y : Vec d, y i ≤ v → (r.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) = (r'.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R})) (c1_s3_burn_prebridge_prefix_bound : ∀ {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d) (J N k : ℕ) (z : Regeneration.CoupledSample d) (hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k), ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ → z.1 t i ≤ z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + R) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m J N k : ℕ) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (m + k)] H) (hbH : Regeneration.BoundedRealTest H) (y : Vec d) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ A : FieldPair d → ℝ, Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A ∧ (fun ω => ∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator H) z * (if y ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) =ᵐ[Q.measure] A := by
  dsimp only
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  let E : Set (CoupledSample d) := {z | y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))}
  let G := (couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator H
  let F := E.indicator G
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < R := div_pos hl h0
  have hF : Measurable[finiteHistorySigma Δ (m + k)] F :=
    (hH.indicator (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h0 hR m i J N k)).indicator
      (measurableSet_endpointBall_past Δ R i (m + k) y)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [F, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R) → F z = 0 := by
    intro z hz
    by_contra hn
    have he : z ∈ E := by
      by_contra h
      exact hn (Set.indicator_of_notMem h _)
    have hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k := by
      by_contra h
      exact hn (by simp [F, G, he, h])
    apply hz
    intro t ht
    have hp := c1_s3_burn_prebridge_prefix_bound Δ hΔ lam R h0 hR m i J N k z hΓ t ht
    have hball : euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) < R := he
    have hcoord := coordinate_abs_le_euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i
    have habs := (abs_lt.mp (lt_of_le_of_lt hcoord hball)).1
    have hshift : (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i = y i - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + 9 * R) := by simp [unitVector]
    linarith
  obtain ⟨A, hA, hAo⟩ := c2_s3_past_kernel_of_requested_locality
    requested_s3_past_supplied_stopped_locality d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK (m+k) (y i - 7*R) F hF hbF hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAo] with ω hω
  rw [← hω]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change G z * (if z ∈ E then 1 else 0) = F z
  by_cases hz : z ∈ E <;> simp [F, hz]

/-- The literal burn and endpoint test is jointly measurable in the endpoint
and coupled sample. -/
theorem c2_s3_burn_endpoint_test_measurable {d : ℕ} (Δ : ℝ≥0)
    (lam R : ℝ) (m : ℕ) (i : Fin d) (J N k : ℕ) :
    Measurable (fun p : Vec d × CoupledSample d =>
      ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
        (fun _ => (1 : ℝ))) p.2 *
        (if p.1 ∈ endpointBall i R (p.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          then 1 else 0)) := by
  have hE : MeasurableSet {p : Vec d × CoupledSample d |
      p.1 ∈ endpointBall i R (p.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))} :=
    (measurableSet_endpointBall_pair i R).preimage
      (((continuous_eval_const _).measurable.comp measurable_snd.fst).prodMk measurable_fst)
  have hG : Measurable (fun p : Vec d × CoupledSample d =>
      ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
        (fun _ => (1 : ℝ))) p.2) :=
    (measurable_const.indicator
      (coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k)).comp measurable_snd
  have h := hG.indicator hE
  convert h using 1
  funext p
  by_cases hp : p.1 ∈ endpointBall i R (p.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) <;>
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hp, if_true, if_false, mul_one, mul_zero]

/-- A jointly measurable version agrees with the literal weight for all
endpoints on a single origin-environment probability event. -/
theorem c2_s3_burn_endpoint_measurable_version {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N k : ℕ) :
    ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧
      ∀ᵐ ω ∂Q.measure, ∀ y : Vec d,
        A (y, ω) = ∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
          (fun _ => (1 : ℝ))) z *
          (if y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            then 1 else 0) ∂K (0, ω) := by
  let κ : ProbabilityTheory.Kernel (Vec d × FieldPair d) (CoupledSample d) :=
    (Probability.probabilityPart (originCoupledLaw K)).comap Prod.snd measurable_snd
  let F : (Vec d × FieldPair d) × CoupledSample d → ℝ := fun p =>
    ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
      (fun _ => (1 : ℝ))) p.2 *
      (if p.1.1 ∈ endpointBall i R (p.2.1 (((m + k : ℕ) : ℝ≥0) * Δ))
        then 1 else 0)
  have hF : Measurable F :=
    (c2_s3_burn_endpoint_test_measurable Δ lam R m i J N k).comp
      (measurable_fst.fst.prodMk measurable_snd)
  refine ⟨fun p => ∫ z, F (p, z) ∂κ p,
    (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable, ?_⟩
  filter_upwards [hK.1] with ω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  intro y
  change (∫ z, F ((y, ω), z) ∂Probability.probabilityPart (originCoupledLaw K) ω) = _
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
  rfl

/-- The literal endpoint weight lies in the unit interval on the common
origin-environment probability event. -/
theorem c2_s3_burn_endpoint_bounded {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N k : ℕ) :
    ∀ᵐ ω ∂Q.measure, ∀ y : Vec d,
      0 ≤ (∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
        (fun _ => (1 : ℝ))) z *
        (if y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          then 1 else 0) ∂K (0, ω)) ∧
      (∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
        (fun _ => (1 : ℝ))) z *
        (if y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          then 1 else 0) ∂K (0, ω)) ≤ 1 := by
  filter_upwards [hK.1] with ω hp
  let : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  intro y
  let E : Set (CoupledSample d) := {z |
    y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))}
  let B := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  have hE : MeasurableSet E :=
    (measurableSet_endpointBall_pair i R).preimage
      (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
  have hS : MeasurableSet (B ∩ E) :=
    (coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k).inter hE
  have heq : (∫ z, B.indicator (fun _ => (1 : ℝ)) z *
      (if z ∈ E then 1 else 0) ∂K (0, ω)) = (K (0, ω)).real (B ∩ E) := by
    rw [← integral_indicator_one hS]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ B <;> by_cases he : z ∈ E <;> simp [hz, he]
  change 0 ≤ (∫ z, B.indicator (fun _ => (1 : ℝ)) z *
      (if z ∈ E then 1 else 0) ∂K (0, ω)) ∧
    (∫ z, B.indicator (fun _ => (1 : ℝ)) z *
      (if z ∈ E then 1 else 0) ∂K (0, ω)) ≤ 1
  rw [heq]
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩


theorem c2_s3_burn_past_bounded_measurable_version {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K) (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N k : ℕ) : ∃ A : Vec d × FieldPair d → ℝ, Measurable A ∧ (∀ p, 0 ≤ A p ∧ A p ≤ 1) ∧ ∀ᵐ ω ∂Q.measure, ∀ y : Vec d, A (y, ω) = (fun p : Vec d × FieldPair d => ∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator (fun _ => (1 : ℝ))) z * (if p.1 ∈ Regeneration.endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, p.2)) (y, ω) := by
  obtain ⟨A, hA, hAe⟩ := c2_s3_burn_endpoint_measurable_version
    Q K hK Δ lam R m i J N k
  refine ⟨fun p => max 0 (min 1 (A p)),
    measurable_const.max (measurable_const.min hA), ?_, ?_⟩
  · intro p
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · filter_upwards [hAe, c2_s3_burn_endpoint_bounded Q K hK Δ lam R m i J N k] with ω hEq hBounds
    intro y
    have hb : 0 ≤ A (y, ω) ∧ A (y, ω) ≤ 1 := by
      rw [hEq y]
      exact hBounds y
    rw [max_eq_right (le_min (by norm_num) hb.1), min_eq_right hb.2, hEq y]

/-- Endpoint Fubini for the literal Burn prebridge and any bounded measurable
future version. -/
theorem c2_s3_burn_endpoint_average_fubini {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (Δ : ℝ≥0)
    (lam R : ℝ) (hR : 0 < R) (m : ℕ) (i : Fin d) (J N k : ℕ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    (∫ ω, ∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
      (fun _ => (1 : ℝ))) z * endpointAverage i R
      (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, ω))
      ∂K (0, ω) ∂Q.measure) =
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
      ∫ y, ∫ ω, (∫ z, ((couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator
        (fun _ => (1 : ℝ))) z *
        (if y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ)) then 1 else 0)
        ∂K (0, ω)) * B (y, ω) ∂Q.measure := by
  let G : CoupledSample d → ℝ :=
    (couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator (fun _ => 1)
  have hG : Measurable G := measurable_const.indicator
    (coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k)
  have hbG : BoundedRealTest G := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k <;>
      simp [G, hz]
  exact integral_annealed_endpointAverage_fubini Q.measure K hK Δ (m + k) i R hR
    G hG hbG B hB hbB

/-- A finite successor trial has a prestart coordinate at least that of its predecessor. -/
private theorem c2_private_s3_trial_prestart_le_succ {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) (n : ℕ)
    (hfin : Regeneration.trialStartSequence Δ lam R z i (n + 1) ≠ ⊤) :
    z.1 ((Regeneration.trialStartSequence Δ lam R z i n).toNNReal - Δ) i ≤
      z.1 ((Regeneration.trialStartSequence Δ lam R z i (n + 1)).toNNReal - Δ) i := by
  let S := Regeneration.trialStartSequence Δ lam R z i n
  let t := Regeneration.trialFailureTime Δ R z i S
  have ht : t ≠ ⊤ := by
    intro h
    apply hfin
    rw [Regeneration.trialStartSequence, if_pos h]
  have hS : S ≠ ⊤ := by
    intro h
    apply ht
    change Regeneration.trialFailureTime Δ R z i S = ⊤
    rw [Regeneration.trialFailureTime, Regeneration.trialDownwardTime, if_pos h,
      Regeneration.roundUp, if_pos rfl]
  let a := lam * (Regeneration.coordinateMaximum z.1 i t.toNNReal -
    (z.1 t.toNNReal i - z.1 0 i) + R)
  let C := Regeneration.firstSuccessfulCandidate Δ lam R a
    (Regeneration.sampleTimeShift Δ z t.toNNReal) i
  have hform : Regeneration.trialStartSequence Δ lam R z i (n + 1) = t + C + Δ := by
    rw [Regeneration.trialStartSequence, if_neg ht]
  have hC : C ≠ ⊤ := by
    intro h
    apply hfin
    rw [hform, h, add_top, top_add]
  have hSt : S ≤ t := by
    have hdown : S ≤ Regeneration.trialDownwardTime Δ R z i S := by
      rw [Regeneration.trialDownwardTime, if_neg hS]
      exact le_add_of_nonneg_right zero_le
    exact hdown.trans (Regeneration.le_roundUp Δ hΔ _)
  have hpre : S.toNNReal - Δ ≤ t.toNNReal :=
    le_trans tsub_le_self ((ENNReal.toNNReal_le_toNNReal hS ht).mpr hSt)
  have hdisp := Regeneration.displacement_le_coordinateMaximum z.1 i _ _ hpre
  obtain ⟨j, _, hj⟩ := Regeneration.firstSuccessfulCandidate_attained Δ hΔ lam R a
    (Regeneration.sampleTimeShift Δ z t.toNNReal) i hC
  have hjfin : Regeneration.roundedCandidateSequence Δ lam R a
      (Regeneration.sampleTimeShift Δ z t.toNNReal) i j ≠ ⊤ := by
    rw [← hj]
    exact hC
  have hheight := Regeneration.roundedCandidateSequence_height_lower_bound Δ hΔ lam R a
    hlam.ne' hR.le (Regeneration.sampleTimeShift Δ z t.toNNReal) i j hjfin
  rw [← hj] at hheight
  have ha : a / lam = Regeneration.coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R := by
    dsimp [a]
    exact mul_div_cancel_left₀ _ hlam.ne'
  rw [ha] at hheight
  change Regeneration.coordinateMaximum z.1 i t.toNNReal -
      (z.1 t.toNNReal i - z.1 0 i) + R - R / 2 ≤
      z.1 (t.toNNReal + C.toNNReal) i - z.1 (t.toNNReal + 0) i at hheight
  rw [add_zero] at hheight
  rw [hform, ENNReal.toNNReal_add (ENNReal.add_ne_top.mpr ⟨ht, hC⟩)
    ENNReal.coe_ne_top, ENNReal.toNNReal_add ht hC, ENNReal.toNNReal_coe,
    add_tsub_cancel_right]
  linarith

/-- Prestart coordinates increase along any finite stretch of actual trials. -/
private theorem c2_private_s3_trial_prestart_le_add {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : Regeneration.CoupledSample d) (i : Fin d) (J N : ℕ)
    (hfin : Regeneration.trialStartSequence Δ lam R z i (J + N) ≠ ⊤) :
    z.1 ((Regeneration.trialStartSequence Δ lam R z i J).toNNReal - Δ) i ≤
      z.1 ((Regeneration.trialStartSequence Δ lam R z i (J + N)).toNNReal - Δ) i := by
  induction N with
  | zero => simp only [Nat.add_zero, le_refl]
  | succ N ih =>
    have hprev : Regeneration.trialStartSequence Δ lam R z i (J + N) ≠ ⊤ := by
      intro htop
      apply hfin
      have hle := coupling_scope_trial_start_monotone Δ hΔ lam R hlam hR z i
        (Nat.le_succ (J + N))
      rw [htop] at hle
      exact top_le_iff.mp (by simpa only [Nat.add_succ] using hle)
    exact (ih hprev).trans (by
      simpa only [Nat.add_succ] using
        c2_private_s3_trial_prestart_le_succ Δ hΔ lam R hlam hR z i (J + N) hfin)

/-- Burn bounds the entire original path prefix at the selected trial. -/
private theorem c2_private_s3_burn_prebridge_prefix_bound {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) (z : Regeneration.CoupledSample d)
    (hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k) :
    ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ →
      z.1 t i ≤ z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + R := by
  let w := Regeneration.forceSampleBit k
    (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
  change Regeneration.trialStartSequence Δ lam R w i (J + N) = _ ∧
    Regeneration.trialStartSequence Δ lam R w i J ≠ ⊤ ∧ _ at hz
  have hn : Regeneration.trialStartSequence Δ lam R w i (J + N) ≠ ⊤ := by
    rw [hz.1]
    exact ENNReal.coe_ne_top
  have htime : (Regeneration.trialStartSequence Δ lam R w i (J + N)).toNNReal - Δ =
      (k : ℝ≥0) * Δ := by
    rw [hz.1, ENNReal.toNNReal_coe, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      add_tsub_cancel_right]
  have hlevels := c2_private_s3_trial_prestart_le_add Δ hΔ lam R hlam hR w i J N hn
  rw [htime] at hlevels
  change z.1 ((m : ℝ≥0) * Δ +
      ((Regeneration.trialStartSequence Δ lam R w i J).toNNReal - Δ)) i ≤
        z.1 ((m : ℝ≥0) * Δ + (k : ℝ≥0) * Δ) i at hlevels
  have hslack := Regeneration.trial_prestart_maximum_slack Δ hΔ lam R hlam hR w i (J + N) hn
  rw [htime] at hslack
  change Regeneration.coordinateMaximum
    (Regeneration.pathTimeShift z.1 ((m : ℝ≥0) * Δ)) i ((k : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (k : ℝ≥0) * Δ) i -
        z.1 ((m : ℝ≥0) * Δ + 0) i + R at hslack
  rw [add_zero] at hslack
  have hmax : z.1 0 i + Regeneration.coordinateMaximum z.1 i
      (((m + k : ℕ) : ℝ≥0) * Δ) ≤
      z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + R := by
    rw [Nat.cast_add, add_mul, Regeneration.coordinateMaximum_add, add_max]
    apply max_le
    · linarith [hz.2.2, hlevels]
    · linarith
  intro t ht
  have hdisp := Regeneration.displacement_le_coordinateMaximum z.1 i t _ ht
  linarith


/-- The Burn past weight has the requested local version at every endpoint. -/
@[nolint unusedArguments]
theorem c2_s3_actual_uniform_burn_past_of_requested_locality (requested_s3_past_supplied_stopped_locality : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K) (v : ℝ), let R := l / lam
      let i := Renewal.forceCoord hd
      let Δ := Renewal.regenDelta lam
      ∀ (ω ω' : FieldPair d) (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω)) (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω')) (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1) (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y) → (∀ y : Vec d, P (y, ω') = r'.pathLaw y) → (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → ∀ y : Vec d, y i ≤ v → (r.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) = (r'.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R})) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : ∀ m J N k : ℕ,
      ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
          y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
        (fun ω => ∫ z, ((couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ))) z *
          (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
            (z.1 (((m + k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then 1 else 0)
          ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro m J N k
  apply Filter.Eventually.of_forall
  intro y
  exact c2_s3_burn_past_local_of_requested_locality
    requested_s3_past_supplied_stopped_locality c2_private_s3_burn_prebridge_prefix_bound
    hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK m J N k (fun _ => 1)
    measurable_const ⟨1, by intro z; simp⟩ y

open ProbabilityTheory EinsteinRelation.Regeneration.Renewal

/-- The actual coupling inherits recentering on almost every spatial fibre. -/
private theorem c2_private_c6_s3_coupled_covariance_iterated_of_all_start_recenter
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂Q.measure,
      (K (a, ω)).map (recenterSample a) = K (0, translate a ω) := by
  have hc := c6_s3_all_start_recenter_covariance d hd Λ₀ r₀ Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK
  have hu := sbxS9_recentered_coupling_laws_eq_of_path_laws_eq
    hd Q lam h0 h1 l δ hl P K hK
  filter_upwards [hc, hu] with a hc hu
  have hp : (∀ᵐ ω ∂Q.measure, P (0, ω) = sbxS9RecenteredPathLaws P a (0, ω)) ∧
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        P p = sbxS9RecenteredPathLaws P a p := by
    constructor
    · filter_upwards [hc] with ω hω
      exact hω 0
    · filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure (Vec d))) (ν := Q.measure)).ae hc] with p hp
      exact hp p.1
  have hk := (hu hp).1
  have ht : MeasurePreserving (translate a) Q.measure Q.measure :=
    ⟨EinsteinRelation.Probability.measurable_translate a, Q.stationary a⟩
  filter_upwards [ht.quasiMeasurePreserving.ae hk] with ω hω
  rw [sbxS9RecenteredCoupledLaws_apply, sbxS9RecenterInput,
    add_zero, translate_add, neg_add_cancel, translate_zero] at hω
  exact hω.symm

/-- The actual complete coupled law is covariant for product-almost every fibre. -/
private theorem c2_private_c6_s3_coupled_covariance_of_all_start_recenter
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2) := by
  let L := EinsteinRelation.Probability.probabilityPart K
  let C := generateSetAlgebra (MeasurableSpace.countableGeneratingSet (CoupledSample d))
  have hC : C.Countable := countable_generateSetAlgebra
    MeasurableSpace.countable_countableGeneratingSet
  have hgen : (inferInstance : MeasurableSpace (CoupledSample d)) =
      MeasurableSpace.generateFrom C := by
    simp only [C, generateFrom_generateSetAlgebra_eq,
      MeasurableSpace.generateFrom_countableGeneratingSet]
  have hleft : Measurable (fun p : Vec d × FieldPair d =>
      (L p).map (recenterSample p.1)) := by
    exact sbxS9_measurable_parameter_map L
      (fun q => recenterSample q.1.1 q.2)
      (measurable_recenterSample.comp (measurable_fst.fst.prodMk measurable_snd))
  have hright : Measurable (fun p : Vec d × FieldPair d => L (0, translate p.1 p.2)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    exact (L.measurable_coe hs).comp
      (measurable_const.prodMk EinsteinRelation.Probability.continuous_translate.measurable)
  have ht : Measure.QuasiMeasurePreserving (fun p : Vec d × FieldPair d => translate p.1 p.2)
      ((volume : Measure (Vec d)).prod Q.measure) Q.measure :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_right
      EinsteinRelation.Probability.continuous_translate.measurable
      (Filter.Eventually.of_forall fun a =>
        (measurePreserving_translate Q.measure Q.stationary a).quasiMeasurePreserving)
  have hnorm : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), L p = K p :=
    EinsteinRelation.Probability.probabilityPart_ae_eq _ K hK.1.2
  have horigin : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      L (0, translate p.1 p.2) = K (0, translate p.1 p.2) := by
    have ho : ∀ᵐ ω ∂Q.measure, L (0, ω) = K (0, ω) := by
      filter_upwards [hK.1.1] with ω hω
      letI := hω
      exact EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure K (0, ω)
    exact ht.ae ho
  have hiter := c2_private_c6_s3_coupled_covariance_iterated_of_all_start_recenter
    c6_s3_all_start_recenter_covariance hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  have hniter := Measure.ae_ae_of_ae_prod hnorm
  have hoiter := Measure.ae_ae_of_ae_prod horigin
  have hall : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      ∀ s ∈ C, (L p).map (recenterSample p.1) s = L (0, translate p.1 p.2) s := by
    apply (ae_ball_iff hC).mpr
    intro s hs
    have hsm : MeasurableSet s := hgen.ge s (MeasurableSpace.measurableSet_generateFrom hs)
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      ((Measure.measurable_coe hsm).comp hleft)
      ((Measure.measurable_coe hsm).comp hright))).mpr
    filter_upwards [hiter, hniter, hoiter] with a ha hn ho
    filter_upwards [ha, hn, ho] with ω ha hn ho
    change (L (a, ω)).map (recenterSample a) s = L (0, translate a ω) s
    rw [hn, ho, ha]
  filter_upwards [hall, hnorm, horigin, hK.1.2] with p hp hn ho hprob
  haveI := hprob
  have heq : (L p).map (recenterSample p.1) = L (0, translate p.1 p.2) := by
    haveI : IsFiniteMeasure ((L p).map (recenterSample p.1)) := by
      rw [hn]
      infer_instance
    exact Measure.ext_of_generateFrom_of_iUnion C (fun _ : ℕ => Set.univ) hgen
      (fun s hs t ht _ => isSetAlgebra_generateSetAlgebra.inter_mem hs ht)
      (by simp only [Set.iUnion_const])
      (fun _ => isSetAlgebra_generateSetAlgebra.univ_mem)
      (fun _ => measure_ne_top _ _) hp
  simpa only [hn, ho] using heq

/-- The supplied coupled law is spatially covariant on product-almost every fibre. -/
private theorem c2_private_c6_s3_actual_coupled_covariance {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (Regeneration.recenterSample p.1) = K (0, translate p.1 p.2) := by
  apply c2_private_c6_s3_coupled_covariance_of_all_start_recenter _ hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK
  exact c6_s3_all_start_recenter_of_requested_identification
    (fun {d} hd Λ hΛ ω hω lam h0 h1 r I =>
      EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I)

open EinsteinFull.Blueprint.EndpointAverageTransport
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat

/-- Product-a.e. covariance transports the actual annealed killed-future mean. -/
private theorem c2_private_c6_s3_annealed_killed_future_mean_of_covariance {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ)
    (hcov : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω) ∂Q.measure := by
  let B : Vec d × FieldPair d → ℝ := fun p =>
    ∫ z, killedFutureTest R i Φ (p, z) ∂EinsteinRelation.Probability.probabilityPart K p
  have hB : Measurable B := measurable_killed_future_mean K R i Φ hΦ
  have hBo : ∀ᵐ ω ∂Q.measure, B (0, ω) =
      ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω) := by
    filter_upwards [hK.1] with ω hω
    letI := hω
    simp only [B, EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have hBp : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), B p =
      ∫ z, killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hK.2] with p hp
    letI := hp
    simp only [B, EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  filter_upwards [Measure.ae_ae_of_ae_prod hBp, Measure.ae_ae_of_ae_prod hcov] with y hyp hyc
  have ht : ∀ᵐ ω ∂Q.measure, B (0, translate y ω) =
      ∫ z, killedFutureTest R i Φ ((0, translate y ω), z) ∂K (0, translate y ω) :=
    (show MeasurePreserving (translate y) Q.measure Q.measure from
      ⟨EinsteinRelation.Probability.measurable_translate y, Q.stationary y⟩).quasiMeasurePreserving.ae hBo
  have heq : (fun ω => B (y, ω)) =ᵐ[Q.measure] (fun ω => B (0, translate y ω)) := by
    filter_upwards [hyp, hyc, ht] with ω hω hcω htω
    have hmrec : Measurable (recenterSample y) :=
      measurable_recenterSample.comp (measurable_const.prodMk measurable_id)
    have hmtest : Measurable (fun z => killedFutureTest R i Φ ((0, translate y ω), z)) :=
      (measurable_killedFutureTest R i Φ hΦ).comp (measurable_const.prodMk measurable_id)
    rw [hω, htω, ← hcω, integral_map hmrec.aemeasurable hmtest.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (killedFutureTest_recenter_origin R i Φ y ω z).symm)
  calc
    _ = ∫ ω, B (y, ω) ∂Q.measure := (integral_congr_ae hyp).symm
    _ = ∫ ω, B (0, translate y ω) ∂Q.measure := integral_congr_ae heq
    _ = ∫ ω, B (0, ω) ∂Q.measure :=
      EinsteinRelation.Probability.integral_translate Q.measure Q.stationary y _
        (hB.comp measurable_prodMk_left)
    _ = _ := integral_congr_ae hBo

/-- In particular, the actual annealed no-backtracking mean is spatially constant. -/
private theorem c2_private_c6_s3_annealed_no_backtracking_mean_of_covariance {d : ℕ}
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (R : ℝ) (i : Fin d)
    (hcov : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest R i (fun _ => (1 : ℝ)) ((y, ω), z)
        ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest R i (fun _ => (1 : ℝ)) ((0, ω), z)
        ∂K (0, ω) ∂Q.measure :=
  c2_private_c6_s3_annealed_killed_future_mean_of_covariance Q K hK R i (fun _ => 1)
    measurable_const hcov

/-- The actual annealed no-backtracking mean is spatially constant. -/
private theorem c2_private_c6_s3_actual_annealed_no_backtracking_mean {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest (l / lam) (forceCoord hd) (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (forceCoord hd) (fun _ => (1 : ℝ))
        ((0, ω), z) ∂K (0, ω) ∂Q.measure :=
  c2_private_c6_s3_annealed_no_backtracking_mean_of_covariance Q K hK.1 (l / lam)
    (forceCoord hd) (c2_private_c6_s3_actual_coupled_covariance hd Q lam h0 h1 l δ
      hl hsep hδ0 hδ1 P K hK)

/-- The spatially averaged killed-one mean is the actual annealed no-return mass. -/
private theorem c2_private_c6_s3_actual_killed_future_one_mean {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
      (Regeneration.annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd R) := by
  have horigin := killed_future_origin_eq_frozen_record hd Q lam h0.le h1 l δ P K hK
    (fun _ => (1 : ℝ)) measurable_const (show BoundedRealTest (fun _ : FutureState d (forceCoord hd) (l / lam) => (1 : ℝ)) from ⟨1, by simp⟩)
  simp only [setIntegral_one_eq_measureReal] at horigin
  filter_upwards [c2_private_c6_s3_actual_annealed_no_backtracking_mean hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK] with y hy
  exact hy.trans horigin


/-- The actual killed-future mean is a positive probability, uniformly in space. -/
theorem c2_s3_actual_positive_future_mean {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω) ∂Q.measure) = η := by
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  refine ⟨(Regeneration.annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd (l / lam)), ?_, measureReal_le_one, ?_⟩
  · exact ENNReal.toReal_pos hD (measure_ne_top _ _)
  · exact c2_private_c6_s3_actual_killed_future_one_mean hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK

/-- The frozen past-kernel input gives the actual burn-past local version. -/
@[nolint unusedArguments]
theorem c2_s3_actual_burn_past_of_past_kernel (hPastKernel : node_app_u3A_factorization_u23_past_u2D_kernelStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : ∀ m J N k : ℕ,
      ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
          y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
        (fun ω => ∫ z, ((couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ))) z *
          (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
            (z.1 (((m + k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then 1 else 0)
          ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro m J N k
  apply Filter.Eventually.of_forall
  intro y
  let H : CoupledSample d → ℝ := fun _ => 1
  have hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (m + k)] H := measurable_const
  have hbH : BoundedRealTest H := ⟨1, by intro z; simp [H]⟩
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  let E : Set (CoupledSample d) := {z | y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))}
  let G := (couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator H
  let F := E.indicator G
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < R := div_pos hl h0
  have hF : Measurable[finiteHistorySigma Δ (m + k)] F :=
    (hH.indicator (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h0 hR m i J N k)).indicator
      (measurableSet_endpointBall_past Δ R i (m + k) y)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [F, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R) → F z = 0 := by
    intro z hz
    by_contra hn
    have he : z ∈ E := by
      by_contra h
      exact hn (Set.indicator_of_notMem h _)
    have hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k := by
      by_contra h
      exact hn (by simp [F, G, he, h])
    apply hz
    intro t ht
    have hp := c2_private_s3_burn_prebridge_prefix_bound Δ hΔ lam R h0 hR m i J N k z hΓ t ht
    have hball : euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) < R := he
    have hcoord := coordinate_abs_le_euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i
    have habs := (abs_lt.mp (lt_of_le_of_lt hcoord hball)).1
    have hshift : (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i = y i - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + 9 * R) := by simp [unitVector]
    linarith
  obtain ⟨A, hA, hAo⟩ := hPastKernel d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK (m+k) (y i - 7*R) F hF hbF hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAo] with ω hω
  rw [← hω]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change G z * (if z ∈ E then 1 else 0) = F z
  by_cases hz : z ∈ E <;> simp [F, hz]


/-- Burn bounds the original path prefix at the selected trial. -/
theorem c2_s3_burn_prebridge_prefix_support {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (J N k : ℕ) (z : Regeneration.CoupledSample d)
    (hz : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k) :
    ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ →
      z.1 t i ≤ z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + R := by
  exact c2_private_s3_burn_prebridge_prefix_bound Δ hΔ lam R hlam hR m i J N k z hz



/-- A bounded local version of the burn-past endpoint weight. -/
theorem c2_s3_bounded_burn_past_of_past_kernel (hPastKernel : node_app_u3A_factorization_u23_past_u2D_kernelStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : ∀ m J N k : ℕ,
      ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
          y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧ (∀ ω, 0 ≤ A ω ∧ A ω ≤ 1) ∧
        (fun ω => ∫ z, ((couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ))) z *
          (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
            (z.1 (((m + k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then 1 else 0)
          ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro m J N k
  filter_upwards [c2_s3_actual_burn_past_of_past_kernel hPastKernel hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD m J N k] with y hy
  obtain ⟨A, hA, hEq⟩ := hy
  refine ⟨fun ω => max 0 (min 1 (A ω)), measurable_const.max (measurable_const.min hA), ?_, ?_⟩
  · intro ω
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · filter_upwards [hEq, c2_s3_burn_endpoint_bounded Q K hK.1 (Regeneration.Renewal.regenDelta lam) lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k] with ω he hb
    have hbounds : 0 ≤ A ω ∧ A ω ≤ 1 := by
      rw [← he]
      exact hb y
    rw [max_eq_right (le_min (by norm_num) hbounds.1), min_eq_right hbounds.2]
    exact he

/-- The actual burn prebridge indicator is integrable under the annealed law. -/
@[nolint unusedArguments]
theorem c2_s3_actual_burn_indicator_integrable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m J N k : ℕ) : Integrable (fun q : FieldPair d × Regeneration.CoupledSample d => (couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam) lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) q.2) (Regeneration.annealedCoupledLaw Q.measure K) := by
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hmeas := (coupling_scope_measurableSet_trial_burn_prebridge
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) m
    (Regeneration.Renewal.forceCoord hd) J N k).preimage
      (measurable_snd : Measurable (Prod.snd : FieldPair d × Regeneration.CoupledSample d → _))
  convert (integrable_const (μ := Regeneration.annealedCoupledLaw Q.measure K) (1 : ℝ)).indicator hmeas using 1
  funext q
  simp only [Set.indicator_apply, Set.mem_preimage]


/-- Stable actual-law integrability interface for endpoint Fubini. -/
theorem c2_s3_actual_burn_indicator_integrable_checked {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m J N k : ℕ) : Integrable (fun q : FieldPair d × Regeneration.CoupledSample d => (couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam) lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) q.2) (Regeneration.annealedCoupledLaw Q.measure K) := by
  exact c2_s3_actual_burn_indicator_integrable hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK m J N k

end EinsteinFull.Blueprint
