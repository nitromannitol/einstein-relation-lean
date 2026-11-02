import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Integrated success estimates on the literal entry slices give a contraction
of the Burn-selected failed prefix. -/
theorem c14_s3_burn_contraction_of_integrated_slices {d : ℕ}
    (μ : Measure (FieldPair d × Regeneration.CoupledSample d)) [IsProbabilityMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N : ℕ)
    (hentry : ∀ᵐ q ∂μ, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hlower : ∀ k : ℕ,
      let S := couplingScopeTrialLost Δ lam R m i J N ∩
        {q | Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
            ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
      ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
          (Regeneration.trialStartSequence Δ lam R
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤})) :
    μ (couplingScopeTrialLost Δ lam R m i J (N + 1)) ≤
      ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam R m i J N) := by
  have hw : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hF : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤} :=
    measurableSet_eq_fun ((Regeneration.measurable_trialFailureTime Δ R i).comp
      (((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw).prodMk hw))
      measurable_const
  have hsuccess := coupling_scope_trial_lost_success_bound_of_slice_estimates
    μ Δ hΔ lam R m i J N hentry η hη hlower
  have h := ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
    μ (couplingScopeTrialLost Δ lam R m i J N) _ hF η hη1 hsuccess
  rw [coupling_scope_trial_lost_succ]
  exact h


/-- An integrated success estimate on the prebridge implies the corresponding
success estimate on the actual trial-entry slice. -/
theorem c14_s3_slice_success_of_integrated_prebridge {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (m : ℕ) (i : Fin d)
    (J N k : ℕ) (η : ℝ)
    (hwin : let μ := Regeneration.annealedCoupledLaw Q K
      let A := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
      let B := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
      ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ B)) :
    let μ := Regeneration.annealedCoupledLaw Q K
    let S := couplingScopeTrialLost Δ lam R m i J N ∩
      {q | Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
          ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
    ENNReal.ofReal η * μ S ≤ μ (S ∩ {q | Regeneration.trialFailureTime Δ R
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N)) = ⊤}) := by
  let μ := Regeneration.annealedCoupledLaw Q K
  let A := {q : FieldPair d × Regeneration.CoupledSample d |
    q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let S := couplingScopeTrialLost Δ lam R m i J N ∩
    {q : FieldPair d × Regeneration.CoupledSample d |
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (J + N) =
          ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let G := {q : FieldPair d × Regeneration.CoupledSample d |
    Regeneration.NoBacktracking R (Regeneration.pathTimeShift
      (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let B := {q : FieldPair d × Regeneration.CoupledSample d | q.2.2 (m + k) = true} ∩ G
  have hmass : μ S = ENNReal.ofReal δ * μ A :=
    coupling_scope_measure_trial_lost_slice_fresh_bit
      Q K hK Δ hΔ δ hδ hFresh lam R hlam hR m i J N k
  have heq : A ∩ B = S ∩ G := by
    have hs : S = A ∩ {q | q.2.2 (m + k) = true} :=
      (coupling_scope_trial_burn_prebridge_slice_eq Δ hΔ lam R m i J N k).symm
    rw [hs]
    exact (Set.inter_assoc _ _ _).symm
  change ENNReal.ofReal η * μ S ≤ _
  calc
    ENNReal.ofReal η * μ S = ENNReal.ofReal (δ * η) * μ A := by
      rw [hmass, ENNReal.ofReal_mul hδ]
      ac_rfl
    _ ≤ μ (A ∩ B) := hwin
    _ = μ (S ∩ G) := by rw [heq]
    _ ≤ _ := by
      apply measure_mono
      rintro q ⟨hq, hqG⟩
      refine ⟨hq, ?_⟩
      apply (Regeneration.trialFailureTime_eq_top_iff_noBacktracking Δ R _ i _ ?_).mpr
      · rw [hq.2, ENNReal.toNNReal_coe]
        exact hqG
      · rw [hq.2]
        exact ENNReal.coe_ne_top


/-- A uniform integrated prebridge success bound gives a uniform Burn
contraction once the trial entries are finite. -/
theorem c14_s3_uniform_burn_contraction_of_integrated_prebridge {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : Regeneration.HasFreshBits Q Δ δ K)
    (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (hentry : ∀ m : ℕ, ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q K, ∀ n,
      Regeneration.trialFailureTime Δ R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i
        (Regeneration.trialStartSequence Δ lam R
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n) ≠ ⊤ →
      Regeneration.trialStartSequence Δ lam R
        (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i (n + 1) ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hwin : ∀ m J N k : ℕ,
      let μ := Regeneration.annealedCoupledLaw Q K
      let A := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
      let B := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
      ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ B)) :
    ∃ η : ℝ, 0 < η ∧ ∀ m J N : ℕ,
      Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J (N + 1)) ≤
        ENNReal.ofReal (1 - η) *
          Regeneration.annealedCoupledLaw Q K (couplingScopeTrialLost Δ lam R m i J N) := by
  let : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  refine ⟨η, hη, ?_⟩
  intro m J N
  apply c14_s3_burn_contraction_of_integrated_slices
    (Regeneration.annealedCoupledLaw Q K) Δ hΔ lam R m i J N (hentry m) η hη.le hη1
  intro k
  exact c14_s3_slice_success_of_integrated_prebridge Q K hK Δ hΔ δ hδ hFresh
    lam R hlam hR m i J N k η (hwin m J N k)


/-- The actual Burn success mass is the integral of its restarted endpoint
kernel over the prebridge. -/
theorem c14_s3_burn_success_mass_endpoint_kernel {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K) (m J N k : ℕ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let A := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
    let S := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ Regeneration.BoundedRealTest B ∧
      (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
        B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) ∧
      μ.real (A ∩ S) = ∫ q in A, δ * Regeneration.endpointAverage i R
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) ∂μ := by
  classical
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let A : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
  let S : Set (FieldPair d × Regeneration.CoupledSample d) :=
    {q | q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
      (Regeneration.pathTimeShift (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
        (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
  let H := couplingScopeAnnealedHistory (d := d) Δ (m + k)
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < R := div_pos hl h₀
  have hH := coupling_scope_annealed_history_le (d := d) Δ (m + k)
  have hA : MeasurableSet[H] A :=
    (coupling_scope_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h₀ hR m i J N k).preimage (Measurable.of_comap_le le_rfl)
  have hshift : @Measurable (FieldPair d × Regeneration.CoupledSample d)
      (Regeneration.CoupledSample d) (MeasurableSpace.prod inferInstance inferInstance)
      inferInstance (fun q =>
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_snd)
  have hS : @MeasurableSet (FieldPair d × Regeneration.CoupledSample d)
      (MeasurableSpace.prod inferInstance inferInstance) S :=
    (measurableSet_eq_fun ((measurable_pi_apply (m + k)).comp measurable_snd.snd)
      measurable_const).inter ((Regeneration.measurableSet_NoBacktracking R i).preimage
        (Probability.continuous_path_time_shift.measurable.comp
          (measurable_const.prodMk hshift.fst)))
  obtain ⟨B, hB, hbB, hBp, hkernel⟩ :=
    coupling_scope_burn_success_integrable_history_endpoint_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k
  refine ⟨B, hB, hbB, hBp, ?_⟩
  have hg := (coupling_scope_endpoint_kernel_integrable Q.measure K hK.1
    i R hR (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB).2
  have hk := hkernel (fun _ => 1) (integrable_const 1) (aestronglyMeasurable_const)
  calc
    μ.real (A ∩ S) = ∫ q in A, S.indicator (fun _ => (1 : ℝ)) q ∂μ := by
      rw [setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
    _ = ∫ q in A, (μ[fun q => δ * Regeneration.endpointAverage i R
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) | H]) q ∂μ := by
      simpa only [one_mul] using hk
    _ = ∫ q in A, δ * Regeneration.endpointAverage i R
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) ∂μ :=
      setIntegral_condExp hH hg hA


/-- An integrated endpoint-kernel lower bound gives the Burn success-mass
bound, without requiring pointwise conditional positivity. -/
theorem c14_s3_burn_success_lower_of_integrated_endpoint {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hlower :
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let μ := Regeneration.annealedCoupledLaw Q.measure K
      let A := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
      ∀ B : Vec d × FieldPair d → ℝ, Measurable B → Regeneration.BoundedRealTest B →
        (∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) →
        δ * η * μ.real A ≤ ∫ q in A, δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) ∂μ) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let A := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
    let S := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
    ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ S) := by
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  obtain ⟨B, hB, hbB, hBp, hmass⟩ :=
    c14_s3_burn_success_mass_endpoint_kernel hd Q lam h₀ h₁ l δ hl P K hK m J N k
  have h := hlower B hB hbB hBp
  rw [← hmass] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (mul_nonneg hδ hη), ofReal_measureReal (measure_ne_top μ _),
    ofReal_measureReal (measure_ne_top μ _)] at h'
  exact h'


/-- The measurable version of the killed-future kernel may be replaced by
its actual quenched integral inside the moving endpoint average. -/
theorem c14_s3_endpoint_average_kernel_version_ae {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K) (i : Fin d) (R : ℝ)
    (t : ℝ≥0) (B : Vec d × FieldPair d → ℝ)
    (hBp : ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      B p = ∫ z, Regeneration.killedFutureTest R i (fun _ => 1) (p, z) ∂K p) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      Regeneration.endpointAverage i R (q.2.1 t) (fun y => B (y, q.1)) =
      Regeneration.endpointAverage i R (q.2.1 t)
        (fun y => ∫ z, Regeneration.killedFutureTest R i (fun _ => 1)
          ((y, q.1), z) ∂K (y, q.1)) := by
  have hs := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hBp)
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × Regeneration.CoupledSample d → FieldPair d)
      (Regeneration.annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [sbxS2_map_fst_annealed Q K hK]
  filter_upwards [hqmp.ae hs] with q hq
  unfold Regeneration.endpointAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hq] with y hy
  exact hy

/-- A lower bound for the iterated quenched endpoint integral gives the
integrated prebridge win estimate. -/
theorem c14_s3_burn_success_lower_of_iterated_endpoint {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (m J N k : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hlower :
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      η * (∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
        ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
          Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            (fun y => ∫ w, Regeneration.killedFutureTest R i (fun _ => 1)
              ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let A := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
    let S := {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
        (Regeneration.pathTimeShift
          (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
            (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
    ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ S) := by
  classical
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let C := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  let A : Set (FieldPair d × Regeneration.CoupledSample d) := {q | q.2 ∈ C}
  let : IsProbabilityMeasure μ := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hC : MeasurableSet C := coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k
  have hA : MeasurableSet A := hC.preimage measurable_snd
  apply c14_s3_burn_success_lower_of_integrated_endpoint hd Q lam h₀ h₁ l δ hl hδ P K hK m J N k η hη
  dsimp only
  intro B hB hbB hBp
  have hver := c14_s3_endpoint_average_kernel_version_ae Q K hK.1 i R
    (((m + k : ℕ) : ℝ≥0) * Δ) B hBp
  have hq : ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω),
      Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, ω)) =
      Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
        (fun y => ∫ w, Regeneration.killedFutureTest R i (fun _ => 1)
          ((y, ω), w) ∂K (y, ω)) :=
    Regeneration.ae_quenched_of_annealed Q.measure K hK.1 hver
  have hraw : (∫ ω, ∫ z, C.indicator (fun _ => (1 : ℝ)) z *
      Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure) =
      ∫ ω, ∫ z, C.indicator (fun _ => (1 : ℝ)) z *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => ∫ w, Regeneration.killedFutureTest R i (fun _ => 1)
            ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [hq] with ω hω
    apply integral_congr_ae
    filter_upwards [hω] with z hz
    rw [hz]
  have hmeasure : μ.real A = ∫ ω, ∫ z, C.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure := by
    have hm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
    have hb : Regeneration.BoundedRealTest (A.indicator (fun _ => (1 : ℝ))) :=
      ⟨1, by intro q; by_cases h : q ∈ A <;> simp [h]⟩
    calc
      μ.real A = ∫ q, A.indicator (fun _ => (1 : ℝ)) q ∂μ := by
        rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) (ω, z) ∂K (0, ω) ∂Q.measure :=
        Regeneration.integral_annealedCoupledLaw Q.measure K hK.1 _ hm hb
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ω
        apply integral_congr_ae
        filter_upwards with z
        by_cases h : z ∈ C <;> simp [A, h]
  have hkernel : (∫ q in A, δ * Regeneration.endpointAverage i R
      (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1)) ∂μ) =
      δ * ∫ ω, ∫ z, C.indicator (fun _ => (1 : ℝ)) z *
        Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
          (fun y => B (y, ω)) ∂K (0, ω) ∂Q.measure := by
    rw [← integral_indicator hA]
    have heq := coupling_scope_integral_mul_endpoint_kernel Q.measure K hK.1 i R (div_pos hl h₀)
      (((m + k : ℕ) : ℝ≥0) * Δ) δ B hB hbB
      (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
      ⟨1, by intro q; by_cases h : q ∈ A <;> simp [h]⟩
    have hind : (∫ q, A.indicator (fun q => δ * Regeneration.endpointAverage i R
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1))) q ∂μ) =
        ∫ q, A.indicator (fun _ => (1 : ℝ)) q * (δ * Regeneration.endpointAverage i R
          (q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)) (fun y => B (y, q.1))) ∂μ := by
      apply integral_congr_ae
      filter_upwards with q
      by_cases h : q ∈ A <;> simp [h]
    rw [hind, heq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
  rw [hmeasure, hkernel, hraw]
  nlinarith [mul_le_mul_of_nonneg_left hlower hδ]




/-- A uniform iterated endpoint lower bound yields the uniform prebridge win. -/
theorem c14_s3_uniform_prebridge_win_of_iterated_endpoint {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlower : ∀ m J N k : ℕ,
      let Δ := Regeneration.Renewal.regenDelta lam
      let R := l / lam
      let i := Regeneration.Renewal.forceCoord hd
      let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      η * (∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
        ∫ ω, ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
          Regeneration.endpointAverage i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))
            (fun y => ∫ w, Regeneration.killedFutureTest R i (fun _ => 1)
              ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ m J N k : ℕ,
      let μ := Regeneration.annealedCoupledLaw Q.measure K
      let A := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2 ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k}
      let B := {q : FieldPair d × Regeneration.CoupledSample d |
        q.2.2 (m + k) = true ∧ Regeneration.NoBacktracking R
          (Regeneration.pathTimeShift
            (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1
              (((k + 1 : ℕ) : ℝ≥0) * Δ)) i}
      ENNReal.ofReal (δ * η) * μ A ≤ μ (A ∩ B) := by
  refine ⟨η, hη, hη1, ?_⟩
  intro m J N k
  exact c14_s3_burn_success_lower_of_iterated_endpoint hd Q lam h₀ h₁ l δ hl
    hδ P K hK m J N k η hη.le (hlower m J N k)

end EinsteinFull.Blueprint
