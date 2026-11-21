import EinsteinFull.Calculus.C14S3BurnContraction
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C14S3BurnContraction`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_burn_success_mass_endpoint_kernel`. -/
theorem c14_s3_burn_success_mass_endpoint_kernel_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K) (m J N k : ℕ) :
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
    coupling_scope_burn_success_integrable_history_endpoint_kernel_phys hd Q lam h₀ h₁ l δ hl P K hK m J N k
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

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_burn_success_lower_of_integrated_endpoint`. -/
theorem c14_s3_burn_success_lower_of_integrated_endpoint_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
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
    c14_s3_burn_success_mass_endpoint_kernel_phys hd Q lam h₀ h₁ l δ hl P K hK m J N k
  have h := hlower B hB hbB hBp
  rw [← hmass] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (mul_nonneg hδ hη), ofReal_measureReal (measure_ne_top μ _),
    ofReal_measureReal (measure_ne_top μ _)] at h'
  exact h'

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_burn_success_lower_of_iterated_endpoint`. -/
theorem c14_s3_burn_success_lower_of_iterated_endpoint_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
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
  apply c14_s3_burn_success_lower_of_integrated_endpoint_phys hd Q lam h₀ h₁ l δ hl hδ P K hK m J N k η hη
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

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c14_s3_uniform_prebridge_win_of_iterated_endpoint`. -/
theorem c14_s3_uniform_prebridge_win_of_iterated_endpoint_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hδ : 0 ≤ δ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K)
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
  exact c14_s3_burn_success_lower_of_iterated_endpoint_phys hd Q lam h₀ h₁ l δ hl
    hδ P K hK m J N k η hη.le (hlower m J N k)

end EinsteinFull.Blueprint
