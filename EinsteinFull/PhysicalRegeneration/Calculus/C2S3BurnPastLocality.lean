import EinsteinFull.Calculus.C2S3BurnPastLocality
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3PastAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C2S3BurnPastLocality`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
open ProbabilityTheory EinsteinRelation.Regeneration.Renewal
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c2_private_c6_s3_coupled_covariance_iterated_of_all_start_recenter`. -/
private theorem c2_private_c6_s3_coupled_covariance_iterated_of_all_start_recenter_phys
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ ω ∂Q.measure,
      (K (a, ω)).map (recenterSample a) = K (0, translate a ω) := by
  have hc := c6_s3_all_start_recenter_covariance d hd Λ₀ r₀ Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK
  have hu := sbxS9_recentered_coupling_laws_eq_of_path_laws_eq_phys
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

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c2_private_c6_s3_coupled_covariance_of_all_start_recenter`. -/
private theorem c2_private_c6_s3_coupled_covariance_of_all_start_recenter_phys
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
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
      let := hω
      exact EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure K (0, ω)
    exact ht.ae ho
  have hiter := c2_private_c6_s3_coupled_covariance_iterated_of_all_start_recenter_phys
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
  have := hprob
  have heq : (L p).map (recenterSample p.1) = L (0, translate p.1 p.2) := by
    have : IsFiniteMeasure ((L p).map (recenterSample p.1)) := by
      rw [hn]
      infer_instance
    exact Measure.ext_of_generateFrom_of_iUnion C (fun _ : ℕ => Set.univ) hgen
      (fun s hs t ht _ => isSetAlgebra_generateSetAlgebra.inter_mem hs ht)
      (by simp only [Set.iUnion_const])
      (fun _ => isSetAlgebra_generateSetAlgebra.univ_mem)
      (fun _ => measure_ne_top _ _) hp
  simpa only [hn, ho] using heq

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c2_private_c6_s3_actual_coupled_covariance`. -/
private theorem c2_private_c6_s3_actual_coupled_covariance_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (Regeneration.recenterSample p.1) = K (0, translate p.1 p.2) := by
  apply c2_private_c6_s3_coupled_covariance_of_all_start_recenter_phys _ hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK
  exact c6_s3_all_start_recenter_of_requested_identification_phys
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
    let := hω
    simp only [B, EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have hBp : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure), B p =
      ∫ z, killedFutureTest R i Φ (p, z) ∂K p := by
    filter_upwards [hK.2] with p hp
    let := hp
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

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c2_private_c6_s3_actual_annealed_no_backtracking_mean`. -/
private theorem c2_private_c6_s3_actual_annealed_no_backtracking_mean_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, killedFutureTest (l / lam) (forceCoord hd) (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
      ∫ ω, ∫ z, killedFutureTest (l / lam) (forceCoord hd) (fun _ => (1 : ℝ))
        ((0, ω), z) ∂K (0, ω) ∂Q.measure :=
  c2_private_c6_s3_annealed_no_backtracking_mean_of_covariance Q K hK.1 (l / lam)
    (forceCoord hd) (c2_private_c6_s3_actual_coupled_covariance_phys hd Q lam h0 h1 l δ
      hl hsep hδ0 hδ1 P K hK)

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c2_private_c6_s3_actual_killed_future_one_mean`. -/
private theorem c2_private_c6_s3_actual_killed_future_one_mean_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure) =
      (Regeneration.annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd R) := by
  have horigin := killed_future_origin_eq_frozen_record_phys hd Q lam h0.le h1 l δ P K hK
    (fun _ => (1 : ℝ)) measurable_const (show BoundedRealTest (fun _ : FutureState d (forceCoord hd) (l / lam) => (1 : ℝ)) from ⟨1, by simp⟩)
  simp only [setIntegral_one_eq_measureReal] at horigin
  filter_upwards [c2_private_c6_s3_actual_annealed_no_backtracking_mean_phys hd Q lam h0 h1 l δ
    hl hsep hδ0 hδ1 P K hK] with y hy
  exact hy.trans horigin

/-- The physical-kernel version of `EinsteinFull.Blueprint.c2_s3_actual_positive_future_mean`. -/
theorem c2_s3_actual_positive_future_mean_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let _Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω) ∂Q.measure) = η := by
  let := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  refine ⟨(Regeneration.annealedCoupledLaw Q.measure K).real (regenerationNoReturn hd (l / lam)), ?_, measureReal_le_one, ?_⟩
  · exact ENNReal.toReal_pos hD (measure_ne_top _ _)
  · exact c2_private_c6_s3_actual_killed_future_one_mean_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK

end EinsteinFull.Blueprint
