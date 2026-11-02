import EinsteinFull.Blueprint.G1.Proofs.SbxS8FiniteKilledHistorySupport
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.Calculus.C4S3FutureStoppedComparison
import EinsteinFull.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.Calculus.SunaS2SuppliedStoppedLocality
import EinsteinRelation.Regeneration.CoupledEnvironmentRegularity
import EinsteinRelation.Regeneration.FirstIntervalCoupledLaw
import EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Integral

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- Invariance of the actual killed path/coin kernel under conditional
resampling gives scalar local versions by conditional averaging. -/
theorem sbxTakeoverR01_killedPathBit_versions_of_resampling_kernel_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hκeq : ∀ᵐ ω ∂Q,
      ∀ᵐ ω' ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
        sbxS8KilledPathBitKernel R i K ω = sbxS8KilledPathBitKernel R i K ω') :
    HasKilledPathBitFutureVersions Q i R K := by
  intro F hF _hbF
  let f : FieldPair d → ℝ := fun ω => ∫ z, F z ∂sbxS8KilledPathBitKernel R i K ω
  have hf : Measurable f :=
    (hF.stronglyMeasurable.integral_kernel (κ := sbxS8KilledPathBitKernel R i K)).measurable
  have havg : (fun ω => ∫ ω', f ω'
      ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω) =ᵐ[Q] f := by
    filter_upwards [hκeq] with ω hω
    calc
      _ = ∫ _ω', f ω ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω := by
        apply integral_congr_ae
        filter_upwards [hω] with ω' he
        exact congrArg (fun μ : Measure (CoupledSample d) => ∫ z, F z ∂μ) he.symm
      _ = f ω := by simp only [integral_const, probReal_univ, one_smul]
  exact ⟨fun ω => ∫ ω', f ω'
      ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
    hf.stronglyMeasurable.integral_condExpKernel.measurable,
    havg.trans (sbxS8_integral_killedPathBitKernel Q K hK R i F)⟩

/-- For the literal supplied coupling, finite killed histories of the stopped
kernel under conditional resampling suffice. Stopping transport is used only
on the killed measure and on a common a.e. set for both conditional copies. -/
theorem sbxTakeoverR01_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
      ∀ᵐ ω' ∂condExpKernel Q.measure (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
          sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n) :
    HasKilledPathBitFutureVersions Q.measure i R K := by
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hstop := sbxS8_killedPathBitKernel_stopped_of_coupling
    hd Q lam l δ h₀ h₁ P K hK R hR i
  have hcopies : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω,
      sbxS8KilledPathBitKernel R i K ω' =
        (sbxS2StoppedOriginKernel R i K ω').restrict
          {z | NoBacktracking R z.1 i} := by
    have hc : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
        sbxS8KilledPathBitKernel R i K ω' =
          (sbxS2StoppedOriginKernel R i K ω').restrict
            {z | NoBacktracking R z.1 i} := by
      rw [condExpKernel_comp_trim hm]
      exact hstop
    exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc)
  have hall : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω, ∀ n : ℕ,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n := by
    filter_upwards [ae_all_iff.mpr hfinite] with ω hω
    exact ae_all_iff.mpr hω
  apply sbxTakeoverR01_killedPathBit_versions_of_resampling_kernel_eq Q.measure K hK.1 R i
  filter_upwards [hstop, hcopies, hall] with ω hs hc hn
  filter_upwards [hc, hn] with ω' hs' hnn
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω) := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω') := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  rw [hs, hs']
  exact sbxS8_killedMeasure_eq_of_finiteKilledHistory
    (sbxS2StoppedOriginKernel R i K ω) (sbxS2StoppedOriginKernel R i K ω')
    Δ hΔ R i hnn

/-- Conditional averaging promotes individual scalar versions to one finite
kernel version on a common a.e. set. The countable-generation hypothesis is
used only for equality of kernels, not asserted for the raw field record. -/
theorem sbxTakeoverMinimalR01_localKernel_of_versions
    {α β : Type*} [mα : MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsFiniteKernel κ]
    (m : MeasurableSpace α) (hm : m ≤ mα)
    (hlocal : ∀ F : β → ℝ, Measurable F → BoundedRealTest F →
      ∃ A : α → ℝ, Measurable[m] A ∧ A =ᵐ[μ] fun a => ∫ b, F b ∂κ a) :
    ∃ η : @Kernel α β m inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ a ∂μ, κ a = η a := by
  let : MeasurableSpace α := mα
  let η : @Kernel α β m inferInstance := κ ∘ₖ condExpKernel μ m
  let η' : Kernel α β := η.comap id (measurable_id.mono le_rfl hm)
  have heq : ∀ t : Set β, MeasurableSet t →
      (fun a => (κ a).real t) =ᵐ[μ] fun a => (η' a).real t := by
    intro t ht
    have hb : BoundedRealTest (t.indicator fun _ => (1 : ℝ)) := by
      refine ⟨1, fun b => ?_⟩
      by_cases hb : b ∈ t
      · simp only [Set.indicator_of_mem hb, abs_one, le_refl]
      · simp only [Set.indicator_of_notMem hb, abs_zero, zero_le_one]
    obtain ⟨A, hA, hAe⟩ := hlocal (t.indicator fun _ => (1 : ℝ))
      (measurable_const.indicator ht) hb
    simp only [integral_indicator ht, setIntegral_one_eq_measureReal] at hAe
    have hfi := Kernel.IsFiniteKernel.integrable μ κ ht
    have hfm : AEStronglyMeasurable[m] (fun a => (κ a).real t) μ :=
      hA.stronglyMeasurable.aestronglyMeasurable.congr hAe
    have hc := condExp_ae_eq_integral_condExpKernel hm hfi
    have hf := condExp_of_aestronglyMeasurable' hm hfm hfi
    have hi : ∀ a, (η' a).real t =
        ∫ b, (κ b).real t ∂condExpKernel μ m a := by
      intro a
      have hint : Integrable (t.indicator fun _ => (1 : ℝ))
          ((κ ∘ₖ condExpKernel μ m) a) :=
        (integrable_const (1 : ℝ)).indicator ht
      have h := Kernel.integral_comp (η := κ) (κ := condExpKernel μ m) (a := a) hint
      simpa only [η', η, Kernel.comap_apply, id_eq, integral_indicator ht,
        setIntegral_one_eq_measureReal] using h
    filter_upwards [hc, hf] with a ha hfa
    rw [hi, ← ha, hfa]
  have heq' : ∀ t : Set β, MeasurableSet t →
      (fun a => κ a t) =ᵐ[μ] fun a => η' a t := by
    intro t ht
    filter_upwards [heq t ht] with a ha
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (κ a) t)
      (measure_ne_top (η' a) t)).mp ha
  have hprod : μ.compProd κ = μ.compProd η' := by
    apply Measure.ext_prod
    intro s t hs ht
    rw [Measure.compProd_apply_prod hs ht, Measure.compProd_apply_prod hs ht]
    exact setLIntegral_congr_fun_ae hs ((heq' t ht).mono fun _ h _ => h)
  exact ⟨η, inferInstance, Kernel.ae_eq_of_compProd_eq hprod⟩

/-- The existing product-version interface localizes the actual killed
path/coin kernel. The constant environment test is admissible; the supplied
coupling and its literal origin probability fibres are preserved. -/
theorem sbxTakeoverMinimalR01_pathBit_localKernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hfuture : HasFutureHalfSpaceVersions Q i R K) :
    ∃ η : @Kernel (FieldPair d) (CoupledSample d)
        (localSigma {x : Vec d | -2 * R ≤ x i}) inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ ω ∂Q, sbxS8KilledPathBitKernel R i K ω = η ω := by
  let : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  have : IsFiniteKernel (sbxS8KilledPathBitKernel R i K) := by
    unfold sbxS8KilledPathBitKernel
    infer_instance
  apply sbxTakeoverMinimalR01_localKernel_of_versions Q (sbxS8KilledPathBitKernel R i K)
    (localSigma {x : Vec d | -2 * R ≤ x i}) (Probability.localSigma_le_borel _)
  intro F hF hbF
  obtain ⟨A, hA, hAe⟩ := hfuture F (fun _ => 1) hF hbF measurable_const
    ⟨1, fun _ => by simp only [abs_one, le_refl]⟩
  simp only [mul_one] at hAe
  exact ⟨A, hA, hAe.trans (sbxS8_integral_killedPathBitKernel Q K hK R i F).symm⟩

/-- Push the single killed-kernel version through the original joint record.
Equality holds on one origin-a.e. set as measures, simultaneously for every
measurable full-record set. The raw restricted field need not be Polish. -/
theorem sbxTakeoverMinimalR01_jointRecord_localKernel {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hfuture : HasFutureHalfSpaceVersions Q i R K) :
    ∃ ν : @Kernel (FieldPair d) (FutureState d i R)
        (localSigma {x : Vec d | -2 * R ≤ x i}) inferInstance,
      IsFiniteKernel ν ∧ ∀ᵐ ω ∂Q, sbxS2KilledFutureRecordLaw R i K ω = ν ω := by
  obtain ⟨η, hηfinite, hη⟩ :=
    sbxTakeoverMinimalR01_pathBit_localKernel Q K hK R i hfuture
  have := hηfinite
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let recordMap : FieldPair d × CoupledSample d → FutureState d i R :=
    fun p => spatialFutureRecord R i (0, p.1) p.2
  have hrec : @Measurable (FieldPair d × CoupledSample d) (FutureState d i R)
      (m.prod inferInstance) inferInstance recordMap :=
    sbxS8_measurable_originFutureRecord_local R i
  let ν : @Kernel (FieldPair d) (FutureState d i R) m inferInstance :=
    (Kernel.id ×ₖ η).map recordMap
  refine ⟨ν, inferInstance, ?_⟩
  filter_upwards [hη] with ω hω
  have hmrec := sbxS2_measurable_originFutureRecord R i ω
  apply Measure.ext
  intro S hS
  rw [show ν = (Kernel.id ×ₖ η).map recordMap from rfl,
    Kernel.map_apply' _ hrec _ hS, Kernel.id_prod_apply' _ _ (hrec hS), ← hω,
    sbxS2KilledFutureRecordLaw, Measure.map_apply hmrec hS]
  rfl

/-- A single local version of the actual killed path/coin kernel integrates
all original joint future tests. No countable generation of the raw function
field is used, and the same full observable is retained throughout. -/
theorem sbxTakeoverMinimalR01_joint_future_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hfuture : HasFutureHalfSpaceVersions Q i R K)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
      (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q] B := by
  obtain ⟨ν, hνfinite, hν⟩ :=
    sbxTakeoverMinimalR01_jointRecord_localKernel Q K hK R i hfuture
  have := hνfinite
  refine ⟨fun ω => ∫ y, Φ y ∂ν ω,
    (hΦ.stronglyMeasurable.integral_kernel (κ := ν)).measurable, ?_⟩
  filter_upwards [hν, hK.1] with ω hω hp
  have : IsProbabilityMeasure (K (0, ω)) := hp
  rw [← hω, sbxS8_integral_killedFutureRecordLaw K ω R i Φ hΦ]


/-- All-order finite stopped histories imply the original future-kernel node.
The finite-history comparison is an explicit conditional mathematical input. -/
theorem sbxTakeoverMinimalR01_future_kernel_of_finite_histories
    (hfinite :
      ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
        (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
        (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
        (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K),
        ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
          ∀ᵐ ω' ∂condExpKernel Q.measure
            (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Renewal.forceCoord hd)}) ω,
            sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam)
              (Renewal.forceCoord hd) K ω) (Renewal.regenDelta lam) (l / lam)
              (Renewal.forceCoord hd) n =
            sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam)
              (Renewal.forceCoord hd) K ω') (Renewal.regenDelta lam) (l / lam)
              (Renewal.forceCoord hd) n) :
    node_app_u3A_factorization_u23_future_u2D_kernelStmt := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK Φ hΦ _hb
  apply sbxTakeoverMinimalR01_joint_future_versions Q.measure K hK.1 (l / lam)
    (Renewal.forceCoord hd)
  · apply future_product_versions_of_killed_path_bit Q.measure (Renewal.forceCoord hd)
      (l / lam) K
    exact sbxTakeoverR01_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory
      hd Q lam l δ h0.le h1 P K hK (Renewal.regenDelta lam)
      (EinsteinRelation.regenDelta_pos h0) (l / lam) (div_pos hl h0)
      (Renewal.forceCoord hd)
      (hfinite hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK)
  · exact hΦ

/-- Conditional copies share each local observation. This is the
`ConditionalLocalVersions.ae_condExpKernel_observation_eq` argument, kept
independent of its unported local-kernel-version import. -/
theorem sbxTakeoverMinimalR01_resampling_observation_eq {α E : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    (X : α → E) (hX : @Measurable α E m inferInstance X) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, X a = X b := by
  let : MeasurableSpace α := mα
  let : MeasurableSpace (α × α) := m.prod mα
  have hp : @MeasurableSet (α × α) (m.prod mα) {p | X p.1 = X p.2} :=
    measurableSet_eq_fun (hX.comp (@measurable_fst α α m mα))
      ((hX.mono hm le_rfl).comp (@measurable_snd α α m mα))
  have hd : @Measurable α (α × α) mα (m.prod mα) (fun a => (a, a)) :=
    (measurable_id.mono le_rfl hm).prodMk measurable_id
  have hprod : ∀ᵐ p ∂(μ.trim hm).compProd (condExpKernel μ m), X p.1 = X p.2 := by
    rw [compProd_trim_condExpKernel hm]
    exact (ae_map_iff hd.aemeasurable hp).mpr (Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hprod)

/-- All physical observations on the conditioning region agree on one
conditional full-measure set. Continuity extends equality from a countable
dense set; there is no uncountable intersection of full-measure sets. -/
theorem sbxTakeoverMinimalR01_resampling_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d)) :
    ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      ∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y := by
  let : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  obtain ⟨A, hAc, hAd⟩ := TopologicalSpace.exists_countable_dense U
  have : Countable A := hAc.to_subtype
  have hpoints : ∀ a : A, ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω,
      (ω.1 (a : U), ω.2 (a : U)) = (ω'.1 (a : U), ω'.2 (a : U)) := by
    intro a
    exact sbxTakeoverMinimalR01_resampling_observation_eq Q (localSigma U)
      (Probability.localSigma_le_borel U)
      (fun ω : FieldPair d => (ω.1 (a : U), ω.2 (a : U)))
      (Measurable.of_comap_le (le_iSup
        (fun y : U => MeasurableSpace.comap
          (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) (a : U)))
  filter_upwards [ae_all_iff.mpr hpoints] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with ω' hω'
  have hfun : (fun y : U => (ω.1 y, ω.2 y)) = fun y : U => (ω'.1 y, ω'.2 y) := by
    apply Continuous.ext_on hAd
      ((ω.1.continuous.comp continuous_subtype_val).prodMk
        (ω.2.continuous.comp continuous_subtype_val))
      ((ω'.1.continuous.comp continuous_subtype_val).prodMk
        (ω'.2.continuous.comp continuous_subtype_val))
    intro a ha
    exact hω' ⟨a, ha⟩
  intro y hy
  exact Prod.mk.inj (congrFun hfun ⟨y, hy⟩)

/-- The zero-length killed history is the deterministic initial sample. -/
theorem sbxTakeoverMinimalR01_s3_finite_killed_history_zero {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel Q.measure
      (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}) ω,
      sbxS8FiniteKilledHistory
        (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω)
        (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) 0 =
      sbxS8FiniteKilledHistory
        (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω')
        (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) 0 := by
  classical
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let Δ := Regeneration.Renewal.regenDelta lam
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hR : 0 < R := div_pos hl h0
  have hb : sbxS8FutureBarrier Δ R i 0 = Set.univ := by
    ext z
    simp only [sbxS8FutureBarrier, Set.mem_setOf_eq, Set.mem_univ, iff_true, Nat.cast_zero, zero_mul]
    intro t ht
    have : t = 0 := le_antisymm ht zero_le
    subst t
    simp [hR]
  let z0 : CoupledSample d := (ContinuousMap.const ℝ≥0 0, fun _ => false)
  have hf : ∀ᵐ ω ∂Q.measure,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i 0 = Measure.dirac z0 := by
    filter_upwards [hK.1.1, future_locality_ae_starts_at_origin_of_coupling hd Q lam l δ h0.le h1 P K hK] with ω hp hs
    haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [sbxS8FiniteKilledHistory, hb, Measure.restrict_univ,
      sbxS2StoppedOriginKernel, Kernel.map_apply _ (sbxS2_measurable_stopFutureSample R i),
      Probability.probabilityPart_eq_of_isProbabilityMeasure,
      Measure.map_map (sbxS8_measurable_stoppedHistorySample Δ 0) (sbxS2_measurable_stopFutureSample R i)]
    calc
      _ = Measure.map (fun _ : CoupledSample d => z0) (originCoupledLaw K ω) := by
        apply Measure.map_congr
        filter_upwards [hs] with z hz
        apply Prod.ext
        · apply ContinuousMap.ext
          intro t
          simp [Function.comp_def, Probability.stoppedHistorySample, sbxS2StopFutureSample,
            localityStoppedPath_zero, hz, z0]
        · funext k
          simp [Function.comp_def, Probability.stoppedHistorySample, z0]
      _ = Measure.dirac z0 := by simp
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hc : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i 0 = Measure.dirac z0 := by
    rw [condExpKernel_comp_trim hm]
    exact hf
  have hc' := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc)
  filter_upwards [hf, hc'] with ω hω hω'
  filter_upwards [hω'] with ω' hω'
  exact hω.trans hω'.symm
/-- Transport the first coupled history, including either first coin, from
an equality of the supplied stopped path laws. -/
theorem sbxTakeoverMinimalR01_future_first_history_eq_of_stopped_map_eq
    {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (y : Vec d) (ω ω' : FieldPair d) (hy : -R ≤ y i)
    [IsProbabilityMeasure (K (y, ω))] [IsProbabilityMeasure (K (y, ω'))]
    (hstart : ∀ᵐ z ∂K (y, ω), z.1 0 = y)
    (hstart' : ∀ᵐ z ∂K (y, ω'), z.1 0 = y)
    (hone : Regeneration.Renewal.OneIntervalKernelAt Δ δ R i P K (y, ω))
    (hone' : Regeneration.Renewal.OneIntervalKernelAt Δ δ R i P K (y, ω'))
    (hstop : (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (F : Regeneration.CoupledSample d → ℝ)
    (hF : @Measurable (Regeneration.CoupledSample d) ℝ
      (Regeneration.finiteHistorySigma Δ 1) inferInstance F)
    (hb : Regeneration.BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ z.1 t i) :
    (∫ z, F z ∂K (y, ω)) = ∫ z, F z ∂K (y, ω') := by
  let Fb := fun b γ => F (firstBitSample (Diffusion.stopPathAt Δ γ) b)
  have hm : ∀ b, Measurable (Fb b) := fun b =>
    (hF.mono (Probability.finiteHistorySigma_le Δ 1) le_rfl).comp
      ((measurable_id.prodMk measurable_const).comp (Diffusion.continuous_stopPathAt Δ).measurable)
  have hs : ∀ b γ γ', (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → Fb b γ = Fb b γ' := by
    intro b γ γ' hh
    have he : Diffusion.stopPathAt Δ γ = Diffusion.stopPathAt Δ γ' := by
      apply ContinuousMap.ext
      intro t
      exact hh _ (min_le_right _ _)
    exact congrArg (fun q => F (firstBitSample q b)) he
  have hp : ∀ b γ, Fb b γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → -R ≤ γ t i := by
    intro b γ hγ t ht
    have h := hsupport (firstBitSample (Diffusion.stopPathAt Δ γ) b) hγ t ht
    simpa [firstBitSample, Diffusion.stopPathAt, min_eq_left ht] using h
  have hpair := fun b => c4_future_integral_pair_of_stopped_map_eq Δ R hR i P y ω ω' hy
    hstop (Fb b) (hm b) (hs b) (hp b)
  exact integral_first_history_eq_of_oneInterval_integrals Δ δ R i P P K K (y, ω) (y, ω')
    hstart hstart' hone hone' F hF hb (fun b => (hpair b).1) (fun b => (hpair b).2)


/-- Stopped-law locality propagates through every supported coupled history. -/
theorem sbxTakeoverMinimalR01_future_histories_eq_of_stopped_map_eq
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (x : Vec d) (hx : CoupledFibreRegular Δ δ R i P K (x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
    (n : ℕ) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i) :
    (∫ z, F z ∂K (x, ω)) = ∫ z, F z ∂K (x, ω') := by
  apply integral_supported_histories_eq_of_regular_environments hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R i P K ω ω' hg hg' {y | -R ≤ y i}
    (isClosed_le continuous_const (continuous_apply i)) ?_ x hx hx' n hn F hF hb hsupport
  intro y hy hyf hyf' G hG hbG hsG
  obtain ⟨hω, r, hr⟩ := hg.1
  obtain ⟨hω', r', hr'⟩ := hg'.1
  haveI := hyf.1
  haveI := hyf'.1
  have hs := r.pathLaw_starts_at y
  have hs' := r'.pathLaw_starts_at y
  rw [← hr y, ← hyf.2.1] at hs
  rw [← hr' y, ← hyf'.2.1] at hs'
  exact sbxTakeoverMinimalR01_future_first_history_eq_of_stopped_map_eq Δ δ R hR i P K y ω ω' hy
    (ae_of_ae_map measurable_fst.aemeasurable hs)
    (ae_of_ae_map measurable_fst.aemeasurable hs') hyf.2.2.2 hyf'.2.2.2
    (hstop y hy) G hG hbG (by
      simpa only [Probability.historyStays, Set.mem_setOf_eq, Nat.cast_one, one_mul] using hsG)

/-- Finite barrier tests agree under supplied stopped-law locality. -/
theorem sbxTakeoverMinimalR01_future_finite_barrier_eq_of_stopped_map_eq
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (m n : ℕ) (hmn : m ≤ n) (hn : 1 ≤ n) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance F)
    (hb : BoundedRealTest F) :
    (∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0) ∂K (0, ω)) =
    ∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0) ∂K (0, ω') := by
  let G : CoupledSample d → ℝ := fun z =>
    if z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      then F z else 0
  have hzero : @Measurable (CoupledSample d) (Vec d)
      (finiteHistorySigma Δ n) inferInstance (fun z => z.1 0) := by
    have h := ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst).comp
      (Probability.measurable_stoppedHistorySample (d := d) Δ n)
    change @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
      (fun z => (Probability.stoppedHistorySample Δ n z).1 0) at h
    simpa only [Probability.stoppedHistorySample_path Δ n _ 0 zero_le] using h
  have hG : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance G :=
    Measurable.ite ((measurableSet_eq_fun hzero measurable_const).inter
      (measurableSet_noBacktracking_prefix Δ n R i))
      (hF.mono (finiteHistorySigma_mono Δ hmn) le_rfl) measurable_const
  obtain ⟨C, hbC⟩ := hb
  have hbG : BoundedRealTest G := by
    refine ⟨max C 0, fun z => ?_⟩
    dsimp only [G]
    split_ifs
    · exact (hbC z).trans (le_max_left _ _)
    · simpa only [abs_zero] using (le_max_right C 0)
  have hsG : ∀ z, G z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i := by
    intro z hz t ht
    have hzcond : z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ →
        -R < z.1 t i - z.1 0 i := by
      by_contra h
      exact hz (if_neg h)
    have h := hzcond.2 t ht
    rw [hzcond.1] at h
    simpa only [Pi.zero_apply, sub_zero] using h.le
  have hcomp := sbxTakeoverMinimalR01_future_histories_eq_of_stopped_map_eq hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R hR i P K ω ω' hg hg' hstop 0 hg.2.1 hg'.2.1 n hn G hG hbG hsG
  have hchange : ∀ η : FieldPair d,
      CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
      (∫ z, G z ∂K (0, η)) = ∫ z,
        (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
          then F z else 0) ∂K (0, η) := by
    intro η hη
    obtain ⟨_, r, hr⟩ := hη.1
    have hs := r.pathLaw_starts_at 0
    rw [← hr 0, ← hη.2.1.2.1] at hs
    apply integral_congr_ae
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hs] with z hz
    change z.1 0 = 0 at hz
    simp only [G, hz, true_and]
  rw [hchange ω hg, hchange ω' hg'] at hcomp
  exact hcomp

/-- The finite-barrier integral comparison determines the raw finite-history law. -/
theorem sbxTakeoverMinimalR01_future_raw_finite_history_eq_of_stopped_map_eq
    {d : ℕ} (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hstop : ∀ y : Vec d, -R ≤ y i →
      (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) =
      (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}))
    (n : ℕ) (hn : 1 ≤ n) :
    sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
      sbxS8FiniteKilledHistory (K (0, ω')) Δ R i n := by
  letI : IsProbabilityMeasure (K (0, ω)) := hg.2.1.1
  letI : IsProbabilityMeasure (K (0, ω')) := hg'.2.1.1
  apply Measure.ext
  intro E hE
  let A := (Probability.stoppedHistorySample Δ n) ⁻¹' E
  have hA : MeasurableSet[finiteHistorySigma Δ n] A :=
    (Probability.measurable_stoppedHistorySample Δ n) hE
  have hAm : MeasurableSet A := Probability.finiteHistorySigma_le Δ n A hA
  have hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      (A.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hA
  have hb : BoundedRealTest (A.indicator fun _ => (1 : ℝ)) :=
    ⟨1, fun z => by by_cases hz : z ∈ A <;> simp [hz]⟩
  have hint := sbxTakeoverMinimalR01_future_finite_barrier_eq_of_stopped_map_eq hd Λ₀ hΛ₀ lam h0 h1
    Δ hΔ δ R hR i P K ω ω' hg hg' hstop n n le_rfl hn _ hF hb
  have hconv : ∀ μ : Measure (CoupledSample d),
      (∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then (A.indicator fun _ => (1 : ℝ)) z else 0) ∂μ) =
        μ.real (sbxS8FutureBarrier Δ R i n ∩ A) := by
    intro μ
    have he : (fun z : CoupledSample d =>
        if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then (A.indicator fun _ => (1 : ℝ)) z else 0) =
        (sbxS8FutureBarrier Δ R i n ∩ A).indicator fun _ => (1 : ℝ) := by
      funext z
      by_cases hz : ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
      · by_cases ha : z ∈ A
        · rw [if_pos hz, Set.indicator_of_mem ha,
            Set.indicator_of_mem (show z ∈ sbxS8FutureBarrier Δ R i n ∩ A from ⟨hz, ha⟩)]
        · rw [if_pos hz, Set.indicator_of_notMem ha,
            Set.indicator_of_notMem (show z ∉ sbxS8FutureBarrier Δ R i n ∩ A from fun h => ha h.2)]
      · rw [if_neg hz,
          Set.indicator_of_notMem (show z ∉ sbxS8FutureBarrier Δ R i n ∩ A from fun h => hz h.1)]
    rw [he, integral_indicator_const (1 : ℝ)
      ((sbxS8_measurableSet_futureBarrier Δ R i n).inter hAm)]
    simp
  rw [hconv, hconv] at hint
  have heq := (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (K (0, ω)) _)
    (measure_ne_top (K (0, ω')) _)).1 hint
  simp only [sbxS8FiniteKilledHistory, Measure.map_apply
    (sbxS8_measurable_stoppedHistorySample Δ n) hE]
  change (K (0, ω)).restrict (sbxS8FutureBarrier Δ R i n) A =
    (K (0, ω')).restrict (sbxS8FutureBarrier Δ R i n) A
  rw [Measure.restrict_apply hAm, Measure.restrict_apply hAm]
  simpa only [Set.inter_comm] using heq

/-- At the inner finite barrier, stopping at the outer half-space preserves
both the retained path and every retained coin. -/
theorem sbxTakeoverMinimalR01_future_finite_history_stop_transport {d : ℕ}
    (μ : Measure (CoupledSample d)) (Δ : ℝ≥0) (R : ℝ) (hR : 0 < R)
    (i : Fin d) (n : ℕ) (hs : ∀ᵐ z ∂μ, z.1 0 = 0) :
    sbxS8FiniteKilledHistory (μ.map (sbxS2StopFutureSample R i)) Δ R i n =
      sbxS8FiniteKilledHistory μ Δ R i n := by
  let U : Set (Vec d) := {x | -2 * R < x i}
  let V : Set (Vec d) := {x | -R < x i}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_apply i)
  have hVU : V ⊆ U := by
    intro x hx
    change -R < x i at hx
    change -2 * R < x i
    linarith
  have hB := sbxS8_measurableSet_futureBarrier Δ R i n
  have he : (sbxS2StopFutureSample R i) ⁻¹' sbxS8FutureBarrier Δ R i n =ᵐ[μ]
      sbxS8FutureBarrier Δ R i n := by
    filter_upwards [hs] with z hz
    have h := Diffusion.localityStoppedPath_stays_iff U V hU hVU z.1 ((n : ℝ≥0) * Δ)
    simpa only [Set.mem_preimage, sbxS8FutureBarrier, Set.mem_setOf_eq,
      sbxS2StopFutureSample, localityStoppedPath_zero, hz, Pi.zero_apply, sub_zero, U, V] using propext h
  rw [sbxS8FiniteKilledHistory, Measure.restrict_map (sbxS2_measurable_stopFutureSample R i) hB,
    Measure.restrict_congr_set he, Measure.map_map (sbxS8_measurable_stoppedHistorySample Δ n)
      (sbxS2_measurable_stopFutureSample R i), sbxS8FiniteKilledHistory]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem hB, ae_restrict_of_ae hs] with z hz hstart
  have hstay : ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → z.1 t ∈ U := by
    intro t ht
    have h := hz t ht
    rw [hstart] at h
    change -2 * R < z.1 t i
    simp only [Pi.zero_apply, sub_zero] at h
    linarith
  have hexit := Diffusion.lt_localityExitTime_of_stays U hU z.1 ((n : ℝ≥0) * Δ) hstay
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change Diffusion.localityStoppedPath U z.1 (min t ((n : ℝ≥0) * Δ)) =
      z.1 (min t ((n : ℝ≥0) * Δ))
    exact Diffusion.localityStoppedPath_eq_of_le_exit U z.1 _
      ((ENNReal.coe_le_coe.mpr (min_le_right _ _)).trans hexit.le)
  · rfl

/-- Conditional finite-history consumer for the requested stopped locality. -/
theorem sbxTakeoverMinimalR01_s3_finite_killed_history_of_requested_locality (requested_s3_future_supplied_stopped_locality : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (hl : 0 < l) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K), let R := l / lam; let i := Renewal.forceCoord hd; let Δ := Renewal.regenDelta lam; ∀ (ω ω' : FieldPair d) (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω)) (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω')) (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1) (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y) → (∀ y : Vec d, P (y, ω') = r'.pathLaw y) → (∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → ∀ y : Vec d, -R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i})) : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K), ∀ n : ℕ, ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel Q.measure (localSigma {x : Vec d | -2 * (l / lam) ≤ x (Regeneration.Renewal.forceCoord hd)}) ω, sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω) (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) n = sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel (l / lam) (Regeneration.Renewal.forceCoord hd) K ω') (Regeneration.Renewal.regenDelta lam) (l / lam) (Regeneration.Renewal.forceCoord hd) n := by
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl P K hK n
  by_cases hn : n = 0
  · subst n
    exact sbxTakeoverMinimalR01_s3_finite_killed_history_zero hd Q lam h0 h1 l δ hl P K hK
  have hn' : 1 ≤ n := by omega
  let R := l / lam
  let i := Renewal.forceCoord hd
  let Δ := Renewal.regenDelta lam
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hR : 0 < R := div_pos hl h0
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hg := ae_coupledEnvironmentRegular hd Q lam h0.le h1 P K
    hK.1 hK.2.1 hK.2.2.1 Δ hΔ δ R i hK.2.2.2.2.1 hK.2.2.2.2.2.2.2
  have hc0 : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      CoupledEnvironmentRegular hd Λ₀ Q.ellipticity_parameter lam h0.le h1 Δ δ R i P K ω' := by
    rw [condExpKernel_comp_trim hm]
    exact hg
  have hc := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc0)
  have hf := sbxTakeoverMinimalR01_resampling_fields_eq_on Q.measure {x : Vec d | -2 * R ≤ x i}
  have ht : ∀ᵐ ω ∂Q.measure,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n := by
    filter_upwards [hK.1.1,
      future_locality_ae_starts_at_origin_of_coupling hd Q lam l δ h0.le h1 P K hK]
      with ω hp hs
    haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hp
    rw [sbxS2StoppedOriginKernel, Kernel.map_apply _ (sbxS2_measurable_stopFutureSample R i),
      Probability.probabilityPart_eq_of_isProbabilityMeasure]
    exact sbxTakeoverMinimalR01_future_finite_history_stop_transport (K (0, ω)) Δ R hR i n hs
  have htc0 : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n =
        sbxS8FiniteKilledHistory (K (0, ω')) Δ R i n := by
    rw [condExpKernel_comp_trim hm]
    exact ht
  have htc := ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp htc0)
  filter_upwards [hg, hc, hf, ht, htc] with ω hω hc hf ht htc
  filter_upwards [hc, hf, htc] with ω' hω' heq ht'
  obtain ⟨hreg, r, hr⟩ := hω.1
  obtain ⟨hreg', r', hr'⟩ := hω'.1
  have hstop := requested_s3_future_supplied_stopped_locality hd Q.ellipticity_parameter
    Q lam l δ hl h0 h1 P K hK ω ω' hreg hreg' r r' hr hr'
    (fun y hy => heq y hy)
  rw [ht, ht']
  exact sbxTakeoverMinimalR01_future_raw_finite_history_eq_of_stopped_map_eq hd Λ₀ Q.ellipticity_parameter
    lam h0.le h1 Δ hΔ δ R hR i P K ω ω' hω hω' hstop n hn'


/-- The original future-kernel assertion follows from supplied stopped
locality and reconstruction of the actual finite path-and-coin histories. -/
theorem sbxTakeoverR01_future_kernel :
    node_app_u3A_factorization_u23_future_u2D_kernelStmt := by
  apply sbxTakeoverMinimalR01_future_kernel_of_finite_histories
  intro d hd Λ₀ r₀ Q lam h0 h1 l δ hl _ _ _ P K hK
  exact sbxTakeoverMinimalR01_s3_finite_killed_history_of_requested_locality
    EinsteinFull.s2_future_supplied_stopped_locality hd Q lam h0 h1 l δ hl P K hK

end EinsteinFull.Blueprint
