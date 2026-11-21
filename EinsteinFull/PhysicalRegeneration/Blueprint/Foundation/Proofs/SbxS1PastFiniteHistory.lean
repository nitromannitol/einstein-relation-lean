import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint.PastFiniteHistory
open EinsteinRelation EinsteinRelation.Regeneration
private theorem bounded_mul {α : Type*} {f g : α → ℝ}
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C * D, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

private theorem bounded_sub {α : Type*} {f g : α → ℝ}
    (hf : BoundedRealTest f) (hg : BoundedRealTest g) :
    BoundedRealTest (fun x => f x - g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩

private theorem bounded_integral_probability_family {α β : Type*}
    [MeasurableSpace β] (μ : α → Measure β)
    (hμ : ∀ a, IsProbabilityMeasure (μ a)) (F : β → ℝ)
    (hF : BoundedRealTest F) : BoundedRealTest (fun a => ∫ z, F z ∂μ a) := by
  obtain ⟨C, hC⟩ := hF
  refine ⟨C, fun a => ?_⟩
  let := hμ a
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ a) (f := F) (C := C)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z))

private theorem integrable_of_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : α → ℝ)
    (hF : Measurable F) (hb : BoundedRealTest F) : Integrable F μ := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- The physical-kernel version of
`EinsteinFull.Blueprint.PastFiniteHistory.ae_origin_data_of_gmpCoupling`. -/
theorem ae_origin_data_of_gmpCoupling_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0 h1 P K) :
    ∀ᵐ ω ∂Q.measure,
      IsProbabilityMeasure (K (0, ω)) ∧
      (∀ᵐ z ∂K (0, ω), z.1 0 = 0) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, ω))) ∧
      Renewal.OneIntervalKernelAt (Renewal.regenDelta lam) δ (l / lam)
        (Renewal.forceCoord hd) P K (0, ω) := by
  filter_upwards [hK.1.1, hK.2.1.1, hK.2.2.1, hK.2.2.2.2.2.2.2.1]
    with ω hp hm hω hone
  obtain ⟨_, r, hr⟩ := hω
  refine ⟨hp, ?_, ?_, hone⟩
  · have hs : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
      rw [hr 0]
      exact r.pathLaw_starts_at 0
    rw [← hm] at hs
    exact ae_of_ae_map measurable_fst.aemeasurable hs
  · intro y
    rw [hr y]
    exact r.pathLaw_isMarkovKernel.isProbabilityMeasure y

section LocalVersions
open ProbabilityTheory
/-- The canonical joint-field carrier is standard Borel. -/
private theorem fieldPair_standardBorel (d : ℕ) : StandardBorelSpace (FieldPair d) := by
  let : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let : PolishSpace (FieldPair d) := inferInstance
  infer_instance

attribute [local instance] fieldPair_standardBorel
private theorem ae_condExpKernel_observation_eq {α E : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    [MeasurableSpace E] [MeasurableEq E]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    (X : α → E) (hX : Measurable[m] X) :
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
    exact (ae_map_iff hd.aemeasurable hp).mpr (Filter.Eventually.of_forall fun _ => rfl)
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_compProd hprod)

private theorem ae_condExpKernel_of_ae {α : Type*}
    [mα : MeasurableSpace α] [StandardBorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (m : MeasurableSpace α) (hm : m ≤ mα)
    {p : α → Prop} (hp : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂condExpKernel (mΩ := mα) μ m a, p b := by
  let : MeasurableSpace α := mα
  have hcomp : ∀ᵐ b ∂condExpKernel μ m ∘ₘ μ.trim hm, p b := by
    rw [condExpKernel_comp_trim hm]
    exact hp
  exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hcomp)

private theorem ae_condExpKernel_fields_eq_on {d : ℕ}
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
    exact ae_condExpKernel_observation_eq Q (localSigma U) (Probability.localSigma_le_borel U)
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

private theorem exists_local_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (U : Set (Vec d))
    (f : FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (FieldPair d)) (hG : ∀ᵐ ω ∂Q, ω ∈ G)
    (hlocal : ∀ ω ∈ G, ∀ ω' ∈ G,
      (∀ y ∈ U, ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) → f ω = f ω') :
    ∃ A : FieldPair d → ℝ, Measurable[localSigma U] A ∧ A =ᵐ[Q] f := by
  refine ⟨fun ω => ∫ ω', f ω' ∂condExpKernel Q (localSigma U) ω,
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  have heq : ∀ᵐ ω ∂Q, ∀ᵐ ω' ∂condExpKernel Q (localSigma U) ω, f ω = f ω' := by
    filter_upwards [hG,
      ae_condExpKernel_of_ae Q (localSigma U) (Probability.localSigma_le_borel U) hG,
      ae_condExpKernel_fields_eq_on Q U] with ω hω hgood heq
    filter_upwards [hgood, heq] with ω' hω' heq'
    exact hlocal ω hω ω' hω' heq'
  filter_upwards [heq] with ω hω
  calc
    _ = ∫ _ω', f ω ∂condExpKernel Q (localSigma U) ω :=
      integral_congr_ae (hω.mono fun _ h => h.symm)
    _ = f ω := by simp

/-- The physical-kernel version of
`EinsteinFull.Blueprint.PastFiniteHistory.exists_local_past_integral_version_of_gmp_scalar_comparison`. -/
theorem exists_local_past_integral_version_of_gmp_scalar_comparison_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : Renewal.IsGMPCouplingV2Phys hd hΛ₀ Q lam l δ h0.le h1 P K) :
    let R := l / lam
    let i := Renewal.forceCoord hd
    let Δ := Renewal.regenDelta lam
    ∀ (v : ℝ),
      (∀ (ω ω' : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ₀) ω)
        (hω' : IsRegular (sourceReducedBound Λ₀) ω')
        (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          ω hω lam h0.le h1)
        (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization
          hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
          ω' hω' lam h0.le h1),
        (∀ y : Vec d, P (y, ω) = r.pathLaw y) →
        (∀ y : Vec d, P (y, ω') = r'.pathLaw y) →
        (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y) →
        ∀ F : Path d → ℝ, Measurable F → BoundedRealTest F →
        (∀ γ γ' : Path d, (∀ t : ℝ≥0, t ≤ Δ → γ t = γ' t) → F γ = F γ') →
        (∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) →
        ∀ y : Vec d, y i ≤ v →
        (∫ γ, F γ ∂P (y, ω)) = (∫ γ, F γ ∂P (y, ω')) ∧
        (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω) =
          ∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P y ω') →
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        Measurable[finiteHistorySigma Δ m] H → BoundedRealTest H →
        (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
        ∃ A : FieldPair d → ℝ,
          Measurable[localSigma {y : Vec d | y i ≤ v + 3 * R}] A ∧
          (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A := by
  intro R i Δ v hcompare m H hH hHb hHs
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  let G : Set (FieldPair d) := {ω |
    (IsProbabilityMeasure (K (0, ω)) ∧
      (∀ᵐ z ∂K (0, ω), z.1 0 = 0) ∧
      (∀ y : Vec d, IsProbabilityMeasure (P (y, ω))) ∧
      Renewal.OneIntervalKernelAt Δ δ R i P K (0, ω)) ∧
    ∃ hω : IsRegular (sourceReducedBound Λ₀) ω,
      ∃ r : External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀)
        ω hω lam h0.le h1,
        ∀ y : Vec d, P (y, ω) = r.pathLaw y}
  have hG : ∀ᵐ ω ∂Q.measure, ω ∈ G := by
    filter_upwards [ae_origin_data_of_gmpCoupling_phys hd hΛ₀ Q lam l δ h0.le h1 P K hK,
      hK.2.2.1] with ω hdata hr
    exact ⟨hdata, hr⟩
  apply exists_local_supported_history_integral_version_of_scalar_comparison
    Q.measure Δ hΔ δ R i P K {y | y i ≤ v + 3 * R} v G hG
    (fun _ hω => hω.1) ?_ m H hH hHb hHs
  intro ω hωG ω' hω'G heq
  obtain ⟨hω, r, hr⟩ := hωG.2
  obtain ⟨hω', r', hr'⟩ := hω'G.2
  exact hcompare ω ω' hω hω' r r' hr hr' heq

/-- Conditional averaging turns individual scalar versions into a single local
finite kernel. The countably generated target is used by
`Kernel.ae_eq_of_compProd_eq` to obtain equality of measures on one common
full-measure set, rather than intersecting all measurable-event exceptional sets.
This is the Lean 4.35 form of `Probability.LocalKernelVersion`, kept here to
avoid importing its independently owned migration failure. -/
private theorem exists_local_kernel_of_integral_versions
    {α β : Type*} [mα : MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α β) [IsFiniteKernel κ]
    (m : MeasurableSpace α) (hm : m ≤ mα)
    (hlocal : ∀ F : β → ℝ, Measurable F → BoundedRealTest F →
      ∃ A : α → ℝ, Measurable[m] A ∧ A =ᵐ[μ] fun a => ∫ b, F b ∂κ a) :
    ∃ η : @Kernel α β m inferInstance,
      IsFiniteKernel η ∧ ∀ᵐ a ∂μ, κ a = η a := by
  classical
  let : MeasurableSpace α := mα
  let η : @Kernel α β m inferInstance := κ ∘ₖ condExpKernel μ m
  let η' : Kernel α β := η.comap id (measurable_id.mono le_rfl hm)
  have heq : ∀ t : Set β, MeasurableSet t →
      (fun a => (κ a).real t) =ᵐ[μ] fun a => (η' a).real t := by
    intro t ht
    obtain ⟨A, hA, hAe⟩ := hlocal (t.indicator (fun _ => 1))
      (measurable_const.indicator ht) ⟨1, fun b => by by_cases hb : b ∈ t <;> simp [hb]⟩
    simp only [integral_indicator ht, setIntegral_one_eq_measureReal] at hAe
    have hfi := Kernel.IsFiniteKernel.integrable μ κ ht
    have hfm : AEStronglyMeasurable[m] (fun a => (κ a).real t) μ :=
      hA.stronglyMeasurable.aestronglyMeasurable.congr hAe
    have hc := condExp_ae_eq_integral_condExpKernel hm hfi
    have hf := condExp_of_aestronglyMeasurable' hm hfm hfi
    have hi : ∀ a, (η' a).real t =
        ∫ b, (κ b).real t ∂condExpKernel μ m a := by
      intro a
      have h := Kernel.integral_comp (η := κ) (κ := condExpKernel μ m) (a := a)
        ((integrable_const (μ := (κ ∘ₖ condExpKernel μ m) a) (1 : ℝ)).indicator ht)
      simpa only [η', Kernel.comap_apply, id_eq, η, integral_indicator ht,
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

/-- A spatially joint local version, under a finite measure on starts and
original fields. Conditional resampling retains the start exactly and both
fields simultaneously at every point of the region. -/
private theorem exists_joint_start_version_of_fields_eq_on {d : ℕ}
    (μ : Measure (Vec d × FieldPair d)) [IsFiniteMeasure μ] (U : Set (Vec d))
    (f : Vec d × FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (Vec d × FieldPair d)) (hG : ∀ᵐ p ∂μ, p ∈ G)
    (hlocal : ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 →
      (∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y) → f p = f q) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧ A =ᵐ[μ] f := by
  let mambient := (inferInstance : MeasurableSpace (Vec d × FieldPair d))
  let m := (borel (Vec d)).prod (localSigma U)
  let : MeasurableSpace (Vec d × FieldPair d) := mambient
  have hm : m ≤ (inferInstance : MeasurableSpace (Vec d × FieldPair d)) :=
    sup_le_sup (MeasurableSpace.comap_mono BorelSpace.measurable_eq.symm.le)
      (MeasurableSpace.comap_mono (Probability.localSigma_le_borel U))
  have hfst : Measurable[m] (fun p : Vec d × FieldPair d => p.1) :=
    (@measurable_fst (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)).mono
      le_rfl BorelSpace.measurable_eq.le
  have hfields : ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p,
      ∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y := by
    let : SecondCountableTopology (Mat d) :=
      inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense U
    have : Countable D := hDc.to_subtype
    have hpoints : ∀ a : D, ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p,
        (p.2.1 (a : U), p.2.2 (a : U)) = (q.2.1 (a : U), q.2.2 (a : U)) := by
      intro a
      have hY : Measurable[localSigma U]
          (fun ω : FieldPair d => (ω.1 (a : U), ω.2 (a : U))) :=
        Measurable.of_comap_le (le_iSup (fun y : U => MeasurableSpace.comap
          (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) (a : U))
      exact ae_condExpKernel_observation_eq μ m hm
        (fun p : Vec d × FieldPair d => (p.2.1 (a : U), p.2.2 (a : U)))
        (hY.comp (@measurable_snd (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)))
    filter_upwards [ae_all_iff.mpr hpoints] with p hp
    filter_upwards [ae_all_iff.mpr hp] with q hq
    have hfun : (fun y : U => (p.2.1 y, p.2.2 y)) = fun y : U => (q.2.1 y, q.2.2 y) := by
      apply Continuous.ext_on hDd
        ((p.2.1.continuous.comp continuous_subtype_val).prodMk
          (p.2.2.continuous.comp continuous_subtype_val))
        ((q.2.1.continuous.comp continuous_subtype_val).prodMk
          (q.2.2.continuous.comp continuous_subtype_val))
      intro a ha
      exact hq ⟨a, ha⟩
    intro y hy
    exact Prod.mk.inj (congrFun hfun ⟨y, hy⟩)
  have heq : ∀ᵐ p ∂μ, ∀ᵐ q ∂condExpKernel μ m p, f p = f q := by
    filter_upwards [hG, ae_condExpKernel_of_ae μ m hm hG,
      ae_condExpKernel_observation_eq μ m hm _ hfst, hfields] with p hp hgood hx he
    filter_upwards [hgood, hx, he] with q hq hqx hqe
    exact hlocal p hp q hq hqx hqe
  refine ⟨fun p => ∫ q, f q ∂condExpKernel μ m p,
    (hf.stronglyMeasurable.integral_condExpKernel).measurable, ?_⟩
  filter_upwards [heq] with p hp
  calc
    _ = ∫ _q, f p ∂condExpKernel μ m p :=
      integral_congr_ae (hp.mono fun _ h => h.symm)
    _ = f p := by simp

/-- Construct one spatially joint local version with the correct origin
section. Product-a.e. information is transferred through an equivalent finite
measure; the separately proved Q-a.e. origin value is spliced in on `{x = 0}`. -/
private theorem exists_origin_and_joint_start_version_of_fields_eq_on {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (i : Fin d) (U : Set (Vec d))
    (f : Vec d × FieldPair d → ℝ) (hf : Measurable f)
    (G : Set (Vec d × FieldPair d)) (hG0 : ∀ᵐ ω ∂Q, (0, ω) ∈ G)
    (hGp : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), p ∈ G)
    (hlocal : ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 →
      (∀ y ∈ U, p.2.1 y = q.2.1 y ∧ p.2.2 y = q.2.2 y) → f p = f q) :
    ∃ A : Vec d × FieldPair d → ℝ,
      Measurable[(borel (Vec d)).prod (localSigma U)] A ∧
      (∀ᵐ ω ∂Q, A (0, ω) = f (0, ω)) ∧
      A =ᵐ[((volume : Measure (Vec d)).prod Q)] f := by
  classical
  obtain ⟨A0, hA0, hA0e⟩ := exists_local_version_of_fields_eq_on Q U
    (fun ω => f (0, ω)) (hf.comp (measurable_const.prodMk measurable_id))
    {ω | (0, ω) ∈ G} hG0 (fun ω hω ω' hω' he => hlocal (0, ω) hω (0, ω') hω' rfl he)
  obtain ⟨ν, hνfin, hvν, hνv⟩ :=
    exists_isFiniteMeasure_absolutelyContinuous (volume : Measure (Vec d))
  have hpv : (volume : Measure (Vec d)).prod Q ≪ ν.prod Q :=
    Measure.AbsolutelyContinuous.prod hvν (Measure.AbsolutelyContinuous.refl Q)
  have hνp : ν.prod Q ≪ (volume : Measure (Vec d)).prod Q :=
    Measure.AbsolutelyContinuous.prod hνv (Measure.AbsolutelyContinuous.refl Q)
  obtain ⟨A1, hA1, hA1e⟩ := exists_joint_start_version_of_fields_eq_on
    (ν.prod Q) U f hf G (hνp.ae_le hGp) hlocal
  have hnot0 : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q), p.1 ≠ 0 := by
    have : Nonempty (Fin d) := ⟨i⟩
    have hx : ∀ᵐ x ∂(volume : Measure (Vec d)), x ≠ 0 :=
      (compl_mem_ae_iff (s := ({0} : Set (Vec d)))).mpr (measure_singleton (0 : Vec d))
    exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Vec d))) (ν := Q)).ae hx
  refine ⟨fun p => if p.1 = 0 then A0 p.2 else A1 p, ?_, ?_, ?_⟩
  · have hs : MeasurableSet[borel (Vec d)] ({0} : Set (Vec d)) := by
      rw [← BorelSpace.measurable_eq]
      exact measurableSet_singleton _
    exact Measurable.ite
      ((@measurable_fst (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U)) hs)
      (hA0.comp (@measurable_snd (Vec d) (FieldPair d) (borel (Vec d)) (localSigma U))) hA1
  · filter_upwards [hA0e] with ω hω
    rw [ite_eq_left rfl]
    exact hω
  · filter_upwards [hpv.ae_le hA1e, hnot0] with p hp hx
    rw [ite_eq_right hx]
    exact hp

end LocalVersions
section EndpointPast
open ProbabilityTheory
end EndpointPast
section BoundedPastVersions
end BoundedPastVersions
section EndpointFubini
end EndpointFubini
section StoppedMesh
end StoppedMesh
section StoppedMeshEndpointSeries
end StoppedMeshEndpointSeries
section HistoryCylinders
end HistoryCylinders
section IntegrableEndpointTests
end IntegrableEndpointTests
end EinsteinFull.Blueprint.PastFiniteHistory
