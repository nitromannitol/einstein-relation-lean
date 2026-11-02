import EinsteinFull.Calculus.CLDFGWApplication
import EinsteinFull.Calculus.CLDFGWTrajectoryTransport
import EinsteinFull.External.DFGWInvariance
import EinsteinFull.Calculus.CLSkorokhod

/-!
The two-sided environment process on its trajectory space `C(ℝ, FieldPair d)`, and the admitted
input `dfgwInvarianceStmtV2` applied to it.

The displacement over `[a, b]` is `displacementInv (η a, η b)` on trajectories; on the image of
the two-sided process it is the actual displacement, so antisymmetry and additivity transfer from
the identities of `CLTwoSidedProcess`, and covariance holds for every trajectory.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation EinsteinFull EinsteinFull.Blueprint
open scoped NNReal Topology ENNReal

namespace EinsteinFull.External.Draft

variable {d : ℕ}

theorem continuous_tsState_time (ω : TwoSidedSpace d) : Continuous fun t => tsState t ω :=
  Probability.continuous_translate.comp (ω.2.continuous.prodMk continuous_const)

/-- The trajectory of the two-sided environment process. -/
abbrev tsTraj : TwoSidedSpace d → C(ℝ, FieldPair d) := trajOf tsState continuous_tsState_time

theorem measurable_tsTraj : Measurable (tsTraj (d := d)) :=
  measurable_trajOf _ measurable_tsState

/-- The displacement over `[a, b]` read on trajectories. -/
noncomputable def tsX0 (a b : ℝ) (η : C(ℝ, FieldPair d)) : Vec d := displacementInv (η a, η b)

theorem tsX0_tsTraj (a b : ℝ) (ω : TwoSidedSpace d) : tsX0 a b (tsTraj ω) = tsDisp a b ω :=
  (tsDisp_eq_displacementInv a b ω).symm

theorem measurable_tsX0 (a b : ℝ) : Measurable (tsX0 (d := d) a b) :=
  measurable_displacementInv.comp
    ((continuous_eval_const a).measurable.prodMk (continuous_eval_const b).measurable)

theorem tsX0_adapted {a b : ℝ} (hab : a ≤ b) :
    Measurable[dfgwCoordSigma (S := FieldPair d) (Set.Icc a b)] (tsX0 (d := d) a b) := by
  have ha : Measurable[dfgwCoordSigma (S := FieldPair d) (Set.Icc a b)]
      (fun η : C(ℝ, FieldPair d) => η a) :=
    Measurable.of_comap_le (le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc a b) =>
      MeasurableSpace.comap (fun η : C(ℝ, FieldPair d) => η t) inferInstance) a
      ⟨le_rfl, hab⟩ le_rfl)
  have hb : Measurable[dfgwCoordSigma (S := FieldPair d) (Set.Icc a b)]
      (fun η : C(ℝ, FieldPair d) => η b) :=
    Measurable.of_comap_le (le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc a b) =>
      MeasurableSpace.comap (fun η : C(ℝ, FieldPair d) => η t) inferInstance) b
      ⟨hab, le_rfl⟩ le_rfl)
  exact measurable_displacementInv.comp (ha.prodMk hb)

theorem tsX0_shift (a b τ : ℝ) (η : C(ℝ, FieldPair d)) :
    tsX0 a b (dfgwShift τ η) = tsX0 (a + τ) (b + τ) η := rfl

/-- A property of trajectories that holds on the image of the two-sided process holds almost
surely for its law. -/
theorem ae_map_tsTraj {P : Measure (TwoSidedSpace d)} {p : C(ℝ, FieldPair d) → Prop}
    (hp : MeasurableSet {η | p η}) (h : ∀ ω, p (tsTraj ω)) :
    ∀ᵐ η ∂P.map tsTraj, p η :=
  (ae_map_iff measurable_tsTraj.aemeasurable hp).2 (ae_of_all _ h)

theorem tsX0_refl_mid_ae (P : Measure (TwoSidedSpace d)) (a b : ℝ) :
    (fun η => tsX0 a b (dfgwRefl ((a + b) / 2) η)) =ᵐ[P.map tsTraj] fun η => -tsX0 a b η := by
  refine ae_map_tsTraj (measurableSet_eq_fun ((measurable_tsX0 a b).comp
    (measurable_dfgwRefl _)) (measurable_tsX0 a b).neg) fun ω => ?_
  change tsX0 a b ((dfgwRefl ((a + b) / 2) ∘ tsTraj) ω) = -tsX0 a b (tsTraj ω)
  rw [← trajOf_refl continuous_tsState_time tsState_refl, Function.comp_apply, tsX0_tsTraj,
    tsX0_tsTraj, tsDisp_refl_mid]

theorem tsX0_add_ae (P : Measure (TwoSidedSpace d)) (a b c : ℝ) :
    (fun η => tsX0 a b η + tsX0 b c η) =ᵐ[P.map tsTraj] tsX0 a c := by
  refine ae_map_tsTraj (measurableSet_eq_fun ((measurable_tsX0 a b).add (measurable_tsX0 b c))
    (measurable_tsX0 a c)) fun ω => ?_
  change tsX0 a b (tsTraj ω) + tsX0 b c (tsTraj ω) = tsX0 a c (tsTraj ω)
  rw [tsX0_tsTraj, tsX0_tsTraj, tsX0_tsTraj, tsDisp_add]

theorem integrable_tsX0 {P : Measure (TwoSidedSpace d)} {a b : ℝ}
    (h : Integrable (tsDisp a b) P) : Integrable (tsX0 a b) (P.map tsTraj) := by
  refine (integrable_map_measure (measurable_tsX0 a b).aestronglyMeasurable
    measurable_tsTraj.aemeasurable).2 ?_
  have : tsX0 a b ∘ tsTraj = tsDisp (d := d) a b := funext fun ω => tsX0_tsTraj a b ω
  rw [this]
  exact h

instance polishSpace_twoSidedPath : PolishSpace C(ℝ, Vec d) := by
  haveI : CompleteSpace C(ℝ, Vec d) := inferInstance
  haveI : Filter.IsCountablyGenerated (uniformity C(ℝ, Vec d)) := inferInstance
  haveI : SecondCountableTopology C(ℝ, Vec d) := inferInstance
  infer_instance

instance polishSpace_path : PolishSpace (Path d) := by
  haveI : CompleteSpace (Path d) := inferInstance
  haveI : Filter.IsCountablyGenerated (uniformity (Path d)) := inferInstance
  haveI : SecondCountableTopology (Path d) := inferInstance
  infer_instance

instance standardBorel_twoSidedSpace : StandardBorelSpace (TwoSidedSpace d) := by
  letI : PolishSpace (FieldPair d) := fieldPair_polish d
  haveI : StandardBorelSpace (aperiodicSet d) := (measurableSet_aperiodicSet d).standardBorel
  infer_instance

/-- On paths through the origin at time zero the trajectory map is injective. -/
theorem tsTraj_injOn : Set.InjOn (tsTraj (d := d)) {ω | ω.2 0 = 0} := by
  intro ω hω ω' hω' h
  simp only [Set.mem_setOf_eq] at hω hω'
  have h0 : (ω.1 : FieldPair d) = ω'.1 := by
    have := congrArg (fun η : C(ℝ, FieldPair d) => η 0) h
    simpa [trajOf, tsState, hω, hω'] using this
  have h1 : ω.1 = ω'.1 := Subtype.ext h0
  refine Prod.ext h1 (ContinuousMap.ext fun t => ?_)
  have ht := congrArg (fun η : C(ℝ, FieldPair d) => η t) h
  simp only [trajOf, tsState, ContinuousMap.coe_mk] at ht
  rw [← h0] at ht
  have := congrArg (fun x => displacementInv ((ω.1 : FieldPair d), x)) ht
  simpa [displacementInv_translate ω.1.2] using this

theorem tsLaw_ae_start {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (K : Kernel (FieldPair d × Vec d) (Path d)) :
    ∀ᵐ ω ∂tsLaw Q K, ω.2 0 = 0 := by
  unfold tsLaw
  refine (ae_map_iff measurable_tsGlue.aemeasurable
    (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      measurable_const)).2 (ae_of_all _ fun z => ?_)
  exact gluePath_zero z.2

/-- The displacement path read on trajectories, decoded to a continuous path. -/
noncomputable def tsY : C(ℝ, FieldPair d) → Path d :=
  (Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)).choose ∘
    fun η (t : ℝ≥0) => tsX0 0 t η

theorem measurable_tsY : Measurable (tsY (d := d)) :=
  (Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)).choose_spec.1.comp
    (Measurable.of_eval fun (t : ℝ≥0) => measurable_tsX0 0 (t : ℝ))

theorem tsY_tsTraj (ω : TwoSidedSpace d) (t : ℝ≥0) : tsY (tsTraj ω) t = tsX0 0 t (tsTraj ω) := by
  let f : Path d := ⟨fun t : ℝ≥0 => ω.2 t - ω.2 0,
    (ω.2.continuous.comp NNReal.continuous_coe).sub continuous_const⟩
  have hraw : (fun t : ℝ≥0 => tsX0 0 t (tsTraj ω)) = fun t => f t := by
    funext s
    rw [tsX0_tsTraj]
    rfl
  have hD := (Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0)
    (E := Vec d)).choose_spec.2 f
  change (Probability.exists_measurable_continuousMap_decoder (X := ℝ≥0) (E := Vec d)).choose
    (fun t : ℝ≥0 => tsX0 0 t (tsTraj ω)) t = _
  rw [hraw, hD, ← congrFun hraw t]

/-- The decoded displacement path is a version of the displacement family, for the law of any
two-sided process whose paths start at the origin. -/
theorem tsY_version {P : Measure (TwoSidedSpace d)} (h0 : ∀ᵐ ω ∂P, ω.2 0 = 0) :
    ∀ᵐ η ∂P.map tsTraj, ∀ t : ℝ≥0, tsY η t = tsX0 0 t η := by
  have hs : MeasurableSet {ω : TwoSidedSpace d | ω.2 0 = 0} :=
    measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd)
      measurable_const
  have hA : MeasurableSet (tsTraj '' {ω : TwoSidedSpace d | ω.2 0 = 0}) :=
    hs.image_of_measurable_injOn measurable_tsTraj tsTraj_injOn
  have hmem : ∀ᵐ η ∂P.map tsTraj, η ∈ tsTraj '' {ω : TwoSidedSpace d | ω.2 0 = 0} := by
    refine (ae_map_iff measurable_tsTraj.aemeasurable hA).2 ?_
    filter_upwards [h0] with ω hω
    exact ⟨ω, hω, rfl⟩
  filter_upwards [hmem] with η hη
  obtain ⟨ω, -, rfl⟩ := hη
  exact tsY_tsTraj ω

section Application

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hap hK in
/-- DFGW (2.39) on the trajectory space of the two-sided process. -/
theorem tsLaw_velocity_traj :
    Tendsto (fun δ : ℝ => ∫ η, ‖δ⁻¹ • (((tsLaw Q K).map tsTraj)[tsX0 0 δ |
      dfgwCoordSigma (S := FieldPair d) (Set.Iic 0)]) η - envDrift hd (η 0)‖
        ∂(tsLaw Q K).map tsTraj) (𝓝[>] 0) (𝓝 0) := by
  have := tsLaw_isProbability Q hap K
  refine Tendsto.congr' ?_ (tsLaw_velocity hd D Q hQ hunforced hpath hap hK)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hle : dfgwCoordSigma (S := FieldPair d) (Set.Iic 0) ≤
      dfgwTrajectoryMeasurableSpace (S := FieldPair d) :=
    iSup₂_le fun u _ => (continuous_eval_const u).measurable.comap_le
  have hint : Integrable (tsX0 0 δ) ((tsLaw Q K).map tsTraj) :=
    integrable_tsX0 (integrable_tsDisp hd D Q hQ hunforced hpath hap hK (le_of_lt hδ))
  have hc := condExp_map_comp measurable_tsTraj hle hint
  rw [comap_trajOf_coordSigma] at hc
  have hcomp : tsX0 0 δ ∘ tsTraj = tsDisp (d := d) 0 δ := funext fun ω => tsX0_tsTraj 0 δ ω
  rw [hcomp] at hc
  have hg : AEStronglyMeasurable (fun η : C(ℝ, FieldPair d) =>
      ‖δ⁻¹ • (((tsLaw Q K).map tsTraj)[tsX0 0 δ | dfgwCoordSigma (S := FieldPair d)
        (Set.Iic 0)]) η - envDrift hd (η 0)‖) ((tsLaw Q K).map tsTraj) :=
    (((stronglyMeasurable_condExp.mono hle).measurable.const_smul δ⁻¹).sub
      ((measurable_envDrift hd).comp (continuous_eval_const 0).measurable)).norm.aestronglyMeasurable
  rw [integral_map measurable_tsTraj.aemeasurable hg]
  refine integral_congr_ae ?_
  filter_upwards [hc] with ω hω
  change ‖δ⁻¹ • ((tsLaw Q K)[tsDisp 0 δ | tsPastSigma d]) ω - envDrift hd (tsState 0 ω)‖ =
    ‖δ⁻¹ • (((tsLaw Q K).map tsTraj)[tsX0 0 δ | dfgwCoordSigma (S := FieldPair d)
      (Set.Iic 0)]) (tsTraj ω) - envDrift hd (tsState 0 ω)‖
  rw [hω]

/-- The compensated displacement read on trajectories. -/
noncomputable def tsM0 (t : ℝ) (η : C(ℝ, FieldPair d)) : Vec d :=
  tsX0 0 t η - ∫ τ in (0 : ℝ)..t, envDrift hd (η τ)

theorem tsM0_tsTraj (t : ℝ) (ω : TwoSidedSpace d) : tsM0 hd t (tsTraj ω) = tsComp hd t ω := by
  simp only [tsM0, tsComp, tsX0_tsTraj]
  rfl

theorem stronglyMeasurable_tsM0 (t : ℝ≥0) :
    StronglyMeasurable[dfgwCoordSigma (S := FieldPair d) (Set.Iic (t : ℝ))] (tsM0 hd t) := by
  have hx : StronglyMeasurable[dfgwCoordSigma (S := FieldPair d) (Set.Iic (t : ℝ))]
      (tsX0 (d := d) 0 t) :=
    ((tsX0_adapted t.coe_nonneg).mono (by
      exact iSup₂_le fun u hu => le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Iic (t : ℝ)) =>
        MeasurableSpace.comap (fun η : C(ℝ, FieldPair d) => η s) inferInstance) u hu.2 le_rfl)
      le_rfl).stronglyMeasurable
  exact hx.sub (stronglyMeasurable_integral_past (measurable_envDrift hd) t.coe_nonneg)

theorem measurable_tsM0 (t : ℝ≥0) : Measurable (tsM0 (d := d) hd t) :=
  ((stronglyMeasurable_tsM0 hd t).mono
    (iSup₂_le fun u _ => (continuous_eval_const u).measurable.comap_le)).measurable

include hQ hap hK in
/-- DFGW (2.40), first part, on the trajectory space. -/
theorem memLp_tsM0 (t : ℝ≥0) : MemLp (tsM0 hd t) 2 ((tsLaw Q K).map tsTraj) := by
  refine (memLp_map_measure_iff (measurable_tsM0 hd t).aestronglyMeasurable
    measurable_tsTraj.aemeasurable).2 ?_
  have : tsM0 hd t ∘ tsTraj = tsComp (d := d) hd t := funext fun ω => tsM0_tsTraj hd t ω
  rw [this]
  exact memLp_tsComp hd D Q hQ hap hK t

include hQ hunforced hpath hap hK in
/-- DFGW (2.40), the martingale property, on the trajectory space. -/
theorem tsM0_martingale :
    Martingale (fun (t : ℝ≥0) η => tsX0 0 t η - ∫ τ in (0 : ℝ)..t, envDrift hd (η τ))
      (dfgwPast (S := FieldPair d)) ((tsLaw Q K).map tsTraj) := by
  have := tsLaw_isProbability Q hap K
  refine ⟨fun t => stronglyMeasurable_tsM0 hd t, fun s t hst => ?_⟩
  have hle : dfgwCoordSigma (S := FieldPair d) (Set.Iic (s : ℝ)) ≤
      dfgwTrajectoryMeasurableSpace (S := FieldPair d) :=
    iSup₂_le fun u _ => (continuous_eval_const u).measurable.comap_le
  have hint : Integrable (tsM0 hd t) ((tsLaw Q K).map tsTraj) :=
    (memLp_tsM0 hd D Q hQ hap hK t).integrable one_le_two
  have hc := condExp_map_comp measurable_tsTraj hle hint
  rw [comap_trajOf_coordSigma] at hc
  have hcomp : tsM0 hd t ∘ tsTraj = tsComp (d := d) hd t := funext fun ω => tsM0_tsTraj hd t ω
  rw [hcomp] at hc
  have hm := (tsComp_martingale hd D Q hQ hunforced hpath hap hK).condExp_ae_eq hst
  have h3 : (fun ω => (((tsLaw Q K).map tsTraj)[tsM0 hd t |
      dfgwCoordSigma (S := FieldPair d) (Set.Iic (s : ℝ))]) (tsTraj ω)) =ᵐ[tsLaw Q K]
        fun ω => tsM0 hd s (tsTraj ω) :=
    hc.trans (hm.trans (Filter.Eventually.of_forall fun ω => (tsM0_tsTraj hd s ω).symm))
  exact (ae_map_iff measurable_tsTraj.aemeasurable (measurableSet_eq_fun
    (stronglyMeasurable_condExp.mono hle).measurable (measurable_tsM0 hd s))).2 h3

include hQ hunforced hpath hap hK in
/-- The trajectory family of the two-sided process satisfies the hypotheses of the admitted input. -/
theorem tsTrajFamily :
    IsDFGWTrajectoryFamily ((tsLaw Q K).map tsTraj) (tsX0 (d := d)) tsY where
  adapted _ _ hab := tsX0_adapted hab
  antisymmetric a b _ := tsX0_refl_mid_ae _ a b
  integrable _ _ hab := integrable_tsX0 (integrable_tsDisp hd D Q hQ hunforced hpath hap hK hab)
  covariant a b τ _ := ae_of_all _ fun η => tsX0_shift a b τ η
  additive a b c _ _ := tsX0_add_ae _ a b c
  version_measurable := measurable_tsY
  version := tsY_version (tsLaw_ae_start Q K)

include hQ hunforced hpath hap hK in
/-- The admitted DFGW input applied to the two-sided environment process. The matrix `C` and the
limit (2.43) are read on the two-sided law; the Skorokhod-space convergence is on its trajectory
law. -/
theorem dfgw_conclusion_traj :
    ∃ C Dm : Mat d,
      (∀ e : Vec d, dot e (C.mulVec e) =
        ∫ ω, dot e (tsComp hd 1 ω) ^ 2 ∂tsLaw Q K) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, envDrift hd x i *
          ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) (Set.Ioi 0) ∧
        Dm i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, envDrift hd x i * ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) ∧
      (∀ (e : Vec d) (t : ℝ≥0), Tendsto
        (fun ε : ℝ => ∫ ω, dot e (ε • tsDisp 0 ((ε⁻¹ ^ 2).toNNReal * t) ω) ^ 2 ∂tsLaw Q K)
        (𝓝[>] 0) (𝓝 (dot e (Dm.mulVec e) * t))) ∧
      ∃ W : Measure (Path d), IsBrownianLaw Dm W ∧
        ∀ F : CadlagPath d → ℝ, IsSkorokhodTest F →
          Tendsto (fun ε : ℝ => ∫ η, F (Path.toCadlag (rescalePath ε (tsY η)))
            ∂(tsLaw Q K).map tsTraj) (𝓝[>] 0) (𝓝 (∫ γ, F (Path.toCadlag γ) ∂W)) := by
  have := tsLaw_isProbability Q hap K
  have hsep : TopologicalSpace.SeparableSpace (Lp ℝ 2 Q.measure) := by
    haveI : IsProbabilityMeasure Q.measure := Q.probability
    haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
    infer_instance
  have hdot : ∀ e : Vec d, Continuous fun v : Vec d => dot e v := fun e => by
    unfold dot
    fun_prop
  obtain ⟨C, Dm, hC, hD, h243, W, hW, hconv⟩ :=
    External.dfgw_invariance d (FieldPair d) ((tsLaw Q K).map tsTraj) Q.measure (envKernel K)
      tsX0 tsY
      (isDFGWTrajectoryProcess_map continuous_tsState_time
        (dfgw_process hd D Q hQ hunforced hpath hap hK))
      dfgwCoordSigma_univ_eq_borel hsep (tsTrajFamily hd D Q hQ hunforced hpath hap hK)
      (envDrift hd) (memLp_envDrift hd D Q)
      (tsLaw_velocity_traj hd D Q hQ hunforced hpath hap hK)
      (memLp_tsM0 hd D Q hQ hap hK) (tsM0_martingale hd D Q hQ hunforced hpath hap hK)
  refine ⟨C, Dm, fun e => ?_, hD, fun e t => ?_, W, hW, hconv⟩
  · have hg : AEStronglyMeasurable (fun η : C(ℝ, FieldPair d) =>
        dot e (tsX0 0 1 η - ∫ τ in (0 : ℝ)..1, envDrift hd (η τ)) ^ 2) ((tsLaw Q K).map tsTraj) :=
      (((hdot e).measurable.comp (measurable_tsM0 hd 1)).pow_const 2).aestronglyMeasurable
    rw [hC e, integral_map measurable_tsTraj.aemeasurable hg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change dot e (tsM0 hd 1 (tsTraj ω)) ^ 2 = dot e (tsComp hd 1 ω) ^ 2
    rw [tsM0_tsTraj]
  · refine Tendsto.congr (fun ε => ?_) (h243 e t)
    have hg : AEStronglyMeasurable (fun η : C(ℝ, FieldPair d) =>
        dot e (ε • tsY η ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2) ((tsLaw Q K).map tsTraj) :=
      (((hdot e).measurable.comp (((continuous_eval_const _).measurable.comp
        measurable_tsY).const_smul ε)).pow_const 2).aestronglyMeasurable
    rw [integral_map measurable_tsTraj.aemeasurable hg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change dot e (ε • tsY (tsTraj ω) ((ε⁻¹ ^ 2).toNNReal * t)) ^ 2 = _
    rw [tsY_tsTraj, tsX0_tsTraj, NNReal.coe_mul]

include hQ hunforced hpath hap hK in
/-- From the admitted DFGW input: every quenched path law solving the unforced reduced martingale
problem has an annealed invariance principle, with the diffusion matrix of DFGW. -/
theorem dfgw_hasDiffusivity_axiom (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) :
    ∃ C Dm : Mat d,
      (∀ e : Vec d, dot e (C.mulVec e) =
        ∫ ω, dot e (tsDisp 0 1 ω - ∫ τ in (0 : ℝ)..1, envDrift hd (tsState τ ω)) ^ 2
          ∂tsLaw Q K) ∧
      (∀ i j : Fin d,
        IntegrableOn (fun t : ℝ => ∫ x, envDrift hd x i *
          ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) (Set.Ioi 0) ∧
        Dm i j = C i j - 2 * ∫ t in Set.Ioi (0 : ℝ),
          ∫ x, envDrift hd x i * ∫ y, envDrift hd y j ∂envKernel K t.toNNReal x ∂Q.measure) ∧
      HasDiffusivity Q.measure (originLaw Y) Dm := by
  have := tsLaw_isProbability Q hap K
  obtain ⟨C, Dm, hC, hD, -, W, hW, hsk⟩ := dfgw_conclusion_traj hd D Q hQ hunforced hpath hap hK
  haveI : IsProbabilityMeasure W := hW.1
  haveI : IsProbabilityMeasure ((tsLaw Q K).map tsTraj) :=
    (Measure.isProbabilityMeasure_map_iff measurable_tsTraj.aemeasurable).2 inferInstance
  refine ⟨C, Dm, hC, hD, W, hW, fun F => ?_⟩
  have h := tendsto_boundedContinuous_of_skorokhod measurable_tsY hsk F
  refine h.congr fun ε => ?_
  have hFm : Measurable fun γ : Path d => F (rescalePath ε γ) :=
    (F.continuous.comp (TimeChangeCovariance.continuous_rescalePath ε)).measurable
  have hg : AEStronglyMeasurable (fun η : C(ℝ, FieldPair d) => F (rescalePath ε (tsY η)))
      ((tsLaw Q K).map tsTraj) := (hFm.comp measurable_tsY).aestronglyMeasurable
  rw [integral_map measurable_tsTraj.aemeasurable hg]
  have hpath' : ∀ ω, tsY (tsTraj ω) =
      dfgwPath (dfgw_family hd D Q hQ hunforced hpath hap hK) ω := fun ω => by
    ext t j
    rw [tsY_tsTraj, tsX0_tsTraj]
    rfl
  simp_rw [hpath']
  exact integral_rescale_dfgwPath hd D Q hQ hap hK Y hY
    (dfgw_family hd D Q hQ hunforced hpath hap hK) F ε

end Application

end EinsteinFull.External.Draft
