import EinsteinRelation.Probability.SlutskyMetrizable
import EinsteinRelation.Diffusion.JointClockPathMapSupport
import EinsteinRelation.Diffusion.Covariance
import EinsteinRelation.Clock.InverseClockScaling
import EinsteinRelation.Diffusion.BrownianScaling
import EinsteinRelation.External.ReducedLimitTheorems
import EinsteinRelation.External.TimeChangeInputs
import EinsteinRelation.Environment.Bounds

/-! # The covariance half of the time-change identities

Source: `paper/main.tex` 228-233. If the reduced diffusion `Y⁰` has diffusivity `ā`, its clock
satisfies `A⁰(t)/t → m`, and the physical diffusion is the time change `X⁰(A⁰(t)) = Y⁰(t)`, then
the physical diffusion has diffusivity `m⁻¹ ā`. The proof follows the source: the diffusive
rescaling of `X⁰` is the rescaling of `Y⁰` run on the rescaled inverse clock
`τ_ε(t) = ε² A⁻¹(ε⁻² t)`, which tends to `t ↦ t / m` locally uniformly; Slutsky's theorem and the
continuity of composition then give the limit `W(· / m)`, a Brownian motion with covariance
`m⁻¹ ā`. The cited inputs enter as explicit hypotheses with the shapes of
`EinsteinRelation.External.TimeChangeLaw`, `EinsteinRelation.External.EnvironmentProcessErgodic`
and `EinsteinRelation.External.ReducedInvarianceAbar`.

The time change is carried by a one-dimensional path `Path 1`, so that its measurability follows
from the cylinder description of the Borel σ-algebra of path space.
-/

open MeasureTheory Filter TopologicalSpace ProbabilityTheory
open scoped NNReal Topology ENNReal

namespace EinsteinRelation.TimeChangeCovariance

open Clock.PathMapV4 (PhysicalInput inversePhysicalTime inverseClockPathMap)

variable {d : ℕ} {L r₀ : ℝ}

/-! ### Paths run on a clock -/

/-- Nonnegative time read off the coordinate of a one-dimensional path value. -/
noncomputable def toTime : C(Vec 1, ℝ≥0) :=
  ⟨fun v => (v 0).toNNReal, continuous_real_toNNReal.comp (continuous_apply 0)⟩

/-- The path `γ` run on the clock `τ`: `t ↦ γ ((τ t)⁺)`. -/
noncomputable def timeChangePath (p : Path d × Path 1) : Path d :=
  p.1.comp (toTime.comp p.2)

@[simp] theorem timeChangePath_apply (p : Path d × Path 1) (t : ℝ≥0) :
    timeChangePath p t = p.1 ((p.2 t 0).toNNReal) := rfl

theorem continuous_timeChangePath : Continuous (timeChangePath (d := d)) :=
  (ContinuousMap.continuous_comp' (X := ℝ≥0) (Y := ℝ≥0) (Z := Vec d)).comp
    (((ContinuousMap.continuous_postcomp toTime).comp continuous_snd).prodMk continuous_fst)

theorem continuous_rescalePath (ε : ℝ) : Continuous (rescalePath (d := d) ε) := by
  let s : C(Vec d, Vec d) := ⟨fun v => ε • v, continuous_const_smul ε⟩
  have h := (ContinuousMap.continuous_postcomp s).comp
    (continuous_timeScalePath (d := d) ((ε⁻¹ ^ 2).toNNReal))
  exact h.congr fun γ => ContinuousMap.ext fun t => rfl

/-- A map into path space is measurable when each of its evaluations is. -/
theorem measurable_path_of_forall_eval {α : Type*} [MeasurableSpace α] {k : ℕ} {f : α → Path k}
    (hf : ∀ t, Measurable fun a => f a t) : Measurable f := by
  change @Measurable α (Path k) _ (borel (Path k)) f
  rw [borel_eq_generateFrom_measurablePathCylinders]
  apply measurable_generateFrom
  intro s hs
  rcases hs with ⟨c, hc, rfl⟩
  induction c with
  | nil => simp [pathEvalCylinder]
  | cons p c ih =>
    rcases p with ⟨t, A⟩
    simp only [pathEvalCylinder, Set.preimage_inter]
    exact (hf t (hc (t, A) (by simp))).inter (ih (fun q hq => hc q (by simp [hq])))

/-! ### The rescaled inverse clock -/

/-- The rescaled inverse clock `t ↦ ε² A⁻¹(ε⁻² t)` of a regular field and a path, as a
one-dimensional path. -/
noncomputable def scaledInverseClock (ε : ℝ) (z : PhysicalInput d L × Path d) : Path 1 :=
  ⟨fun t _ => ε ^ 2 * (inversePhysicalTime z ((ε⁻¹ ^ 2).toNNReal * t) : ℝ), by
    have hinv : Continuous (inversePhysicalTime z) :=
      (Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2).symm.continuous
    exact continuous_pi fun _ => continuous_const.mul
      (NNReal.continuous_coe.comp (hinv.comp (continuous_const.mul continuous_id)))⟩

/-- The linear clock `t ↦ t / m`, as a one-dimensional path. -/
noncomputable def linearClock (m : ℝ) : Path 1 :=
  ⟨fun t _ => (t : ℝ) / m, continuous_pi fun _ => NNReal.continuous_coe.div_const m⟩

theorem measurable_scaledInverseClock (ε : ℝ) :
    Measurable (scaledInverseClock (d := d) (L := L) ε) := by
  refine measurable_path_of_forall_eval fun t => Measurable.of_eval fun _ => ?_
  have h := (Clock.PathMapV4.measurable_inversePhysicalTime (d := d) (L := L)).comp
    (measurable_id.prodMk (measurable_const (a := (ε⁻¹ ^ 2).toNNReal * t)))
  exact measurable_const.mul (NNReal.continuous_coe.measurable.comp h)

/-- The rescaled physical path is the rescaled reduced path run on the rescaled inverse clock. -/
theorem rescalePath_inverseClockPathMap {ε : ℝ} (hε : ε ≠ 0) (z : PhysicalInput d L × Path d) :
    rescalePath ε (inverseClockPathMap z) =
      timeChangePath (rescalePath ε z.2, scaledInverseClock ε z) := by
  refine ContinuousMap.ext fun t => ?_
  set x := inversePhysicalTime z ((ε⁻¹ ^ 2).toNNReal * t)
  have key : (ε⁻¹ ^ 2).toNNReal * (ε ^ 2 * (x : ℝ)).toNNReal = x := by
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    field_simp
  calc rescalePath ε (inverseClockPathMap z) t = ε • z.2 x := rfl
    _ = ε • z.2 ((ε⁻¹ ^ 2).toNNReal * (ε ^ 2 * (x : ℝ)).toNNReal) := by rw [key]
    _ = timeChangePath (rescalePath ε z.2, scaledInverseClock ε z) t := rfl

/-- Along a path whose clock grows at rate `m`, the rescaled inverse clock tends to `t ↦ t / m`
in path space. -/
theorem tendsto_scaledInverseClock {m : ℝ} (hm : 0 < m) (z : PhysicalInput d L × Path d)
    (hA : Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / t) atTop (𝓝 m)) :
    Tendsto (fun ε => scaledInverseClock ε z) (𝓝[>] 0) (𝓝 (linearClock m)) := by
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
  have h := inverse_scaling_tendsto_locallyUniformly
    (A := Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2) hm (by simpa using hA)
  rw [Metric.tendstoLocallyUniformly_iff] at h ⊢
  intro δ hδ t
  obtain ⟨u, hu, hev⟩ := h δ hδ t
  refine ⟨u, hu, hev.mono fun ε hε s hs => ?_⟩
  have hdist : dist (linearClock m s) (scaledInverseClock ε z s) =
      dist ((s : ℝ) / m) (ε ^ 2 * (inversePhysicalTime z ((ε⁻¹ ^ 2).toNNReal * s) : ℝ)) :=
    dist_pi_const _ _
  rw [hdist]
  exact hε s hs

/-- The linear clock runs a path at the constant speed `m⁻¹`. -/
theorem timeChangePath_linearClock {m : ℝ} (hm : 0 < m) (γ : Path d) :
    timeChangePath (γ, linearClock m) = timeScalePath (m⁻¹).toNNReal γ := by
  refine ContinuousMap.ext fun t => ?_
  have key : ((t : ℝ) / m).toNNReal = (m⁻¹).toNNReal * t := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    ring
  show γ (((t : ℝ) / m).toNNReal) = γ ((m⁻¹).toNNReal * t)
  rw [key]

/-! ### Annealed laws over regular fields -/

theorem ae_physicalReferenceLaw (Q : EnvironmentLaw d L r₀) {p : FieldPair d → Prop}
    (h : ∀ᵐ ω ∂Q.measure, p ω) : ∀ᵐ x ∂ReductionImageV3.physicalReferenceLaw Q, p x.1 := by
  rw [← ReductionImageV3.physicalReferenceLaw_forget Q] at h
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable h

theorem integral_physicalReferenceLaw (Q : EnvironmentLaw d L r₀) {G : FieldPair d → ℝ}
    (hG : AEStronglyMeasurable G Q.measure) :
    ∫ x, G x.1 ∂ReductionImageV3.physicalReferenceLaw Q = ∫ ω, G ω ∂Q.measure := by
  have hmap := ReductionImageV3.physicalReferenceLaw_forget Q
  rw [← hmap] at hG ⊢
  exact (integral_map measurable_subtype_coe.aemeasurable hG).symm

/-- The quenched integral of a bounded measurable path observable is a.e. strongly measurable in
the environment, through the probability part of the kernel. -/
theorem aestronglyMeasurable_quenchedIntegral (Q : EnvironmentLaw d L r₀) (K : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw K ω))
    {G : Path d → ℝ} (hG : Measurable G) :
    AEStronglyMeasurable (fun ω => ∫ γ, G γ ∂originLaw K ω) Q.measure := by
  have hsm : StronglyMeasurable fun ω => ∫ γ, G γ ∂Probability.probabilityPart (originLaw K) ω :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := Probability.probabilityPart (originLaw K))
      (f := fun q : FieldPair d × Path d => G q.2) (hG.comp measurable_snd).stronglyMeasurable
  refine hsm.aestronglyMeasurable.congr ?_
  filter_upwards [Probability.probabilityPart_ae_eq Q.measure (originLaw K) hprob] with ω hω
  rw [hω]

theorem integral_actualPhysicalInputPathLaw (Q : EnvironmentLaw d L r₀) (K : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw K ω))
    {H : PhysicalInput d L × Path d → ℝ} (hH : Measurable H) (hb : ∃ C : ℝ, ∀ z, |H z| ≤ C) :
    ∫ z, H z ∂Clock.PathMapV4.actualPhysicalInputPathLaw Q K =
      ∫ x, ∫ γ, H (x, γ) ∂(K (0, x.1)) ∂ReductionImageV3.physicalReferenceLaw Q := by
  letI : IsProbabilityMeasure (ReductionImageV3.physicalReferenceLaw Q) :=
    ReductionImageV3.physicalReferenceLaw_probability Q
  have hK : ∀ᵐ x ∂ReductionImageV3.physicalReferenceLaw Q,
      IsProbabilityMeasure (((originLaw K).comap (Subtype.val : PhysicalInput d L → FieldPair d)
        measurable_subtype_coe) x) := ae_physicalReferenceLaw Q hprob
  exact Probability.integral_compProd_probabilityPart _ _ hK H hH hb

/-- A bounded continuous function composed with a measurable map is integrable for a finite
measure. -/
theorem integrable_bcf_comp {α E : Type*} [MeasurableSpace α] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] (ν : Measure α) [IsFiniteMeasure ν]
    (F : BoundedContinuousFunction E ℝ) {X : α → E} (hX : Measurable X) :
    Integrable (fun a => F (X a)) ν :=
  (integrable_const ‖F‖).mono' (F.continuous.measurable.comp hX).aestronglyMeasurable
    (ae_of_all _ fun a => F.norm_coe_le_norm (X a))

/-! ### Convergence of the reduced path and of the clock on an enlarged space -/

/-- Integrals over the product with a probability measure that only see the first factor. -/
theorem integral_prod_fst_of_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {g : α → ℝ} (hg : Integrable g μ) : ∫ p, g p.1 ∂(μ.prod ν) = ∫ a, g a ∂μ := by
  rw [integral_prod _ (hg.comp_fst ν)]
  simp

theorem integral_prod_snd_of_prob {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    {g : β → ℝ} (hg : Integrable g ν) : ∫ p, g p.2 ∂(μ.prod ν) = ∫ b, g b ∂ν := by
  rw [integral_prod _ (hg.comp_snd μ)]
  simp

/-- If the rescaled paths `rescalePath ε (path a)` converge weakly to `W` under `μ`, then on the
product with `W` they converge in distribution to the second coordinate. -/
theorem tendstoInDistribution_rescalePath {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {path : α → Path d} (hpath : Measurable path)
    {W : Measure (Path d)} [IsProbabilityMeasure W]
    (hlim : ∀ F : BoundedContinuousFunction (Path d) ℝ,
      Tendsto (fun ε : ℝ => ∫ a, F (rescalePath ε (path a)) ∂μ) (𝓝[>] 0) (𝓝 (∫ γ, F γ ∂W))) :
    TendstoInDistribution (fun ε (p : α × Path d) => rescalePath ε (path p.1)) (𝓝[>] 0)
      (fun p => p.2) (fun _ => μ.prod W) (μ.prod W) := by
  refine ⟨fun ε => ((continuous_rescalePath ε).measurable.comp
    (hpath.comp measurable_fst)).aemeasurable, measurable_snd.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map measurable_snd.aemeasurable F.continuous.aestronglyMeasurable,
    integral_prod_snd_of_prob μ W (F.integrable W)]
  refine (hlim F).congr fun ε => ?_
  have hX : Measurable fun p : α × Path d => rescalePath ε (path p.1) :=
    (continuous_rescalePath ε).measurable.comp (hpath.comp measurable_fst)
  rw [integral_map hX.aemeasurable F.continuous.aestronglyMeasurable,
    integral_prod_fst_of_prob μ W (integrable_bcf_comp μ F (X := fun a => rescalePath ε (path a))
      ((continuous_rescalePath ε).measurable.comp hpath))]

theorem probabilityPart_le_one {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α β) (a : α) (s : Set β) : Probability.probabilityPart K a s ≤ 1 := by
  classical
  rw [Probability.probabilityPart_apply]
  split_ifs with h
  · exact (measure_mono (Set.subset_univ s)).trans h.le
  · simp

/-- Under the annealed reduced law, the rescaled inverse clock converges in probability to the
linear clock `t ↦ t / m`. -/
theorem tendsto_measure_scaledInverseClock_not_mem (Q : EnvironmentLaw d L r₀)
    (K : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw K ω))
    {m : ℝ} (hm : 0 < m)
    (hErg : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(K (0, ω)),
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 m))
    (W : Measure (Path d)) [IsProbabilityMeasure W] :
    ∀ U ∈ 𝓝 (linearClock m), Tendsto (fun ε =>
      ((Clock.PathMapV4.actualPhysicalInputPathLaw Q K).prod W)
        {p | scaledInverseClock ε p.1 ∉ U}) (𝓝[>] 0) (𝓝 0) := by
  intro U hU
  obtain ⟨V, hVU, hVo, hcV⟩ := mem_nhds_iff.mp hU
  letI : IsProbabilityMeasure (ReductionImageV3.physicalReferenceLaw Q) :=
    ReductionImageV3.physicalReferenceLaw_probability Q
  set K' := (originLaw K).comap (Subtype.val : PhysicalInput d L → FieldPair d)
    measurable_subtype_coe
  set S : ℝ → Set (PhysicalInput d L × Path d) := fun ε => {z | scaledInverseClock ε z ∉ V}
  have hS : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurable_scaledInverseClock ε) hVo.measurableSet.compl
  have hle : ∀ ε, ((Clock.PathMapV4.actualPhysicalInputPathLaw Q K).prod W)
      {p | scaledInverseClock ε p.1 ∉ U} ≤ Clock.PathMapV4.actualPhysicalInputPathLaw Q K (S ε) := by
    intro ε
    calc ((Clock.PathMapV4.actualPhysicalInputPathLaw Q K).prod W)
          {p | scaledInverseClock ε p.1 ∉ U}
        ≤ ((Clock.PathMapV4.actualPhysicalInputPathLaw Q K).prod W) (S ε ×ˢ Set.univ) :=
          measure_mono fun p hp => ⟨fun hV => hp (hVU hV), Set.mem_univ _⟩
      _ = Clock.PathMapV4.actualPhysicalInputPathLaw Q K (S ε) := by
          rw [Measure.prod_prod, measure_univ, mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
  have happly : ∀ ε, Clock.PathMapV4.actualPhysicalInputPathLaw Q K (S ε) =
      ∫⁻ x, Probability.probabilityPart K' x (Prod.mk x ⁻¹' S ε)
        ∂ReductionImageV3.physicalReferenceLaw Q := fun ε =>
    Measure.compProd_apply (hS ε)
  simp_rw [happly]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂ReductionImageV3.physicalReferenceLaw Q by simp]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun ε => Kernel.measurable_kernel_prodMk_left (hS ε))
    (Eventually.of_forall fun ε => ae_of_all _ fun x => probabilityPart_le_one _ _ _)
    (by simp) ?_
  filter_upwards [ae_physicalReferenceLaw Q hprob, ae_physicalReferenceLaw Q hErg]
    with x hxprob hxerg
  haveI : IsProbabilityMeasure (K' x) := hxprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure K' x]
  have hind : ∀ ε, K' x (Prod.mk x ⁻¹' S ε) =
      ∫⁻ γ, (Prod.mk x ⁻¹' S ε).indicator 1 γ ∂K' x := fun ε =>
    (lintegral_indicator_one (measurable_prodMk_left (hS ε))).symm
  simp_rw [hind]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂K' x by simp]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun ε => measurable_one.indicator (measurable_prodMk_left (hS ε)))
    (Eventually.of_forall fun ε => ae_of_all _ fun γ => Set.indicator_le_self' (fun _ _ => zero_le_one) γ)
    (by simp) ?_
  filter_upwards [hxerg] with γ hγ
  have hτ := tendsto_scaledInverseClock hm (x, γ) hγ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), scaledInverseClock ε (x, γ) ∈ V := hτ (hVo.mem_nhds hcV)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with ε hε
  have : γ ∉ Prod.mk x ⁻¹' S ε := fun h => h hε
  simp [Set.indicator_of_notMem this]

/-! ### The physical rescaled integrals -/

/-- The physical annealed integral of a rescaled path observable is the reduced annealed integral
of the time-changed rescaled path. -/
theorem physicalIntegral_eq (Q : EnvironmentLaw d L r₀) (P P' : DiffusionFamily d)
    (hprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    (hTC : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular L ω,
      P 0 (0, ω) = (P' 0 (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω))
    (F : BoundedContinuousFunction (Path d) ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    ∫ ω, ∫ γ, F (rescalePath ε γ) ∂originLaw (P 0) ω ∂Q.measure =
      ∫ z, F (timeChangePath (rescalePath ε z.2, scaledInverseClock ε z))
        ∂Clock.PathMapV4.actualPhysicalInputPathLaw Q (P' 0) := by
  have hGm : Measurable fun γ : Path d => F (rescalePath ε γ) :=
    F.continuous.measurable.comp (continuous_rescalePath ε).measurable
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P 0) ω) := by
    filter_upwards [hTC, Q.regular, hprob'] with ω h hreg hp
    rw [originLaw_apply, h hreg]
    haveI : IsProbabilityMeasure (P' 0 (0, ω)) := hp
    exact inferInstance
  rw [← integral_physicalReferenceLaw Q (aestronglyMeasurable_quenchedIntegral Q (P 0) hprob hGm)]
  have hH : Measurable fun z : PhysicalInput d L × Path d => F (rescalePath ε (inverseClockPathMap z)) :=
    hGm.comp Clock.PathMapV4.measurable_inverseClockPathMap
  have hb : ∃ C : ℝ, ∀ z : PhysicalInput d L × Path d,
      |F (rescalePath ε (inverseClockPathMap z))| ≤ C :=
    ⟨‖F‖, fun z => by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _⟩
  have hfinal : ∫ z, F (rescalePath ε (inverseClockPathMap z))
      ∂Clock.PathMapV4.actualPhysicalInputPathLaw Q (P' 0) =
      ∫ z, F (timeChangePath (rescalePath ε z.2, scaledInverseClock ε z))
        ∂Clock.PathMapV4.actualPhysicalInputPathLaw Q (P' 0) := by
    congr 1
    funext z
    rw [rescalePath_inverseClockPathMap hε z]
  rw [← hfinal, integral_actualPhysicalInputPathLaw Q (P' 0) hprob' hH hb]
  apply integral_congr_ae
  filter_upwards [ae_physicalReferenceLaw Q hTC] with x hx
  have hmeas : Measurable fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath x.1 γ L x.2 :=
    (Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
      (measurable_const (a := x).prodMk measurable_id)
  rw [originLaw_apply, hx x.2, integral_map hmeas.aemeasurable hGm.aestronglyMeasurable]
  rfl

/-! ### The covariance identity -/

/-- **Time change of the diffusivity** (`paper/main.tex` 228-233). If the reduced diffusion has
diffusivity `ā`, its clock grows at rate `m > 0` along almost every path, and the physical
diffusion is its time change by the inverse clock, then the physical diffusion has diffusivity
`m⁻¹ ā`. -/
theorem hasDiffusivity_of_timeChange (Q : EnvironmentLaw d L r₀) (P P' : DiffusionFamily d)
    (hprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    (hTC : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular L ω,
      P 0 (0, ω) = (P' 0 (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω))
    {m : ℝ} (hm : 0 < m)
    (hErg : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' 0 (0, ω)),
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 m))
    {abar : Mat d} (hY : HasDiffusivity Q.measure (originLaw (P' 0)) abar) :
    HasDiffusivity Q.measure (originLaw (P 0)) (m⁻¹ • abar) := by
  obtain ⟨W, hW, hWlim⟩ := hY
  haveI : IsProbabilityMeasure W := hW.1
  set μY := Clock.PathMapV4.actualPhysicalInputPathLaw Q (P' 0) with hμY
  haveI : IsProbabilityMeasure μY :=
    Clock.PathMapV4.actualPhysicalInputPathLaw_isProbabilityMeasure Q (P' 0) hprob'
  have hred : ∀ (F : BoundedContinuousFunction (Path d) ℝ) (ε : ℝ),
      ∫ z, F (rescalePath ε z.2) ∂μY =
        ∫ ω, ∫ γ, F (rescalePath ε γ) ∂originLaw (P' 0) ω ∂Q.measure := by
    intro F ε
    have hGm : Measurable fun γ : Path d => F (rescalePath ε γ) :=
      F.continuous.measurable.comp (continuous_rescalePath ε).measurable
    have hH : Measurable fun z : PhysicalInput d L × Path d => F (rescalePath ε z.2) :=
      hGm.comp measurable_snd
    rw [hμY, integral_actualPhysicalInputPathLaw Q (P' 0) hprob' hH
      ⟨‖F‖, fun z => by rw [← Real.norm_eq_abs]; exact F.norm_coe_le_norm _⟩]
    exact integral_physicalReferenceLaw Q
      (aestronglyMeasurable_quenchedIntegral Q (P' 0) hprob' hGm)
  have hXd := tendstoInDistribution_rescalePath μY (path := fun z => z.2) measurable_snd (W := W)
    (fun F => (hWlim F).congr fun ε => (hred F ε).symm)
  have hτ := tendsto_measure_scaledInverseClock_not_mem Q (P' 0) hprob' hm hErg W
  have hpair := tendstoInDistribution_prodMk_of_tendsto_const hXd hτ
    (fun ε => ((measurable_scaledInverseClock ε).comp measurable_fst).aemeasurable)
  have hcomp := hpair.continuous_comp continuous_timeChangePath
  have hc : (((m⁻¹).toNNReal : ℝ)) = m⁻¹ := Real.coe_toNNReal _ (inv_nonneg.mpr hm.le)
  refine ⟨W.map (timeScalePath (m⁻¹).toNNReal), ?_, fun F => ?_⟩
  · have h := hW.timeScale (c := (m⁻¹).toNNReal)
    rwa [hc] at h
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hcomp.tendsto) F
  simp only [ProbabilityMeasure.coe_mk] at h1
  have hTm : Measurable (timeScalePath (d := d) (m⁻¹).toNNReal) :=
    (continuous_timeScalePath _).measurable
  have hgm : Measurable (timeChangePath ∘ fun p : (PhysicalInput d L × Path d) × Path d =>
      (p.2, linearClock m)) :=
    continuous_timeChangePath.measurable.comp (measurable_snd.prodMk measurable_const)
  have hlimit : ∫ y, F y ∂Measure.map (timeChangePath ∘ fun p : (PhysicalInput d L × Path d) ×
      Path d => (p.2, linearClock m)) (μY.prod W) =
      ∫ γ, F γ ∂W.map (timeScalePath (m⁻¹).toNNReal) := by
    rw [integral_map hgm.aemeasurable F.continuous.aestronglyMeasurable,
      integral_map hTm.aemeasurable F.continuous.aestronglyMeasurable]
    have hpt : ∀ p : (PhysicalInput d L × Path d) × Path d,
        F ((timeChangePath ∘ fun p : (PhysicalInput d L × Path d) × Path d =>
          (p.2, linearClock m)) p) = F (timeScalePath (m⁻¹).toNNReal p.2) := fun p => by
      simp only [Function.comp_apply, timeChangePath_linearClock hm]
    simp_rw [hpt]
    exact integral_prod_snd_of_prob μY W (integrable_bcf_comp W F hTm)
  rw [hlimit] at h1
  refine Tendsto.congr' ?_ h1
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hgε : Measurable (timeChangePath ∘ fun p : (PhysicalInput d L × Path d) × Path d =>
      (rescalePath ε ((fun z : PhysicalInput d L × Path d => z.2) p.1), scaledInverseClock ε p.1)) :=
    continuous_timeChangePath.measurable.comp
      (((continuous_rescalePath ε).measurable.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_scaledInverseClock ε).comp measurable_fst))
  have hHz : Measurable fun z : PhysicalInput d L × Path d =>
      timeChangePath (rescalePath ε z.2, scaledInverseClock ε z) :=
    continuous_timeChangePath.measurable.comp
      (((continuous_rescalePath ε).measurable.comp measurable_snd).prodMk
        (measurable_scaledInverseClock ε))
  rw [integral_map hgε.aemeasurable F.continuous.aestronglyMeasurable,
    physicalIntegral_eq Q P P' hprob' hTC F hε.ne']
  exact integral_prod_fst_of_prob μY W (integrable_bcf_comp μY F hHz)

/-- **Covariance identity of the time change** (`paper/main.tex` 228-233): the physical unforced
diffusivity is `m⁻¹ ā`. -/
theorem diffusivity_eq_of_timeChange (Q : EnvironmentLaw d L r₀) (P P' : DiffusionFamily d)
    (hprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    (hTC : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular L ω,
      P 0 (0, ω) = (P' 0 (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω))
    {m : ℝ} (hm : 0 < m)
    (hErg : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(P' 0 (0, ω)),
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 m))
    {abar : Mat d} (hY : HasDiffusivity Q.measure (originLaw (P' 0)) abar)
    {cov : Mat d} (hX : HasDiffusivity Q.measure (originLaw (P 0)) cov) :
    cov = m⁻¹ • abar :=
  hX.unique (hasDiffusivity_of_timeChange Q P P' hprob' hTC hm hErg hY)

/-- The mean clock density `E_Q μ = ∫ μ(0) dQ` is positive. -/
theorem meanClock_pos (Q : EnvironmentLaw d L r₀) :
    0 < ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure := by
  have hbd : ∀ᵐ ω ∂Q.measure,
      Real.exp (-2 * L) ≤ clockDensity ω 0 ∧ clockDensity ω 0 ≤ Real.exp (2 * L) := by
    filter_upwards [Q.regular] with ω hω
    exact clockDensity_bounds ω 0 L (hω.2.1 0)
  have hcont : Continuous (fun ω : FieldPair d => ω.2 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  have hcd : Continuous (fun ω : FieldPair d => clockDensity ω 0) := by
    unfold clockDensity
    exact Real.continuous_exp.comp (continuous_const.mul hcont)
  have hnorm : ∀ᵐ ω ∂Q.measure, ‖clockDensity ω 0‖ ≤ Real.exp (2 * L) := by
    filter_upwards [hbd] with ω hω
    rw [Real.norm_of_nonneg (clockDensity_pos ω 0).le]
    exact hω.2
  have hint : Integrable (fun ω : FieldPair d => clockDensity ω 0) Q.measure :=
    Integrable.of_bound hcd.aestronglyMeasurable _ hnorm
  have h := integral_mono_ae (integrable_const (Real.exp (-2 * L))) hint
    (hbd.mono fun ω hω => hω.1)
  rw [integral_const, probReal_univ, one_smul] at h
  exact (Real.exp_pos _).trans_le h

/-- The covariance half of the time-change identities, from the cited inputs
`External.TimeChangeLaw`,
`External.EnvironmentProcessErgodic` and `External.ReducedInvarianceAbar`: every unforced
diffusivity of a physical family is `(E_Q μ)⁻¹ ā`. -/
theorem physicalDiffusivity_eq_of_inputs (hTC : External.TimeChangeLaw)
    (hErg : External.EnvironmentProcessErgodic) (hIP : External.ReducedInvarianceAbar)
    (hd : 2 ≤ d) (Q : EnvironmentLaw d L r₀) (P P' : DiffusionFamily d)
    (hP : IsPhysicalDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P)
    (hP' : IsReducedDiffusionFamily (⟨0, by omega⟩ : Fin d) Q P')
    {cov : Mat d} (hX : HasDiffusivity Q.measure (originLaw (P 0)) cov) :
    cov = (∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure)⁻¹ •
      Matrix.of fun (j i : Fin d) =>
        WithLp.ofLp (@EinsteinRelation.Carriers.homogenizedCoefficientColumn d ⟨hd⟩ L r₀ Q i) j := by
  have hprob' : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω) := by
    filter_upwards [hP' 0 le_rfl] with ω hω using hω.1
  exact diffusivity_eq_of_timeChange Q P P' hprob' (hTC d hd L r₀ Q P P' hP hP' 0 le_rfl)
    (meanClock_pos Q) (hErg d hd L r₀ Q P' hP') (hIP d hd L r₀ Q P' hP') hX

end EinsteinRelation.TimeChangeCovariance
