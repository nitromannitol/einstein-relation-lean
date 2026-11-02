import EinsteinFull.Calculus.U5RegularKernelInvariance
import EinsteinFull.Calculus.U1GMPKernelL2
import EinsteinFull.Calculus.K11GMPRealizationFields
import EinsteinFull.Blueprint.G1.Proofs.SbxS4RemainderMoment

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- Absolute continuity of every positive-time marginal implies absolute
continuity of the positive-time averaged occupation measure. -/
theorem u2_averaged_occupation_ac_of_marginals {d : ℕ}
    (P : Measure (Path d)) [IsProbabilityMeasure P]
    (h : ∀ t : ℝ≥0, 0 < t →
      P.map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  refine Measure.AbsolutelyContinuous.mk fun N hN hnull => ?_
  have hsection : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ γ ∂P, γ t.toNNReal ∉ N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hz : (P.map (pathPosition t.toNNReal)) N = 0 := (h _ ht') hnull
    have hm := measure_eq_zero_iff_ae_notMem.mp hz
    exact (ae_map_iff (measurable_pathPosition _).aemeasurable hN.compl).mp hm
  have hprod : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))).prod P,
      z.2 z.1.toNNReal ∉ N := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2 hsection
    exact ((hN.preimage heval).compl).preimage measurable_swap
  have hswap : ∀ᵐ z ∂P.prod (volume.restrict (Set.Ioi (0 : ℝ))),
      z.1 z.2.toNNReal ∉ N :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
  rw [Measure.map_apply heval hN]
  exact measure_eq_zero_iff_ae_notMem.mpr hswap

/-- A volume-absolutely-continuous initial measure stays absolutely continuous
under the actual regular signed kernel, at every nonnegative time. -/
theorem u2_regular_kernel_preserves_volume_ac {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ν : Measure (Vec d))
    (hν : ν ≪ (volume : Measure (Vec d))) :
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∘ₘ ν ≪
      (volume : Measure (Vec d)) := by
  have hvμ : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd lam := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP
  have hμv : physicalReversibleMeasure ω hd lam ≪ (volume : Measure (Vec d)) := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mpr hP
  exact ((hν.trans hvμ).comp_right _).trans
    ((Measure.absolutelyContinuous_of_le
      (u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t)).trans hμv)


/-- Every physical L² representative is integrable against almost every
actual transition kernel. -/
theorem u2_regular_kernel_integrable_ae_L2 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      Integrable f (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
  have hfComp := hf.mono_measure
    (u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t)
  have hFiberEq : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      f =ᵐ[u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x]
        hfComp.aestronglyMeasurable.mk f :=
    Measure.ae_ae_of_ae_comp hfComp.aestronglyMeasurable.ae_eq_mk
  have hpowInt := hfComp.integrable_norm_rpow (by norm_num) (by simp)
  have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  let : IsProbabilityMeasure (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  have hxMeas : AEStronglyMeasurable f
      (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
    hfComp.aestronglyMeasurable.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  have hxMemLp : MemLp f 2
      (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) :=
    (integrable_norm_rpow_iff hxMeas (by norm_num) (by simp)).mp hxInt
  exact hxMemLp.integrable (by norm_num)

local instance : Fact (1 ≤ (2 : ℝ≥0)) := ⟨by norm_num⟩

/-- The canonical L² kernel operator agrees with the physical evolution. -/
theorem u2_regular_kernel_operator_L2 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) :
    let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
    let μ := physicalReversibleMeasure ω hd lam
    let hμ : P.IsSubInvariant μ :=
      (fun t => u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t)
    P.operatorFinite μ hμ 2 t = Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t := by
  dsimp only
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd lam
  let hμ : P.IsSubInvariant μ :=
    (fun t => u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t)
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense : Dense {F : Lp ℝ 2 μ |
      ∃ g : Vec d → ℝ, (F : Vec d → ℝ) =ᵐ[μ] g ∧
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  apply ContinuousLinearMap.ext
  have heq := Continuous.ext_on hdense
    (P.operatorFinite μ hμ 2 t).continuous
    (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t).continuous (by
      rintro F ⟨g, hFg, hgc, hgd⟩
      have hm := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam g hgd.continuous hgc
      have hF : F = hm.toLp g := Lp.ext (hFg.trans hm.coeFn_toLp.symm)
      apply Lp.ext
      calc
        (P.operatorFinite μ hμ 2 t F : Vec d → ℝ) =ᵐ[μ]
            MarkovProcess.kernelIntegral (P t) F :=
          P.isAssociatedFinite_operatorFinite μ hμ 2 t F
        _ =ᵐ[μ] MarkovProcess.kernelIntegral (P t) g :=
          MarkovProcess.kernelIntegral_congr_ae (hμ t) hFg
        _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hm.toLp g) : Vec d → ℝ) :=
          (u5_regular_integral_ae_L2_compact
            hd ω lam Λ hΛ hω t g hgd.continuous hgc).2
        _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F : Vec d → ℝ) := by rw [hF])
  exact fun x => congrFun heq x

/-- The actual kernel represents the physical L² semigroup for every L² input. -/
theorem u2_regular_kernel_integral_ae_L2 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam), Integrable f (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) ∧
    (∀ᵐ x ∂(physicalReversibleMeasure ω hd lam),
      (∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)) =
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) x) := by
  constructor
  · exact u2_regular_kernel_integrable_ae_L2 hd ω lam Λ hΛ hω t f hf
  · let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
    let μ := physicalReversibleMeasure ω hd lam
    let hμ : P.IsSubInvariant μ :=
      (fun t => u5_regular_kernel_subinvariant hd ω lam Λ hΛ hω t)
    have hchange := MarkovProcess.kernelIntegral_congr_ae (hμ t) hf.coeFn_toLp
    have hrepr := P.isAssociatedFinite_operatorFinite μ hμ 2 t (hf.toLp f)
    have hop := u2_regular_kernel_operator_L2 hd ω lam Λ hΛ hω t
    calc
      MarkovProcess.kernelIntegral (P t) f =ᵐ[μ]
          MarkovProcess.kernelIntegral (P t) (hf.toLp f) := hchange.symm
      _ =ᵐ[μ] (P.operatorFinite μ hμ 2 t (hf.toLp f) : Vec d → ℝ) := hrepr.symm
      _ =ᵐ[μ] (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f) : Vec d → ℝ) := by
        rw [hop]
        exact Filter.EventuallyEq.rfl

/-- Every weighted L² input is represented by the actual regular kernel. -/
theorem u2_regular_kernel_integral_ae_of_L2 {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      Integrable (fun y => f y) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) =
        (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f : Vec d → ℝ) x := by
  have h := u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω t f (Lp.memLp f)
  rw [Lp.toLp_coeFn] at h
  filter_upwards [h.1, h.2] with x hi he
  exact ⟨hi, he⟩


/-- The domain of the physical closed form is characterized by the actual kernel. -/
theorem u2_regular_kernel_closedForm_domain {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (f : Vec d → ℝ)
    (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    ((∃ C : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam (fun s => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s) t f ≤ C) ↔
      physicalH1Member ω hd lam f) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hquot (t : ℝ≥0) :
      semigroupFormDifferenceQuotient ω hd lam
          (fun s => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s) t f =
        (t : ℝ)⁻¹ * inner ℝ
          (hf.toLp f - Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))
          (hf.toLp f) := by
    have hk := (u2_regular_kernel_integral_ae_L2
      hd ω lam Λ hΛ hω t f hf).2
    unfold semigroupFormDifferenceQuotient
    rw [L2.inner_def]
    simp only [one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [hk, hf.coeFn_toLp,
      Lp.coeFn_sub (hf.toLp f) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))] with x hx hfx hs
    rw [hs]
    simp [Pi.sub_apply, hx, hfx, RCLike.inner_apply, mul_comm]
  have hh1 : physicalH1Member ω hd lam f ↔ physicalH1Member ω hd lam (hf.toLp f) := by
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans hf.coeFn_toLp.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.trans hf.coeFn_toLp⟩
  rw [hh1, ← Blueprint.gmpPhysicalSemigroup_bounded_formQuotient_iff hd ω lam Λ hΛ hω (hf.toLp f)]
  simp only [hquot]

/-- The actual kernel recovers the energy of any graph representing the same H¹ value. -/
theorem u2_regular_kernel_closedForm_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ)
    (q : SpatialDirichlet.DensityWeightedH1 (physicalForceWeight hd lam))
    (hq : SpatialDirichlet.densityWeightedH1Value (physicalForceWeight hd lam) q =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hu : u.value =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      (fun s => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s) t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 (physicalH1FormEnergy ω hd lam u)) := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let v := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q
  let F := Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
  have hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f := by
    have h := Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v
    rw [Blueprint.gmpForceH1_graphEquiv_value hd lam q] at h
    exact h.trans hq
  have hf : MemLp f 2 (physicalReversibleMeasure ω hd lam) := (Lp.memLp F).ae_eq hF
  have hFLp : hf.toLp f = F := Lp.ext (hf.coeFn_toLp.trans hF.symm)
  have hquot (t : ℝ≥0) :
      semigroupFormDifferenceQuotient ω hd lam
          (fun s => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s) t f =
        (t : ℝ)⁻¹ * inner ℝ
          (F - Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t F) F := by
    have hk := (u2_regular_kernel_integral_ae_L2
      hd ω lam Λ hΛ hω t f hf).2
    unfold semigroupFormDifferenceQuotient
    rw [← hFLp, L2.inner_def]
    simp only [one_div]
    congr 1
    apply integral_congr_ae
    filter_upwards [hk, hf.coeFn_toLp,
      Lp.coeFn_sub (hf.toLp f) (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hf.toLp f))] with x hx hfx hs
    rw [hs]
    simp [Pi.sub_apply, hx, hfx, RCLike.inner_apply, mul_comm]
  have hgv : g.value =ᵐ[physicalReversibleMeasure ω hd lam] u.value := by
    have hr := Blueprint.gmpH1Representative_value_ae (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
    have hp := (Measure.absolutelyContinuous_of_le_smul
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hr
    exact hp.trans ((Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v).symm.trans (hF.trans hu.symm))
  have hvol := (ae_withDensity_iff_volume_of_continuous_pos
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) _).mp hgv
  have hgrad := weakGradients_ae_eq_of_value_ae_eq hvol g.distributionalGradient u.distributionalGradient
  have hgradphys := (ae_withDensity_iff_volume_of_continuous_pos
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) _).mpr hgrad
  have henergy : physicalH1FormEnergy ω hd lam g = physicalH1FormEnergy ω hd lam u := by
    unfold physicalH1FormEnergy
    apply integral_congr_ae
    filter_upwards [hgradphys] with x hx
    simp only [weightedFormIntegrand, hx]
  have hmember : physicalH1Member ω hd lam F :=
    (Blueprint.gmpPhysicalH1Value_range_iff hd ω lam Λ hω F).mp ⟨v, rfl⟩
  have hlimit := Blueprint.gmpPhysicalSemigroup_formLimit hd ω lam Λ hΛ hω hmember hmember
  rw [Blueprint.gmpPhysicalClosedForm_value hd ω lam Λ hΛ hω v v,
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam Λ hω v,
    henergy] at hlimit
  simpa only [hquot] using hlimit



/- Real-valued version of the sigma-finite Bochner representative argument in
C1CrudeEnergyLargeTime. -/
private theorem u2_real_integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    ∫ x, ‖f x‖ ∂μ ≤ (μ Set.univ ^ (1 / 2 : ℝ)).toReal * ‖f‖ := by
  have hb : eLpNorm f 1 μ ≤ eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
    convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f) using 1
    norm_num
  have hfin : eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).ne
    finiteness
  have h := ENNReal.toReal_mono hfin hb
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ENNReal.toReal_mul, ← Lp.norm_def] at h
  simpa only [mul_comm] using h

private theorem u2_real_integrable_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    Integrable U (ν.prod μ) := by
  apply (integrable_prod_iff hU.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).integrable (by norm_num)).congr
    (heq t).symm), ?_⟩
  apply (hu.norm.const_mul (μ Set.univ ^ (1 / 2 : ℝ)).toReal).mono'
    (hU.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _)),
    integral_congr_ae ((heq t).mono (fun x h => congrArg norm h))]
  exact u2_real_integral_norm_le_l2 (u t)

private theorem u2_real_coeFn_integral_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi := u2_real_integrable_joint_l2_finite hu hU heq
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℝ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℝ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable U (ν.prod (μ.restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun t x => U (t, x)) hir]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)

/-- On each finite spatial set, a measurable representative of an integrable
physical L2 curve has the literal pointwise time integral prescribed by its
Bochner integral. Spatial volume need not be finite. -/
private theorem u2_real_coeFn_integral_joint_l2_local {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t)
    (K : Set Ω) (hK : μ K ≠ ⊤) :
    Integrable U (ν.prod (μ.restrict K)) ∧
      (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ.restrict K] fun x => ∫ t, U (t, x) ∂ν := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.lt_top⟩
  let C := LpToLpRestrictCLM Ω ℝ ℝ μ 2 K
  have hC : Integrable (fun t => C (u t)) ν := C.integrable_comp hu
  have hrep : ∀ t, (fun x => U (t, x)) =ᵐ[μ.restrict K] C (u t) := by
    intro t
    have ht : (fun x => U (t, x)) =ᵐ[μ.restrict K] (u t : Ω → ℝ) :=
      ae_restrict_of_ae (heq t)
    exact ht.trans (LpToLpRestrictCLM_coeFn ℝ K (u t)).symm
  refine ⟨u2_real_integrable_joint_l2_finite hC hU hrep, ?_⟩
  have hi := u2_real_coeFn_integral_joint_l2_finite hC hU hrep
  rw [C.integral_comp_comm hu] at hi
  exact (LpToLpRestrictCLM_coeFn ℝ K (∫ t, u t ∂ν)).symm.trans hi

/-- The L² Bochner integral agrees with the time integral of a joint
representative on a sigma-finite spatial measure. Finite restrictions justify
the identification before taking a countable spatial union. -/
theorem u2_real_coeFn_integral_joint_l2_sigmaFinite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℝ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℝ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi (n : ℕ) := (u2_real_coeFn_integral_joint_l2_local hu hU heq
    (spanningSets μ n) (measure_spanningSets_lt_top μ n).ne).2
  have h := (ae_restrict_iUnion_iff (spanningSets μ)
    (fun x => (∫ t, u t ∂ν) x = ∫ t, U (t, x) ∂ν)).mpr hi
  simpa only [iUnion_spanningSets, Measure.restrict_univ, Filter.EventuallyEq] using h


/-- The actual regular kernel satisfies the compact-test Dynkin identity
for almost every starting point, at each fixed time. -/
theorem u2_regular_kernel_compactTest_dynkin_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ≥0) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) - φ x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x := by
  let μ := physicalReversibleMeasure ω hd lam
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let S := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let F := Blueprint.gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  let hg := sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc
  let G := hg.toLp (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
  let U := fun p : ℝ × Vec d => ∫ y,
    physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal p.1) p.2
  obtain ⟨B, hB, hU, hbound⟩ :=
    u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hcont : Continuous (fun s : ℝ => S (Real.toNNReal s) G) :=
    (S.continuous_orbit G).comp continuous_real_toNNReal
  have hint : Integrable (fun s : ℝ => S (Real.toNNReal s) G)
      (volume.restrict (Set.Ioc 0 (t : ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp (hcont.intervalIntegrable 0 t)
  have hrep : ∀ s : ℝ, (fun x => U (s, x)) =ᵐ[μ] S (Real.toNNReal s) G := by
    intro s
    exact (u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω
      (Real.toNNReal s) _ hg).2
  have htime := u2_real_coeFn_integral_joint_l2_sigmaFinite hint hU hrep
  have hf := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam φ hφ.continuous hc
  have hF : hf.toLp φ = F := Lp.ext
    (hf.coeFn_toLp.trans (Blueprint.gmpPhysicalH1Value_compactTest hd ω lam Λ hω φ hφ hc).symm)
  have hp := (u2_regular_kernel_integral_ae_L2 hd ω lam Λ hΛ hω t φ hf).2
  rw [hF] at hp
  have he := u2_regular_semigroup_compactTest_evolution hd ω lam Λ hΛ hω φ hφ hc t
  change S t F - F = ∫ s in (0 : ℝ)..(t : ℝ), S (Real.toNNReal s) G at he
  rw [intervalIntegral.integral_of_le t.coe_nonneg] at he
  filter_upwards [hp, Blueprint.gmpPhysicalH1Value_compactTest hd ω lam Λ hω φ hφ hc,
    Lp.coeFn_sub (S t F) F, htime] with x hpx hfx hsub ht
  change (S t F - F) x = S t F x - F x at hsub
  rw [intervalIntegral.integral_of_le t.coe_nonneg]
  rw [hpx, ← hfx, ← hsub, he]
  exact ht

/-- The regular transition kernels compose on every bounded measurable observable. -/
theorem u2_regular_kernel_integral_add {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (s t : ℝ≥0) (x : Vec d) (f : Vec d → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ y, ‖f y‖ ≤ B) :
    (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (s + t) x) =
      ∫ z, (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z) ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsProbabilityMeasure (P (s + t) x) :=
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω (s + t) x⟩
  have hi : Integrable f (P (s + t) x) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)
  have hi' : Integrable f ((P t ∘ₖ P s) x) := by
    rw [← P.add]
    exact hi
  change (∫ y, f y ∂P (s + t) x) = _
  rw [P.add]
  exact Kernel.integral_comp hi'

/-- The bounded generator orbit can be integrated over time and a regular
transition law in either order, for every starting point. -/
theorem u2_regular_generator_orbit_integral_swap {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (r t : ℝ≥0) (x : Vec d) :
    (∫ z, (∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) z) ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) =
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ z, (∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) z) ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsProbabilityMeasure (P r x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω r x⟩
  let : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    infer_instance
  obtain ⟨B, hB, hmeas, hbound⟩ :=
    u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hi : Integrable (fun p : ℝ × Vec d => ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂P (Real.toNNReal p.1) p.2)
      ((volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))).prod (P r x)) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using hbound (Real.toNNReal p.1) p.2
  exact (intervalIntegral_integral_swap hi).symm

/-- The compact-test Dynkin identity holds after averaging over any finite
absolutely continuous initial measure, without a point-start density assumption. -/
theorem u2_regular_kernel_compactTest_dynkin_of_ac_initial {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ≥0) (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (hac : ν ≪ physicalReversibleMeasure ω hd lam) :
    (∫ z, (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z) ∂ν) -
    (∫ z, φ z ∂ν) =
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ z, (∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) z) ∂ν := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let f := Blueprint.gmpPhysicalCompactC0 φ hφ.continuous hc
  let ft := u2RegularC0Semigroup hd ω lam Λ hΛ hω t f
  have hft (z : Vec d) : (∫ y, φ y ∂P t z) = ft z := by
    exact u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f z
  have hi : Integrable (fun z => ∫ y, φ y ∂P t z) ν := by
    simp_rw [hft]
    exact Integrable.of_bound ft.continuous.measurable.aestronglyMeasurable ‖ft.toBCF‖
      (ae_of_all _ fun z => BoundedContinuousFunction.norm_coe_le_norm ft.toBCF z)
  have hφi : Integrable φ ν := hφ.continuous.integrable_of_hasCompactSupport hc
  let : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))) := by
    rw [Set.uIoc_of_le t.coe_nonneg]
    infer_instance
  obtain ⟨B, hB, hmeas, hbound⟩ :=
    u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hjoint : Integrable (fun p : ℝ × Vec d => ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂P (Real.toNNReal p.1) p.2)
      ((volume.restrict (Set.uIoc (0 : ℝ) (t : ℝ))).prod ν) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable B
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using hbound (Real.toNNReal p.1) p.2
  rw [← integral_sub hi hφi]
  calc
    _ = ∫ z, (∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂P (Real.toNNReal s) z) ∂ν := by
      apply integral_congr_ae
      exact hac.ae_le (u2_regular_kernel_compactTest_dynkin_ae hd ω lam Λ hΛ hω φ hφ hc t)
    _ = _ := (intervalIntegral_integral_swap hjoint).symm


/-- Positive-time absolute continuity transfers the fixed-time almost-everywhere
Dynkin identity through the actual regular transition kernel. -/
theorem u2_regular_kernel_compactTest_dynkin_after_transition {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (r t : ℝ≥0) (x : Vec d)
    (hac : u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x ≪
      physicalReversibleMeasure ω hd lam) :
    (∫ z, (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z) ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) -
    (∫ z, φ z ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) =
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ z, (∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) z) ∂
          u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsProbabilityMeasure (P r x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω r x⟩
  let f := Blueprint.gmpPhysicalCompactC0 φ hφ.continuous hc
  let ft := u2RegularC0Semigroup hd ω lam Λ hΛ hω t f
  have hft (z : Vec d) : (∫ y, φ y ∂P t z) = ft z := by
    exact u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t f z
  have hi : Integrable (fun z => ∫ y, φ y ∂P t z) (P r x) := by
    simp_rw [hft]
    exact Integrable.of_bound ft.continuous.measurable.aestronglyMeasurable ‖ft.toBCF‖
      (ae_of_all _ fun z => BoundedContinuousFunction.norm_coe_le_norm ft.toBCF z)
  have hφi : Integrable φ (P r x) := hφ.continuous.integrable_of_hasCompactSupport hc
  rw [← integral_sub hi hφi]
  calc
    _ = ∫ z, (∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂P (Real.toNNReal s) z) ∂P r x := by
      apply integral_congr_ae
      exact hac.ae_le (u2_regular_kernel_compactTest_dynkin_ae hd ω lam Λ hΛ hω φ hφ hc t)
    _ = _ := u2_regular_generator_orbit_integral_swap hd ω lam Λ hΛ hω φ hφ hc r t x

/-- The bounded generator orbit has a continuous time primitive at each start. -/
theorem u2_regular_generator_orbit_primitive_continuous {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (x : Vec d) :
    Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (Real.toNNReal s) x) := by
  obtain ⟨B, hB, hm, hb⟩ :=
    u2_regular_kernel_compactTest_generator_orbit hd ω lam Λ hΛ hω φ hφ hc
  have hm' := hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => x)))
  apply intervalIntegral.continuous_primitive
  intro a b
  apply (intervalIntegrable_const (c := B)).mono_fun hm'.aestronglyMeasurable
  filter_upwards with s
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, Real.norm_of_nonneg hB] using
    hb (Real.toNNReal s) x

/-- The regular Dynkin formula after a positive transition, written entirely
with the original transition kernels. -/
theorem u2_regular_kernel_compactTest_dynkin_shifted {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (r t : ℝ≥0) (x : Vec d)
    (hac : u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x ≪
      physicalReversibleMeasure ω hd lam) :
    (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + t) x) -
    (∫ y, φ y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) =
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + Real.toNNReal s) x := by
  let f := Blueprint.gmpPhysicalCompactC0 φ hφ.continuous hc
  have hfbound : ∀ y, ‖φ y‖ ≤ ‖f.toBCF‖ := fun y =>
    BoundedContinuousFunction.norm_coe_le_norm f.toBCF y
  obtain ⟨B, hB, hg⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hφ hc
  have hadd := u2_regular_kernel_integral_add hd ω lam Λ hΛ hω r t x φ
    hφ.continuous.measurable ‖f.toBCF‖ hfbound
  rw [hadd]
  rw [u2_regular_kernel_compactTest_dynkin_after_transition hd ω lam Λ hΛ hω φ hφ hc r t x hac]
  apply intervalIntegral.integral_congr
  intro s hs
  exact (u2_regular_kernel_integral_add hd ω lam Λ hΛ hω r (Real.toNNReal s) x
    (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
    (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam φ) B
    (fun y => by simpa only [Real.norm_eq_abs] using hg y)).symm

/-- A bounded measurable function has the usual shifted primitive identity. -/
theorem u2_bounded_orbit_primitive_shift (H : ℝ → ℝ) (hm : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ s, ‖H s‖ ≤ B) (r t : ℝ) :
    (∫ s in (0 : ℝ)..t, H (s + r)) =
      (∫ s in (0 : ℝ)..(r + t), H s) - ∫ s in (0 : ℝ)..r, H s := by
  have hi (a b : ℝ) : IntervalIntegrable H volume a b := by
    apply (intervalIntegrable_const (c := B)).mono_fun hm.aestronglyMeasurable
    filter_upwards with s
    simpa only [Real.norm_of_nonneg hB] using hb s
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r (r + t))
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add, add_comm t r]
  linarith

/-- The actual regular kernel and any of its continuous-path realizations
satisfy all fixed-environment GMP fields when the positive-time kernels have
Lebesgue densities. -/
theorem u2_regular_fixed_environment_realization_of_ac_fdd
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d))) :
    ∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1,
      R.pathLaw = K ∧ R.transitionKernel = fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  have hP : P.IsConservative := u2_regular_kernel_conservative hd ω lam Λ hΛ hω
  refine ⟨{
    pathLaw := K
    transitionKernel := fun t => P t
    heatKernel := fun t x => (P t x).rnDeriv volume
    pathLaw_isMarkovKernel := inferInstance
    transitionKernel_isMarkovKernel := hP.isMarkovKernel
    transitionKernel_zero := P.kernel_zero
    transitionKernel_add := P.kernel_add
    transitionKernel_reversible := ?_
    pathLaw_starts_at := Blueprint.k11_starts_at P K hfdd
    heatKernel_aeMeasurable := ?_
    transitionKernel_eq_heatKernel := ?_
    pathLaw_endpoint := Blueprint.k11_endpoint P K hfdd
    pathLaw_ordered_finite_dimensional := ?_
    closedForm_domain := ?_
    closedForm_value := ?_
  }, rfl, rfl⟩
  · intro t A B hA hB
    exact u5_regular_kernel_measurable_rectangles hd ω lam Λ hΛ hω t A B hA hB
  · intro t ht x
    exact (Measure.measurable_rnDeriv _ _).aemeasurable
  · intro t ht x
    let : IsProbabilityMeasure (P t x) := ⟨hP t x⟩
    exact (Measure.withDensity_rnDeriv_eq _ _ (hac t ht x)).symm
  · intro increments x F hF hbounded
    obtain ⟨B, hB⟩ := hbounded
    exact Blueprint.k11_fdd_general P hP K hfdd increments x F hF B hB
  · intro f hf
    exact u2_regular_kernel_closedForm_domain hd ω lam Λ hΛ hω f hf
  · intro f q hq u hu
    exact u2_regular_kernel_closedForm_value hd ω lam Λ hΛ hω f q hq u hu

/-- The same continuous-path realization supplies the GMP fields and solves
the physical martingale problem at every starting point. -/
theorem u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d))) :
    (∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1,
      R.pathLaw = K ∧ R.transitionKernel = fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t) ∧
    ∀ x : Vec d, SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) ω lam) x (K x) := by
  obtain ⟨R, hK, hP⟩ := u2_regular_fixed_environment_realization_of_ac_fdd
    hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  refine ⟨⟨R, hK, hP⟩, ?_⟩
  intro x
  rw [← hK]
  exact SbxS4Dynkin.actual_solves_martingale_problem hd hΛ R x

/-- Every measurable GMP origin law solves the physical martingale problem
under that very same kernel, without a smoothness assumption. -/
theorem u2_gmp_physical_origin_law_solves_mp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (K : Kernel (FieldPair d) (Path d))
    (hK : IsGMPPhysicalOriginLaw hd hΛ Q lam h0 h1 K) :
    ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω) := by
  filter_upwards [hK] with ω hω
  obtain ⟨_, R, hR⟩ := hω
  rw [hR]
  exact SbxS4Dynkin.actual_solves_martingale_problem hd hΛ R 0












end EinsteinFull
