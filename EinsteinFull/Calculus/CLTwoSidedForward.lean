import EinsteinFull.Calculus.CLTwoSidedMarkov

/-!
# Forward path functionals of the two-sided process

Given the states up to time zero, the forward displacement path has the law of the environment
kernel path from the state at time zero. For an integrable functional `G` of the environment at
time zero and the forward path, the conditional expectation given the past is the kernel mean of
`G`. This gives DFGW's mean forward velocity (2.39) and, with stationarity, the martingale
property (2.40) relative to the past filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- Equal set integrals of integrable functions over a generating pi-system, and over the whole
space, give equal set integrals over the generated sigma-algebra. -/
theorem setIntegral_eq_of_generate_integrable {α : Type*} {m m₀ : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m₀) (C : Set (Set α)) (hC : IsPiSystem C)
    (hgen : m = MeasurableSpace.generateFrom C) {X Y : α → ℝ} (hX : Integrable X μ)
    (hY : Integrable Y μ) (hCeq : ∀ s ∈ C, ∫ ω in s, X ω ∂μ = ∫ ω in s, Y ω ∂μ)
    (huniv : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂μ) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫ ω in s, X ω ∂μ = ∫ ω in s, Y ω ∂μ := by
  have hCm : ∀ s ∈ C, MeasurableSet s := fun s hsC => hm _ (hgen ▸
    MeasurableSpace.measurableSet_generateFrom hsC)
  let P : α → ℝ := fun ω => max (X ω) 0 + max (-Y ω) 0
  let N : α → ℝ := fun ω => max (Y ω) 0 + max (-X ω) 0
  have hP : Integrable P μ := hX.pos_part.add hY.neg_part
  have hN : Integrable N μ := hY.pos_part.add hX.neg_part
  have hP0 : ∀ ω, 0 ≤ P ω := fun ω => add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hN0 : ∀ ω, 0 ≤ N ω := fun ω => add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hdiff : ∀ t, ∫ ω in t, P ω ∂μ - ∫ ω in t, N ω ∂μ =
      ∫ ω in t, X ω ∂μ - ∫ ω in t, Y ω ∂μ := by
    intro t
    rw [← integral_sub hP.restrict hN.restrict, ← integral_sub hX.restrict hY.restrict]
    congr 1
    funext ω
    have h1 := max_zero_sub_max_neg_zero_eq_self (X ω)
    have h2 := max_zero_sub_max_neg_zero_eq_self (Y ω)
    simp only [P, N]
    linarith
  have hν : ∀ (Z : α → ℝ), Integrable Z μ → (∀ ω, 0 ≤ Z ω) → ∀ t, MeasurableSet t →
      μ.withDensity (fun ω => ENNReal.ofReal (Z ω)) t = ENNReal.ofReal (∫ ω in t, Z ω ∂μ) := by
    intro Z hZ hZ0 t ht
    rw [withDensity_apply _ ht, ← ofReal_integral_eq_lintegral_ofReal hZ.restrict
      (ae_of_all _ hZ0)]
  have : IsFiniteMeasure (μ.withDensity fun ω => ENNReal.ofReal (P ω)) :=
    isFiniteMeasure_withDensity_ofReal hP.2
  have heq : μ.withDensity (fun ω => ENNReal.ofReal (P ω)) s =
      μ.withDensity (fun ω => ENNReal.ofReal (N ω)) s := by
    refine ext_on_measurableSpace_of_generate_finite m₀ C (fun t htC => ?_) hm hgen hC ?_ hs
    · rw [hν P hP hP0 t (hCm t htC), hν N hN hN0 t (hCm t htC)]
      congr 1
      have := hdiff t
      rw [hCeq t htC, sub_self] at this
      linarith
    · rw [hν P hP hP0 _ MeasurableSet.univ, hν N hN hN0 _ MeasurableSet.univ]
      congr 1
      have := hdiff Set.univ
      simp only [setIntegral_univ] at this ⊢
      rw [huniv, sub_self] at this
      linarith
  have hsm : MeasurableSet s := hm _ hs
  rw [hν P hP hP0 s hsm, hν N hN hN0 s hsm] at heq
  have h := (ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg hsm fun ω _ => hP0 ω)
    (setIntegral_nonneg hsm fun ω _ => hN0 ω)).1 heq
  have := hdiff s
  rw [h, sub_self] at this
  linarith

/-- The forward displacement path. -/
def tsFwdPath (ω : TwoSidedSpace d) : Path d :=
  ⟨fun t => ω.2 t - ω.2 0, (ω.2.continuous.comp NNReal.continuous_coe).sub continuous_const⟩

theorem measurable_tsFwdPath : Measurable (tsFwdPath (d := d)) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  exact ((ContinuousMap.measurable_eval _).comp measurable_snd).sub
    ((ContinuousMap.measurable_eval _).comp measurable_snd)

theorem tsFwdPath_glue (ω₀ : aperiodicSet d) (p : Path d × Path d) (h0 : p.1 0 = 0) :
    tsFwdPath (ω₀, gluePath p) = p.1 := by
  ext t j
  simp [tsFwdPath, gluePath_nnreal, gluePath_zero, h0]

/-- The environment kernel from the origin. -/
def originKernel (K : Kernel (FieldPair d × Vec d) (Path d)) : Kernel (FieldPair d) (Path d) :=
  K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)

instance (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] :
    IsMarkovKernel (originKernel K) := by
  unfold originKernel
  infer_instance


open Classical in
/-- A past box event is the product of an observable at time zero and a backward product. -/
theorem tsPastWindow_box_indicator (h : ℝ≥0) (N : ℕ) (A : Fin (N + 1) → Set (FieldPair d))
    (ω : TwoSidedSpace d) :
    (tsPastWindow h N ⁻¹' Set.pi Set.univ A).indicator (fun _ => (1 : ℝ)) ω =
      (A 0).indicator (fun _ => (1 : ℝ)) (tsState 0 ω) *
        tsBwdProd (gridGaps h (List.ofFn fun k : Fin N => (A k.succ).indicator fun _ => (1 : ℝ)))
          0 ω := by
  have hiff : ω ∈ tsPastWindow h N ⁻¹' Set.pi Set.univ A ↔ (tsState 0 ω ∈ A 0 ∧
      ∀ k : Fin N, tsState (0 - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k.succ) := by
    have he : ∀ k : Fin N, -((((k.succ : Fin (N + 1)) : ℕ) : ℝ)) * (h : ℝ) =
        0 - (((k : ℕ) : ℝ) + 1) * h := by
      intro k
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
    simp only [Set.mem_preimage, Set.mem_univ_pi, tsPastWindow]
    rw [Fin.forall_fin_succ]
    simp only [Fin.val_zero, Nat.cast_zero, neg_zero, zero_mul, he]
  rw [tsBwdProd_ofFn_indicator]
  simp only [Set.indicator_apply]
  by_cases h0 : tsState 0 ω ∈ A 0 <;> simp [hiff, h0]

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hap in
theorem integrable_glue_fwd {G : FieldPair d × Path d → ℝ} (hG : Measurable G)
    (hGi : Integrable G (Q.measure ⊗ₘ originKernel K)) :
    Integrable (fun z : aperiodicSet d × (Path d × Path d) => G ((z.1 : FieldPair d), z.2.1))
      ((apLaw Q) ⊗ₘ (apOriginKernel K ×ₖ apOriginKernel K)) := by
  have := apLaw_isProbability Q hap
  let κ := apOriginKernel K ×ₖ apOriginKernel K
  have hπ : Measurable fun z : aperiodicSet d × (Path d × Path d) =>
      ((z.1 : FieldPair d), z.2.1) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hGi' := (Measure.integrable_compProd_iff hG.aestronglyMeasurable).1 hGi
  rw [Measure.integrable_compProd_iff (show Measurable (fun z : aperiodicSet d × (Path d × Path d) =>
    G ((z.1 : FieldPair d), z.2.1)) from hG.comp hπ).aestronglyMeasurable]
  constructor
  · filter_upwards [ae_apLaw Q hap hGi'.1] with ω₀ hω₀
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.fst =
        apOriginKernel K ω₀ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    change Integrable (fun p : Path d × Path d => G ((ω₀ : FieldPair d), p.1)) (κ ω₀)
    rw [Kernel.prod_apply]
    have h : Integrable (fun γ => G ((ω₀ : FieldPair d), γ))
        (((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.fst) := by
      rw [hmap]
      exact hω₀
    exact h.comp_measurable measurable_fst
  · have hfun : (fun ω₀ : aperiodicSet d => ∫ p, ‖G ((ω₀ : FieldPair d), p.1)‖ ∂κ ω₀) =
        (fun ω => ∫ γ, ‖G (ω, γ)‖ ∂originKernel K ω) ∘ Subtype.val := by
      funext ω₀
      simp only [Function.comp, κ]
      rw [Kernel.prod_apply, integral_fun_fst (fun γ : Path d => ‖G ((ω₀ : FieldPair d), γ)‖),
        probReal_univ, one_smul]
      rfl
    rw [hfun, ← (MeasurableEmbedding.subtype_coe
      (measurableSet_aperiodicSet d)).integrable_map_iff, map_val_apLaw Q hap]
    exact hGi'.2

include hap hK in
theorem ae_glue_fwd_zero :
    ∀ᵐ z ∂((apLaw Q) ⊗ₘ (apOriginKernel K ×ₖ apOriginKernel K)), z.2.1 0 = 0 := by
  refine Measure.ae_compProd_of_ae_ae ?_ ?_
  · exact measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp
      (measurable_fst.comp measurable_snd)) measurable_const
  · filter_upwards [ae_apLaw Q hap Q.regular] with ω₀ hreg
    have h0 : ∀ᵐ γ ∂(apOriginKernel K ω₀), γ 0 = 0 := (hK ω₀ hreg 0).2.1
    rw [Kernel.prod_apply]
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.fst =
        apOriginKernel K ω₀ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← hmap] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0

include hap hK in
theorem integrable_tsLaw_split_fwd {F₀ : FieldPair d → ℝ} (hF₀ : Measurable F₀)
    (hF₀b : ∀ ω, |F₀ ω| ≤ 1) {Lb : List (ℝ≥0 × (FieldPair d → ℝ))}
    (hLb : IsUnitObservables Lb) {G : FieldPair d × Path d → ℝ} (hG : Measurable G)
    (hGi : Integrable G (Q.measure ⊗ₘ originKernel K)) :
    Integrable (fun ω => F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * G (tsState 0 ω, tsFwdPath ω))
      (tsLaw Q K) := by
  obtain ⟨hbm, hbb⟩ := tsBwdProd_measurable_bound Lb hLb 0
  have hΦm : Measurable fun ω =>
      F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * G (tsState 0 ω, tsFwdPath ω) :=
    ((hF₀.comp (measurable_tsState 0)).mul hbm).mul
      (hG.comp ((measurable_tsState 0).prodMk measurable_tsFwdPath))
  rw [tsLaw, integrable_map_measure hΦm.aestronglyMeasurable measurable_tsGlue.aemeasurable]
  refine Integrable.mono' (integrable_glue_fwd D Q hap hG hGi).norm
    (hΦm.comp measurable_tsGlue).aestronglyMeasurable ?_
  filter_upwards [ae_glue_fwd_zero hd D Q hap hK] with z hz
  simp only [Function.comp, tsState_zero_glue, tsFwdPath_glue z.1 z.2 hz, Real.norm_eq_abs,
    abs_mul]
  calc |F₀ (z.1 : FieldPair d)| * |tsBwdProd Lb 0 (z.1, gluePath z.2)| *
        |G ((z.1 : FieldPair d), z.2.1)| ≤ 1 * 1 * |G ((z.1 : FieldPair d), z.2.1)| := by
        gcongr
        · exact hF₀b _
        · exact hbb _
    _ = |G ((z.1 : FieldPair d), z.2.1)| := by ring

include hap hK in
/-- Split formula with an integrable functional of the environment at time zero and the forward
path. -/
theorem integral_tsLaw_split_fwd {F₀ : FieldPair d → ℝ} (hF₀ : Measurable F₀)
    (hF₀b : ∀ ω, |F₀ ω| ≤ 1) {Lb : List (ℝ≥0 × (FieldPair d → ℝ))}
    (hLb : IsUnitObservables Lb) {G : FieldPair d × Path d → ℝ} (hG : Measurable G)
    (hGi : Integrable G (Q.measure ⊗ₘ originKernel K)) :
    ∫ ω, F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * G (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K =
      ∫ ω, F₀ ω * chainMean K Lb ω * ∫ γ, G (ω, γ) ∂K (ω, 0) ∂Q.measure := by
  have := apLaw_isProbability Q hap
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨hbm, hbb⟩ := tsBwdProd_measurable_bound Lb hLb 0
  let Φ : TwoSidedSpace d → ℝ := fun ω =>
    F₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * G (tsState 0 ω, tsFwdPath ω)
  have hΦm : Measurable Φ := ((hF₀.comp (measurable_tsState 0)).mul hbm).mul
    (hG.comp ((measurable_tsState 0).prodMk measurable_tsFwdPath))
  have hint : Integrable (fun z : aperiodicSet d × (Path d × Path d) => Φ (z.1, gluePath z.2))
      ((apLaw Q) ⊗ₘ (apOriginKernel K ×ₖ apOriginKernel K)) := by
    have h := integrable_tsLaw_split_fwd hd D Q hap hK hF₀ hF₀b hLb hG hGi
    rw [tsLaw, integrable_map_measure hΦm.aestronglyMeasurable
      measurable_tsGlue.aemeasurable] at h
    exact h
  change ∫ ω, Φ ω ∂tsLaw Q K = _
  rw [tsLaw, integral_map measurable_tsGlue.aemeasurable hΦm.aestronglyMeasurable,
    Measure.integral_compProd hint, ← integral_apLaw Q hap]
  apply integral_congr_ae
  filter_upwards [ae_apLaw Q hap Q.regular] with ω₀ hreg
  have hK0 := hK ω₀ hreg 0
  rw [Kernel.prod_apply]
  have h0 : ∀ᵐ γ ∂(apOriginKernel K ω₀), γ 0 = 0 := hK0.2.1
  have h1 : ∀ᵐ z ∂((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)), z.1 0 = 0 := by
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.fst =
        apOriginKernel K ω₀ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← hmap] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0
  have h2 : ∀ᵐ z ∂((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)), z.2 0 = 0 := by
    have h0' : ∀ᵐ γ ∂(apOriginKernel K ω₀), γ 0 = 0 := hK0.2.1
    have hmap : ((apOriginKernel K ω₀).prod (apOriginKernel K ω₀)).map Prod.snd =
        apOriginKernel K ω₀ := by rw [Measure.map_snd_prod, measure_univ, one_smul]
    rw [← hmap] at h0'
    exact ae_of_ae_map measurable_snd.aemeasurable h0'
  have hcongr : (fun p : Path d × Path d => Φ (ω₀, gluePath p)) =ᵐ[(apOriginKernel K ω₀).prod
      (apOriginKernel K ω₀)] fun p => F₀ ω₀ * (G ((ω₀ : FieldPair d), p.1) *
        chainProd Lb 0 p.2 ω₀) := by
    filter_upwards [h1, h2] with p hp1 hp2
    simp only [Φ, tsState_zero_glue, tsFwdPath_glue ω₀ p hp1]
    have hb := tsBwdProd_glue Lb 0 ω₀ p hp2
    simp only [NNReal.coe_zero, neg_zero] at hb
    rw [hb]
    ring
  rw [integral_congr_ae hcongr, integral_const_mul]
  have hpm := integral_prod_mul (μ := apOriginKernel K ω₀) (ν := apOriginKernel K ω₀)
    (fun Y : Path d => G ((ω₀ : FieldPair d), Y))
    (fun Y : Path d => chainProd Lb 0 Y (ω₀ : FieldPair d))
  rw [hpm]
  simp only [apOriginKernel, Kernel.comap_apply]
  rw [integral_chainProd hd hΛ hK Lb hLb _ hreg]
  ring


include hap hK in
/-- The conditional law of the forward path given the past: for an integrable functional of the
environment at time zero and the forward path, the conditional expectation given the states up to
time zero is its kernel mean. -/
theorem tsLaw_condExp_fwd {G : FieldPair d × Path d → ℝ} (hG : Measurable G)
    (hGi : Integrable G (Q.measure ⊗ₘ originKernel K)) :
    (tsLaw Q K)[fun ω => G (tsState 0 ω, tsFwdPath ω) | tsPastSigma d] =ᵐ[tsLaw Q K]
      fun ω => ∫ γ, G (tsState 0 ω, γ) ∂K (tsState 0 ω, 0) := by
  have := tsLaw_isProbability Q hap K
  let Φ : FieldPair d → ℝ := fun x => ∫ γ, G (x, γ) ∂originKernel K x
  have hΦs : StronglyMeasurable Φ := hG.stronglyMeasurable.integral_kernel_prod_right'
  have hΦm : Measurable Φ := hΦs.measurable
  have hGi' := (Measure.integrable_compProd_iff hG.aestronglyMeasurable).1 hGi
  have hΦi : Integrable Φ Q.measure := by
    refine Integrable.mono' hGi'.2 hΦs.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    exact norm_integral_le_integral_norm _
  let G' : FieldPair d × Path d → ℝ := fun z => Φ z.1
  have hG'm : Measurable G' := hΦm.comp measurable_fst
  have hG'i : Integrable G' (Q.measure ⊗ₘ originKernel K) := by
    have hmap : (Q.measure ⊗ₘ originKernel K).map Prod.fst = Q.measure := by
      rw [← Measure.fst, Measure.fst_compProd]
    have h : Integrable Φ ((Q.measure ⊗ₘ originKernel K).map Prod.fst) := by rw [hmap]; exact hΦi
    exact h.comp_measurable measurable_fst
  have hG'int : ∀ x, ∫ γ, G' (x, γ) ∂K (x, 0) = Φ x := by
    intro x
    simp only [G', integral_const, probReal_univ, one_smul]
  have hcand : (fun ω => ∫ γ, G (tsState 0 ω, γ) ∂K (tsState 0 ω, 0)) =
      fun ω => G' (tsState 0 ω, tsFwdPath ω) := rfl
  rw [hcand]
  have hYi : Integrable (fun ω => G (tsState 0 ω, tsFwdPath ω)) (tsLaw Q K) := by
    have h := integrable_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
      (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim) hG hGi
    simpa only [tsBwdProd, one_mul] using h
  have hXi : Integrable (fun ω => G' (tsState 0 ω, tsFwdPath ω)) (tsLaw Q K) := by
    have h := integrable_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
      (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim) hG'm hG'i
    simpa only [tsBwdProd, one_mul] using h
  -- equality on past boxes
  have hbox : ∀ (h : ℝ≥0) (N : ℕ) (A : Fin (N + 1) → Set (FieldPair d)),
      (∀ k, MeasurableSet (A k)) →
      ∫ ω in tsPastWindow h N ⁻¹' Set.pi Set.univ A, G' (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K =
        ∫ ω in tsPastWindow h N ⁻¹' Set.pi Set.univ A, G (tsState 0 ω, tsFwdPath ω)
          ∂tsLaw Q K := by
    intro h N A hA
    have hS : MeasurableSet (tsPastWindow h N ⁻¹' Set.pi Set.univ A) :=
      measurable_tsPastWindow h N (MeasurableSet.univ_pi hA)
    let Lb := gridGaps h (List.ofFn fun k : Fin N => (A k.succ).indicator fun _ => (1 : ℝ))
    have hLb : IsUnitObservables Lb := (isUnitList_ofFn_indicator fun k => hA k.succ).gridGaps
    have hg₀ : Measurable ((A 0).indicator fun _ => (1 : ℝ)) :=
      measurable_const.indicator (hA 0)
    have hg₀b : ∀ ω, |(A 0).indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases h : ω ∈ A 0 <;> simp [h]
    rw [← integral_indicator hS, ← integral_indicator hS]
    have hind : ∀ (F : TwoSidedSpace d → ℝ) ω,
        (tsPastWindow h N ⁻¹' Set.pi Set.univ A).indicator F ω =
          (A 0).indicator (fun _ => (1 : ℝ)) (tsState 0 ω) * tsBwdProd Lb 0 ω * F ω := by
      intro F ω
      rw [← tsPastWindow_box_indicator]
      by_cases hω : ω ∈ tsPastWindow h N ⁻¹' Set.pi Set.univ A <;> simp [hω]
    simp_rw [hind]
    rw [integral_tsLaw_split_fwd hd D Q hap hK hg₀ hg₀b hLb hG'm hG'i,
      integral_tsLaw_split_fwd hd D Q hap hK hg₀ hg₀b hLb hG hGi]
    congr 1
    funext x
    rw [hG'int]
    rfl
  -- equality on past windows
  have hwin : ∀ (h : ℝ≥0) (N : ℕ) {u : Set (TwoSidedSpace d)},
      MeasurableSet[tsPastWindowSigma h N] u →
      ∫ ω in u, G' (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K =
        ∫ ω in u, G (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K := by
    intro h N u hu
    let C : Set (Set (TwoSidedSpace d)) := {s | ∃ B ∈ Set.pi Set.univ '' Set.pi Set.univ
      (fun _ : Fin (N + 1) => {s : Set (FieldPair d) | MeasurableSet s}),
        tsPastWindow h N ⁻¹' B = s}
    have hgen : tsPastWindowSigma (d := d) h N = MeasurableSpace.generateFrom C := by
      rw [tsPastWindowSigma, ← generateFrom_pi, MeasurableSpace.comap_generateFrom]
      rfl
    have hle : tsPastWindowSigma (d := d) h N ≤
        (inferInstance : MeasurableSpace (TwoSidedSpace d)) :=
      (tsPastWindowSigma_le h N).trans tsPastSigma_le
    refine setIntegral_eq_of_generate_integrable hle C (isPiSystem_pi.comap _) hgen hXi hYi
      ?_ ?_ hu
    · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
      exact hbox h N A fun k => hA k (Set.mem_univ k)
    · have h := hbox h N (fun _ => Set.univ) fun _ => MeasurableSet.univ
      simp only [Set.pi_univ, Set.preimage_univ, Measure.restrict_univ] at h
      exact h
  have hset : ∀ s, MeasurableSet[tsPastSigma d] s →
      ∫ ω in s, G' (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K =
        ∫ ω in s, G (tsState 0 ω, tsFwdPath ω) ∂tsLaw Q K := by
    intro s hs
    refine setIntegral_eq_of_generate_integrable tsPastSigma_le (tsPastWindowSets d)
      isPiSystem_tsPastWindowSets tsPastSigma_eq_generateFrom hXi hYi ?_ ?_ hs
    · intro u hu
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hu
      exact hwin _ _ hm
    · have h := hwin (dyadicMesh 1 0) (4 ^ 0) (u := Set.univ) MeasurableSet.univ
      simp only [Measure.restrict_univ] at h
      exact h
  have hXm : Measurable[tsPastSigma d] fun ω : TwoSidedSpace d =>
      G' (tsState 0 ω, tsFwdPath ω) := hΦm.comp (measurable_tsState_past le_rfl)
  exact (ae_eq_condExp_of_forall_setIntegral_eq tsPastSigma_le hYi
    (fun s _ _ => hXi.integrableOn) (fun s hs _ => hset s hs) hXm.aestronglyMeasurable).symm

end Annealed

end EinsteinFull.Blueprint
