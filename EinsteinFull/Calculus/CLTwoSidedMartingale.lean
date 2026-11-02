import EinsteinFull.Calculus.CLTwoSidedDFGWInputs
import EinsteinFull.Calculus.CLUnforcedClockShift

/-!
# The compensated displacement of the two-sided process

The displacement minus the time integral of the drift along the process is a square-integrable
martingale for the past filtration (DFGW (2.40)). It is a functional of the time-zero state and
the forward path, equal to the compensated coordinates of the kernel path, whose kernel means
vanish; an increment over `[s, t]` is the compensated displacement over `[0, t - s]` seen from
time `s`, and the past up to time `s` is the time shift by `s` of the past up to time zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- The sigma-algebra of the states up to time `t`. -/
abbrev tsPastSigmaAt (d : ℕ) (t : ℝ) : MeasurableSpace (TwoSidedSpace d) :=
  ⨆ s ∈ Set.Iic t, MeasurableSpace.comap (tsState s) inferInstance

theorem tsPastSigmaAt_le (t : ℝ) :
    tsPastSigmaAt d t ≤ (inferInstance : MeasurableSpace (TwoSidedSpace d)) :=
  iSup₂_le fun s _ => (measurable_tsState s).comap_le

theorem tsPastSigmaAt_mono {s t : ℝ} (h : s ≤ t) : tsPastSigmaAt d s ≤ tsPastSigmaAt d t :=
  iSup₂_le fun r hr => le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Iic t) =>
    MeasurableSpace.comap (tsState (d := d) r) inferInstance) r (le_trans hr h) le_rfl

theorem measurable_tsState_pastAt {s t : ℝ} (h : s ≤ t) :
    Measurable[tsPastSigmaAt d t] (tsState (d := d) s) :=
  Measurable.of_comap_le (le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Iic t) =>
    MeasurableSpace.comap (tsState (d := d) r) inferInstance) s h le_rfl)

/-- The past filtration of the two-sided process. -/
def tsFiltration (d : ℕ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (TwoSidedSpace d)) where
  seq t := tsPastSigmaAt d t
  mono' _ _ h := tsPastSigmaAt_mono (by exact_mod_cast h)
  le' t := tsPastSigmaAt_le t

/-- The past up to time `s` is the time shift by `s` of the past up to time zero. -/
theorem tsPastSigmaAt_eq_comap (s : ℝ) :
    tsPastSigmaAt d s = (tsPastSigma d).comap (tsShift s) := by
  rw [tsPastSigma]
  simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  apply le_antisymm
  · refine iSup₂_le fun r hr => ?_
    have h : tsState (d := d) r = tsState (r - s) ∘ tsShift s := by
      funext ω
      simp [Function.comp, tsState_shift]
    rw [h]
    exact le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Iic (0 : ℝ)) =>
      MeasurableSpace.comap (tsState (d := d) r ∘ tsShift s) inferInstance) (r - s)
      (by simp only [Set.mem_Iic] at hr ⊢; linarith) le_rfl
  · refine iSup₂_le fun r hr => ?_
    have h : tsState (d := d) r ∘ tsShift s = tsState (r + s) := by
      funext ω
      simp [Function.comp, tsState_shift]
    rw [h]
    exact le_iSup₂_of_le (f := fun r (_ : r ∈ Set.Iic s) =>
      MeasurableSpace.comap (tsState (d := d) r) inferInstance) (r + s)
      (by simp only [Set.mem_Iic] at hr ⊢; linarith) le_rfl

/-- The compensated displacement: displacement minus the time integral of the drift. -/
def tsComp (hd : 2 ≤ d) (t : ℝ) (ω : TwoSidedSpace d) : Vec d :=
  tsDisp 0 t ω - ∫ τ in (0 : ℝ)..t, envDrift hd (tsState τ ω)

/-- The compensated displacement as a functional of an environment and a path. -/
def compFn (hd : 2 ≤ d) (t : ℝ) (z : FieldPair d × Path d) : Vec d :=
  z.2 t.toNNReal - ∫ τ in (0 : ℝ)..t, envDrift hd (translate (z.2 τ.toNNReal) z.1)

theorem tsComp_eq_compFn (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) (ω : TwoSidedSpace d) :
    tsComp hd t ω = compFn hd t (tsState 0 ω, tsFwdPath ω) := by
  simp only [tsComp, compFn]
  congr 1
  · ext j
    simp [tsDisp, tsFwdPath, Real.coe_toNNReal _ ht]
  · refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le ht] at hτ
    simp only [tsState, tsFwdPath, ContinuousMap.coe_mk, Real.coe_toNNReal _ hτ.1]
    rw [translate_add, sub_add_cancel]

theorem measurable_envDrift_translate (hd : 2 ≤ d) :
    Measurable fun p : ℝ × (FieldPair d × Path d) =>
      envDrift hd (translate (p.2.2 p.1.toNNReal) p.2.1) := by
  refine (measurable_envDrift hd).comp (Localization.physicalTranslation_jointlyMeasurable.comp
    (Measurable.prodMk ?_ (measurable_fst.comp measurable_snd)))
  exact (measurable_uncurry_of_continuous_of_measurable
    (u := fun (τ : ℝ) (z : FieldPair d × Path d) => z.2 τ.toNNReal)
    (fun z => z.2.continuous.comp continuous_real_toNNReal)
    fun τ => (continuous_eval_const _).measurable.comp measurable_snd)

theorem measurable_compFn (hd : 2 ≤ d) (t : ℝ) : Measurable (compFn (d := d) hd t) := by
  have h := (measurable_envDrift_translate (d := d) hd).stronglyMeasurable
  refine ((continuous_eval_const _).measurable.comp measurable_snd).sub ?_
  simp only [intervalIntegral]
  exact ((h.integral_prod_left' (μ := volume.restrict (Set.Ioc 0 t))).measurable).sub
    ((h.integral_prod_left' (μ := volume.restrict (Set.Ioc t 0))).measurable)

/-- On a smooth environment, the coordinates of `compFn` along a path from the origin are the
compensated coordinates of the reduced martingale problem. -/
theorem compFn_apply_eq_compensatedTest (hd : 2 ≤ d) {x : FieldPair d} (hs : IsSmoothFieldPair x)
    (t : ℝ≥0) {γ : Path d} (hγ : γ 0 = 0) (j : Fin d) :
    compFn hd t (x, γ) j =
      compensatedTest (reducedGenerator ⟨0, by omega⟩ x 0) (fun y => y j) t γ := by
  have hcov : ∀ y : Vec d, envDrift hd (translate y x) =
      forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y := by
    intro y
    have h := forcedDrift_reduced_translate (⟨0, by omega⟩ : Fin d) 0 y x
    simp only [envDrift, h, add_zero]
  have hLf : ∀ (k : Fin d) (y : Vec d), reducedGenerator ⟨0, by omega⟩ x 0 (fun y => y k) y =
      forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y k := fun k y =>
    response_reducedGenerator_coordinate hs _ k 0 y
  have hbc : Continuous fun y : Vec d => forcedDrift (reducedCoefficient x) ⟨0, by omega⟩ 0 y := by
    refine continuous_pi fun k => ?_
    have h := continuous_reducedGenerator_apply hs (⟨0, by omega⟩ : Fin d) 0 (contDiff_apply ℝ ℝ k)
    exact h.congr fun y => hLf k y
  have hF : Continuous fun τ : ℝ => envDrift hd (translate (γ τ.toNNReal) x) := by
    simp_rw [hcov]
    exact hbc.comp (γ.continuous.comp continuous_real_toNNReal)
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).intervalIntegral_comp_comm
    (hF.intervalIntegrable (μ := volume) 0 (t : ℝ))
  simp only [ContinuousLinearMap.proj_apply] at hcomm
  have e1 : compFn hd t (x, γ) j = γ t j - (∫ τ in (0 : ℝ)..(t : ℝ),
      envDrift hd (translate (γ τ.toNNReal) x)) j := by
    simp only [compFn, Pi.sub_apply, Real.toNNReal_coe]
  rw [e1, ← hcomm]
  simp only [compensatedTest, hγ, Pi.zero_apply, sub_zero]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [hcov, hLf]

private theorem abs_le_sq_add_one' (y : ℝ) : |y| ≤ y ^ 2 + 1 := by
  nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]

private theorem stronglyMeasurable_intervalIntegral_of {Ω E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : MeasurableSpace Ω} {g : ℝ → Ω → E}
    (hg : @StronglyMeasurable (ℝ × Ω) E _ (@Prod.instMeasurableSpace ℝ Ω _ m)
      (Function.uncurry g)) (a b : ℝ) :
    StronglyMeasurable[m] (fun ω => ∫ τ in a..b, g τ ω) := by
  let _ : MeasurableSpace Ω := m
  simp only [intervalIntegral]
  exact (hg.integral_prod_left' (μ := volume.restrict (Set.Ioc a b))).sub
    (hg.integral_prod_left' (μ := volume.restrict (Set.Ioc b a)))

/-- The compensated displacement up to time `t` is determined by the past up to time `t`. -/
theorem stronglyMeasurable_tsComp (hd : 2 ≤ d) (t : ℝ≥0) :
    StronglyMeasurable[tsPastSigmaAt d t] (tsComp (d := d) hd t) := by
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  have hdisp : Measurable[tsPastSigmaAt d t] (tsDisp (d := d) 0 t) := by
    have h : tsDisp (d := d) 0 t = fun ω => displacementInv (tsState 0 ω, tsState t ω) :=
      funext fun ω => tsDisp_eq_displacementInv 0 t ω
    rw [h]
    exact measurable_displacementInv.comp ((measurable_tsState_pastAt t.coe_nonneg).prodMk
      (measurable_tsState_pastAt le_rfl))
  have hjoint : @Measurable (ℝ × TwoSidedSpace d) (FieldPair d)
      (@Prod.instMeasurableSpace ℝ (TwoSidedSpace d) _ (tsPastSigmaAt d t)) _
      (Function.uncurry fun (τ : ℝ) (ω : TwoSidedSpace d) => tsState (min τ t) ω) :=
    measurable_uncurry_of_continuous_of_measurable (m := tsPastSigmaAt d t)
      (u := fun (τ : ℝ) (ω : TwoSidedSpace d) => tsState (min τ t) ω)
      (fun ω => (Probability.continuous_translate.comp
        ((ω.2.continuous.comp (continuous_id.min continuous_const)).prodMk continuous_const)))
      fun τ => measurable_tsState_pastAt (min_le_right _ _)
  have hint : StronglyMeasurable[tsPastSigmaAt d t] fun ω : TwoSidedSpace d =>
      ∫ τ in (0 : ℝ)..t, envDrift hd (tsState (min τ t) ω) :=
    stronglyMeasurable_intervalIntegral_of (g := fun τ ω => envDrift hd (tsState (min τ t) ω))
      ((measurable_envDrift hd).comp hjoint).stronglyMeasurable 0 t
  have hcongr : tsComp (d := d) hd t = fun ω =>
      tsDisp 0 t ω - ∫ τ in (0 : ℝ)..t, envDrift hd (tsState (min τ t) ω) := by
    funext ω
    simp only [tsComp]
    congr 1
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hτ
    simp only [min_eq_left hτ.2]
  rw [hcongr]
  exact hdisp.stronglyMeasurable.sub hint


section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hK in
/-- Moments of the compensated coordinates under the kernel, uniformly in the environment. -/
theorem compFn_kernel_moments :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (j : Fin d), ∀ᵐ x ∂Q.measure,
      Integrable (fun γ => compFn hd t (x, γ) j ^ 2) (K (x, 0)) ∧
      ∫ γ, compFn hd t (x, γ) j ^ 2 ∂K (x, 0) ≤ B * t ∧
      Integrable (fun γ => compFn hd t (x, γ) j) (K (x, 0)) ∧
      ∫ γ, compFn hd t (x, γ) j ∂K (x, 0) = 0 := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hf : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y j) :=
    fun j => contDiff_apply ℝ ℝ j
  have hG0 : ∀ (j : Fin d) (y : Vec d) (k : Fin d),
      |fderiv ℝ (fun y : Vec d => y j) y (unitVector k)| ≤ 1 := by
    intro j y k
    rw [(hasFDerivAt_apply j y).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    by_cases h : j = k <;> simp [unitVector, h]
  have hgrow : ∀ (j : Fin d) (y : Vec d), |(fun y : Vec d => y j) y| ≤ 0 + 1 * ‖y‖ :=
    fun j y => by simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_le_pi_norm y j
  choose B hB0 hB using fun j => lintegral_sq_reduced_le_uniform hΛ (⟨0, by omega⟩ : Fin d) 0
    (hf j) (hG0 j) (hgrow j) le_rfl zero_le_one
  have hBm0 : 0 ≤ ∑ j, B j := Finset.sum_nonneg fun k _ => hB0 k
  refine ⟨∑ j, B j, hBm0, fun t j => ?_⟩
  filter_upwards [Q.regular, hQ] with x hx hsm
  have hP := (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK x hx 0)
  have : IsProbabilityMeasure (K (x, 0)) := hP.1
  let M := compensatedTest (reducedGenerator (⟨0, by omega⟩ : Fin d) x 0) (fun y => y j) t
  have heq : (fun γ => compFn hd t (x, γ) j) =ᵐ[K (x, 0)] M := by
    filter_upwards [hP.2.1] with γ hγ
    exact compFn_apply_eq_compensatedTest hd hsm.1 t hγ j
  obtain ⟨B', _, hB'⟩ := response_coordinate_second_moment hΛ hx hsm.1 _ 0 hP j
  have hMm : MemLp M 2 (K (x, 0)) := (hB' t).1
  have hMi2 : Integrable (fun γ => M γ ^ 2) (K (x, 0)) := hMm.integrable_sq
  have hsq : Integrable (fun γ => compFn hd t (x, γ) j ^ 2) (K (x, 0)) := by
    refine hMi2.congr ?_
    filter_upwards [heq] with γ hγ
    simp only [hγ]
  refine ⟨hsq, ?_, ?_, ?_⟩
  · have e : ∫ γ, compFn hd t (x, γ) j ^ 2 ∂K (x, 0) = ∫ γ, M γ ^ 2 ∂K (x, 0) := by
      refine integral_congr_ae ?_
      filter_upwards [heq] with γ hγ
      simp only [hγ]
    rw [e]
    have h := hB j x hx hsm.1 _ hP t
    rw [← ofReal_integral_eq_lintegral_ofReal hMi2 (ae_of_all _ fun _ => sq_nonneg _)] at h
    exact ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hB0 j) t.coe_nonneg)).1 h).trans
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := B) (fun k _ => hB0 k)
        (Finset.mem_univ j)) t.coe_nonneg)
  · exact (hMm.integrable one_le_two).congr heq.symm
  · rw [integral_congr_ae heq]
    have hmart := reduced_coordinate_martingale hΛ hx hsm.1 _ 0 hP j
    have h := hmart.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    show ∫ γ, compensatedTest (reducedGenerator (⟨0, by omega⟩ : Fin d) x 0) (fun y => y j) t γ
      ∂K (x, 0) = 0
    rw [← h]
    simp [compensatedTest]

include hQ hK in
theorem integrable_compFn_compProd (t : ℝ≥0) (j : Fin d) :
    Integrable (fun z => compFn hd t z j) (Q.measure ⊗ₘ originKernel K) ∧
      Integrable (fun z => compFn hd t z j ^ 2) (Q.measure ⊗ₘ originKernel K) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨B, hB0, hB⟩ := compFn_kernel_moments hd D Q hQ hK
  have hm : Measurable fun z : FieldPair d × Path d => compFn hd t z j :=
    (measurable_pi_iff.1 (measurable_compFn hd t)) j
  constructor
  · rw [Measure.integrable_compProd_iff hm.aestronglyMeasurable]
    refine ⟨(hB t j).mono fun x hx => hx.2.2.1, Integrable.of_bound (C := B * t + 1)
      (hm.norm.stronglyMeasurable.integral_kernel_prod_right' (κ := originKernel K)).aestronglyMeasurable
      ?_⟩
    filter_upwards [hB t j] with x ⟨hsq, hle, hint, _⟩
    have : IsProbabilityMeasure (K (x, 0)) := inferInstance
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change ∫ γ, ‖compFn hd t (x, γ) j‖ ∂K (x, 0) ≤ B * t + 1
    calc ∫ γ, ‖compFn hd t (x, γ) j‖ ∂K (x, 0) ≤
          ∫ γ, (compFn hd t (x, γ) j ^ 2 + 1) ∂K (x, 0) :=
          integral_mono hint.norm (hsq.add (integrable_const 1)) fun γ => by
            rw [Real.norm_eq_abs]
            exact abs_le_sq_add_one' _
      _ = ∫ γ, compFn hd t (x, γ) j ^ 2 ∂K (x, 0) + 1 := by
          rw [integral_add hsq (integrable_const 1), integral_const, probReal_univ, one_smul]
      _ ≤ B * t + 1 := by linarith
  · rw [Measure.integrable_compProd_iff (hm.pow_const 2).aestronglyMeasurable]
    refine ⟨(hB t j).mono fun x hx => hx.1, Integrable.of_bound (C := B * t)
      ((hm.pow_const 2).norm.stronglyMeasurable.integral_kernel_prod_right'
        (κ := originKernel K)).aestronglyMeasurable ?_⟩
    filter_upwards [hB t j] with x ⟨hsq, hle, _, _⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ γ, ‖compFn hd t (x, γ) j ^ 2‖ ∂originKernel K x =
          ∫ γ, compFn hd t (x, γ) j ^ 2 ∂K (x, 0) := by
          refine integral_congr_ae (ae_of_all _ fun γ => ?_)
          simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      _ ≤ B * t := hle

include hQ hap hK in
/-- DFGW (2.40), first part: the compensated displacement is square integrable. -/
theorem memLp_tsComp (t : ℝ≥0) : MemLp (tsComp hd t) 2 (tsLaw Q K) := by
  refine memLp_pi_iff.2 fun j => ?_
  have hfun : (fun ω => tsComp hd t ω j) =
      fun ω => (fun z => compFn hd t z j) (tsState 0 ω, tsFwdPath ω) := by
    funext ω
    rw [tsComp_eq_compFn hd t.coe_nonneg]
  rw [hfun]
  have hm : Measurable fun z : FieldPair d × Path d => compFn hd t z j :=
    (measurable_pi_iff.1 (measurable_compFn hd t)) j
  have hmΩ : Measurable fun ω : TwoSidedSpace d =>
      (fun z => compFn hd t z j) (tsState 0 ω, tsFwdPath ω) :=
    hm.comp ((measurable_tsState 0).prodMk measurable_tsFwdPath)
  refine (memLp_two_iff_integrable_sq hmΩ.aestronglyMeasurable).2 ?_
  have h := integrable_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
    (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim)
    (G := fun z => compFn hd t z j ^ 2) (hm.pow_const 2)
    (integrable_compFn_compProd hd D Q hQ hK t j).2
  simpa only [tsBwdProd, one_mul] using h

include hQ hap hK in
/-- The compensated displacement has zero integral over every past event. -/
theorem setIntegral_tsComp_past (u : ℝ≥0) {A : Set (TwoSidedSpace d)}
    (hA : MeasurableSet[tsPastSigma d] A) : ∫ ω in A, tsComp hd u ω ∂tsLaw Q K = 0 := by
  have := tsLaw_isProbability Q hap K
  obtain ⟨B, hB0, hB⟩ := compFn_kernel_moments hd D Q hQ hK
  have hmem := memLp_tsComp hd D Q hQ hap hK u
  have hcomp : ∀ j, Integrable (fun ω => tsComp hd u ω j) ((tsLaw Q K).restrict A) := fun j =>
    ((memLp_pi_iff.1 hmem j).integrable one_le_two).restrict
  funext j
  rw [Pi.zero_apply, eval_integral hcomp j]
  have hm : Measurable fun z : FieldPair d × Path d => compFn hd u z j :=
    (measurable_pi_iff.1 (measurable_compFn hd u)) j
  have hfun : (fun ω => tsComp hd u ω j) =
      fun ω => (fun z => compFn hd u z j) (tsState 0 ω, tsFwdPath ω) := by
    funext ω
    rw [tsComp_eq_compFn hd u.coe_nonneg]
  rw [hfun]
  have hYi : Integrable (fun ω => (fun z => compFn hd u z j) (tsState 0 ω, tsFwdPath ω))
      (tsLaw Q K) := by
    rw [← hfun]
    exact (memLp_pi_iff.1 hmem j).integrable one_le_two
  rw [← setIntegral_condExp tsPastSigma_le hYi hA]
  have hce := tsLaw_condExp_fwd hd D Q hap hK hm (integrable_compFn_compProd hd D Q hQ hK u j).1
  have hzero : ∀ᵐ ω ∂tsLaw Q K, ∫ γ, compFn hd u (tsState 0 ω, γ) j ∂K (tsState 0 ω, 0) = 0 := by
    have h := (hB u j).mono fun x hx => hx.2.2.2
    rw [← tsLaw_map_tsState_zero D Q hap (K := K)] at h
    exact ae_of_ae_map (measurable_tsState 0).aemeasurable h
  rw [setIntegral_congr_ae (tsPastSigma_le _ hA) (by
    filter_upwards [hce, hzero] with ω h1 h2 _
    rw [h1, h2])]
  simp

include hap in
/-- Along almost every path the drift is bounded, so the compensated displacement over `[s, t]`
is the compensated displacement over `[0, t - s]` seen from time `s`. -/
theorem tsComp_sub_ae (s t : ℝ) :
    ∀ᵐ ω ∂tsLaw Q K, tsComp hd t ω - tsComp hd s ω = tsComp hd (t - s) (tsShift s ω) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hreg : ∀ᵐ ω ∂tsLaw Q K, IsRegular D.ellipticity (tsState 0 ω) := by
    have h := Q.regular
    rw [← tsLaw_map_tsState_zero D Q hap (K := K)] at h
    exact ae_of_ae_map (measurable_tsState 0).aemeasurable h
  filter_upwards [hreg] with ω hω
  have hregτ : ∀ τ, IsRegular D.ellipticity (tsState τ ω) := by
    intro τ
    have e : tsState τ ω = translate (ω.2 τ - ω.2 0) (tsState 0 ω) := by
      simp only [tsState]
      rw [translate_add, sub_add_cancel]
    rw [e]
    exact (ActualImageLpStateTransport.isRegular_translate_iff _ _).2 hω
  let f : ℝ → Vec d := fun τ => envDrift hd (tsState τ ω)
  have hfc : Measurable f := (measurable_envDrift hd).comp
    (Probability.continuous_translate.comp (ω.2.continuous.prodMk continuous_const)).measurable
  have hfb : ∀ τ, ‖f τ‖ ≤ driftBound d D.ellipticity := fun τ =>
    (pi_norm_le_iff_of_nonneg (driftBound_nonneg _)).2 fun j => by
      rw [Real.norm_eq_abs]
      exact abs_reducedDrift_le hΛ (hregτ τ) _ 0 j
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => by
    refine ⟨?_, ?_⟩ <;>
    exact Integrable.of_bound hfc.aestronglyMeasurable (driftBound d D.ellipticity)
      (ae_of_all _ hfb)
  have hint : (∫ τ in (0 : ℝ)..t, f τ) - ∫ τ in (0 : ℝ)..s, f τ =
      ∫ τ in (0 : ℝ)..(t - s), envDrift hd (tsState τ (tsShift s ω)) := by
    rw [intervalIntegral.integral_interval_sub_left (hii 0 t) (hii 0 s)]
    have h := intervalIntegral.integral_comp_add_right f s (a := 0) (b := t - s)
    rw [zero_add, sub_add_cancel] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [f, tsState_shift]
  simp only [tsComp]
  rw [show tsDisp 0 (t - s) (tsShift s ω) = tsDisp 0 t ω - tsDisp 0 s ω by
    rw [tsDisp_shift, zero_add, sub_add_cancel, ← tsDisp_add 0 s t, add_sub_cancel_left]]
  rw [← hint]
  abel

include hQ hunforced hpath hap hK in
/-- DFGW (2.40): the compensated displacement is a martingale for the past filtration. -/
theorem tsComp_martingale :
    Martingale (fun (t : ℝ≥0) => tsComp (d := d) hd t) (tsFiltration d) (tsLaw Q K) := by
  have := tsLaw_isProbability Q hap K
  refine ⟨fun t => stronglyMeasurable_tsComp hd t, fun s t hst => ?_⟩
  have hint : ∀ u : ℝ≥0, Integrable (tsComp (d := d) hd u) (tsLaw Q K) := fun u =>
    (memLp_tsComp hd D Q hQ hap hK u).integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((tsFiltration d).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (stronglyMeasurable_tsComp hd s).aestronglyMeasurable).symm
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  -- the past up to `s` is the shift of the past up to zero
  have hA' : MeasurableSet[(tsPastSigma d).comap (tsShift s)] A := by
    rw [← tsPastSigmaAt_eq_comap]
    exact hA
  obtain ⟨A', hA'm, rfl⟩ := hA'
  have hAm : MeasurableSet (tsShift (d := d) s ⁻¹' A') :=
    measurable_tsShift s (tsPastSigma_le _ hA'm)
  have hdiff : ∫ ω in tsShift s ⁻¹' A', (tsComp hd t ω - tsComp hd s ω) ∂tsLaw Q K = 0 := by
    rw [setIntegral_congr_ae hAm ((tsComp_sub_ae hd D Q hap (K := K) s t).mono
      fun ω h _ => h)]
    have hmap := setIntegral_map (μ := tsLaw Q K) (g := tsShift s) (s := A')
      (f := tsComp hd ((t : ℝ) - s)) (tsPastSigma_le _ hA'm)
      (by rw [tsLaw_map_tsShift hd D Q hQ hunforced hpath hap hK s]
          have h := (memLp_tsComp hd D Q hQ hap hK (t - s)).aestronglyMeasurable
          rwa [NNReal.coe_sub hst] at h)
      (measurable_tsShift s).aemeasurable
    rw [tsLaw_map_tsShift hd D Q hQ hunforced hpath hap hK s] at hmap
    rw [← hmap]
    have h := setIntegral_tsComp_past hd D Q hQ hap hK (t - s) hA'm
    rwa [NNReal.coe_sub hst] at h
  rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at hdiff
  exact (sub_eq_zero.1 hdiff).symm

end Annealed

end EinsteinFull.Blueprint
