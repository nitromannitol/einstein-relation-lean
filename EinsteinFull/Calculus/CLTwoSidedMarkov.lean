import EinsteinFull.Calculus.CLTwoSidedStationary

/-!
# The Markov property of the two-sided environment process

Given the states up to time zero, the state at time `t ≥ 0` has the law of the environment kernel
at time `t` from the state at time zero. On a past box event the claim is the split formula with a
single forward step; the past grid windows generate the past sigma-algebra, and equal set
integrals on a generating pi-system extend to the generated sigma-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem measurable_envMap (t : ℝ≥0) :
    Measurable fun p : FieldPair d × Path d => translate (p.2 t) p.1 :=
  (Probability.continuous_translate.comp
    (((continuous_eval_const t).comp continuous_snd).prodMk continuous_fst)).measurable

/-- The environment kernel at time `t`: the law of the environment seen from the particle. -/
def envKernel (K : Kernel (FieldPair d × Vec d) (Path d)) (t : ℝ≥0) :
    Kernel (FieldPair d) (FieldPair d) :=
  (Kernel.deterministic id measurable_id ×ₖ
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)).map
      fun p : FieldPair d × Path d => translate (p.2 t) p.1

instance (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0) :
    IsMarkovKernel (envKernel K t) := by
  unfold envKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_envMap t)

theorem integral_envKernel (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K]
    (t : ℝ≥0) {f : FieldPair d → ℝ} (hf : Measurable f) (ω : FieldPair d) :
    ∫ y, f y ∂envKernel K t ω = kernelPhysMean K f t ω := by
  rw [envKernel, Kernel.map_apply _ (measurable_envMap t),
    integral_map (measurable_envMap t).aemeasurable hf.aestronglyMeasurable,
    Kernel.prod_apply, Kernel.deterministic_apply, Measure.dirac_prod,
    integral_map measurable_prodMk_left.aemeasurable]
  · rfl
  · exact (hf.comp (measurable_envMap t)).aestronglyMeasurable

/-- Equal integrals of bounded observables over the sets of a generating pi-system, and over the
whole space, give equal integrals over every set of the generated sigma-algebra. -/
theorem setIntegral_eq_of_generate {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] (hm : m ≤ m₀) (C : Set (Set α))
    (hC : IsPiSystem C) (hgen : m = MeasurableSpace.generateFrom C)
    {X Y : α → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXb : ∀ ω, |X ω| ≤ 1)
    (hYb : ∀ ω, |Y ω| ≤ 1)
    (hCeq : ∀ s ∈ C, ∫ ω in s, X ω ∂μ = ∫ ω in s, Y ω ∂μ)
    (huniv : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂μ) {s : Set α} (hs : MeasurableSet[m] s) :
    ∫ ω in s, X ω ∂μ = ∫ ω in s, Y ω ∂μ := by
  have hCm : ∀ s ∈ C, MeasurableSet s := fun s hsC => hm _ (hgen ▸
    MeasurableSpace.measurableSet_generateFrom hsC)
  have hXi : Integrable X μ := Integrable.of_bound hX.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hXb ω)
  have hYi : Integrable Y μ := Integrable.of_bound hY.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hYb ω)
  have hX1 : ∀ ω, 0 ≤ X ω + 1 := fun ω => by linarith [(abs_le.1 (hXb ω)).1]
  have hY1 : ∀ ω, 0 ≤ Y ω + 1 := fun ω => by linarith [(abs_le.1 (hYb ω)).1]
  let νX := μ.withDensity fun ω => ENNReal.ofReal (X ω + 1)
  let νY := μ.withDensity fun ω => ENNReal.ofReal (Y ω + 1)
  have hν : ∀ (Z : α → ℝ), Measurable Z → Integrable Z μ → (∀ ω, 0 ≤ Z ω + 1) →
      ∀ t, MeasurableSet t → μ.withDensity (fun ω => ENNReal.ofReal (Z ω + 1)) t =
        ENNReal.ofReal (∫ ω in t, Z ω ∂μ + μ.real t) := by
    intro Z hZ hZi hZ1 t ht
    have hint : Integrable (fun ω => Z ω + 1) (μ.restrict t) :=
      (hZi.add (integrable_const 1)).restrict
    rw [withDensity_apply _ ht, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hZ1)]
    congr 1
    rw [integral_add hZi.restrict (integrable_const 1), setIntegral_const, smul_eq_mul, mul_one]
  have : IsFiniteMeasure νX := isFiniteMeasure_withDensity_ofReal (hXi.add (integrable_const 1)).2
  have heq : νX s = νY s := by
    refine ext_on_measurableSpace_of_generate_finite m₀ C (fun t htC => ?_) hm hgen hC ?_ hs
    · rw [hν X hX hXi hX1 t (hCm t htC), hν Y hY hYi hY1 t (hCm t htC), hCeq t htC]
    · rw [hν X hX hXi hX1 _ MeasurableSet.univ, hν Y hY hYi hY1 _ MeasurableSet.univ,
        setIntegral_univ, setIntegral_univ, huniv]
  have hsm : MeasurableSet s := hm _ hs
  rw [hν X hX hXi hX1 s hsm, hν Y hY hYi hY1 s hsm] at heq
  have h1 : 0 ≤ ∫ ω in s, X ω ∂μ + μ.real s := by
    have e : ∫ ω in s, X ω ∂μ + μ.real s = ∫ ω in s, (X ω + 1) ∂μ := by
      rw [integral_add hXi.restrict (integrable_const 1), setIntegral_const, smul_eq_mul,
        mul_one]
    rw [e]
    exact setIntegral_nonneg hsm fun ω _ => hX1 ω
  have h2 : 0 ≤ ∫ ω in s, Y ω ∂μ + μ.real s := by
    have e : ∫ ω in s, Y ω ∂μ + μ.real s = ∫ ω in s, (Y ω + 1) ∂μ := by
      rw [integral_add hYi.restrict (integrable_const 1), setIntegral_const, smul_eq_mul,
        mul_one]
    rw [e]
    exact setIntegral_nonneg hsm fun ω _ => hY1 ω
  have := (ENNReal.ofReal_eq_ofReal_iff h1 h2).1 heq
  linarith

open Classical in
theorem tsBwdProd_ofFn_indicator (h : ℝ≥0) :
    ∀ (n : ℕ) (A : Fin n → Set (FieldPair d)) (t : ℝ) (ω : TwoSidedSpace d),
      tsBwdProd (gridGaps h (List.ofFn fun k => (A k).indicator fun _ => (1 : ℝ))) t ω =
        if ∀ k : Fin n, tsState (t - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k then 1 else 0
  | 0, A, t, ω => by simp [gridGaps, tsBwdProd]
  | n + 1, A, t, ω => by
    rw [List.ofFn_succ]
    simp only [gridGaps, List.map_cons, tsBwdProd]
    have hrec := tsBwdProd_ofFn_indicator h n (fun k => A k.succ) (t - h) ω
    simp only [gridGaps] at hrec
    rw [hrec]
    have hiff : (∀ k : Fin (n + 1), tsState (t - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k) ↔
        tsState (t - h) ω ∈ A 0 ∧
          ∀ k : Fin n, tsState (t - h - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k.succ := by
      rw [Fin.forall_fin_succ]
      have he : ∀ k : Fin n, t - ((((k.succ : Fin (n + 1)) : ℕ) : ℝ) + 1) * h =
          t - h - (((k : ℕ) : ℝ) + 1) * h := by
        intro k
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring
      simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul, he]
    by_cases h0 : tsState (t - h) ω ∈ A 0 <;>
      by_cases h1 : ∀ k : Fin n, tsState (t - h - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k.succ <;>
      simp [hiff, h0, h1]

/-- The sigma-algebra of the states up to time zero. -/
abbrev tsPastSigma (d : ℕ) : MeasurableSpace (TwoSidedSpace d) :=
  ⨆ s ∈ Set.Iic (0 : ℝ), MeasurableSpace.comap (tsState s) inferInstance

theorem tsPastSigma_le :
    tsPastSigma d ≤ (inferInstance : MeasurableSpace (TwoSidedSpace d)) :=
  iSup₂_le fun s _ => (measurable_tsState s).comap_le

theorem measurable_tsState_past {s : ℝ} (hs : s ≤ 0) :
    Measurable[tsPastSigma d] (tsState (d := d) s) :=
  Measurable.of_comap_le (le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Iic (0 : ℝ)) =>
    MeasurableSpace.comap (tsState (d := d) s) inferInstance) s hs le_rfl)

/-- The states at the past grid times `-k h`, `k ≤ N`. -/
def tsPastWindow (h : ℝ≥0) (N : ℕ) (ω : TwoSidedSpace d) : Fin (N + 1) → FieldPair d :=
  fun k => tsState (-((k : ℕ) : ℝ) * h) ω

theorem measurable_tsPastWindow (h : ℝ≥0) (N : ℕ) : Measurable (tsPastWindow (d := d) h N) :=
  measurable_pi_iff.mpr fun _ => measurable_tsState _

/-- The sigma-algebra of a past window. -/
abbrev tsPastWindowSigma (h : ℝ≥0) (N : ℕ) : MeasurableSpace (TwoSidedSpace d) :=
  MeasurableSpace.comap (tsPastWindow h N) MeasurableSpace.pi

theorem tsPastWindowSigma_eq (h : ℝ≥0) (N : ℕ) :
    tsPastWindowSigma (d := d) h N =
      ⨆ k : Fin (N + 1), MeasurableSpace.comap
        (tsState (-((k : ℕ) : ℝ) * h)) inferInstance := by
  rw [tsPastWindowSigma, MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  congr 1
  funext k
  rw [MeasurableSpace.comap_comp]
  rfl

theorem tsPastWindowSigma_le (h : ℝ≥0) (N : ℕ) :
    tsPastWindowSigma (d := d) h N ≤ tsPastSigma d := by
  rw [tsPastWindowSigma_eq]
  refine iSup_le fun k => ?_
  have hk : -((k : ℕ) : ℝ) * h ≤ 0 := by
    have : (0 : ℝ) ≤ ((k : ℕ) : ℝ) * h := by positivity
    linarith
  exact le_iSup₂_of_le (f := fun s (_ : s ∈ Set.Iic (0 : ℝ)) =>
    MeasurableSpace.comap (tsState (d := d) s) inferInstance) _ hk le_rfl

theorem tsPastWindowSigma_mono (m : ℕ) :
    tsPastWindowSigma (d := d) (dyadicMesh 1 m) (4 ^ m) ≤
      tsPastWindowSigma (dyadicMesh 1 (m + 1)) (4 ^ (m + 1)) := by
  rw [tsPastWindowSigma_eq, tsPastWindowSigma_eq]
  refine iSup_le fun k => ?_
  have hk := k.2
  let j : Fin (4 ^ (m + 1) + 1) := ⟨2 * k, by rw [pow_succ]; omega⟩
  have ht : -((k : ℕ) : ℝ) * (dyadicMesh 1 m : ℝ) =
      -((j : ℕ) : ℝ) * (dyadicMesh 1 (m + 1) : ℝ) := by
    simp only [j, dyadicMesh, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
    push_cast
    field_simp
    ring
  rw [ht]
  exact le_iSup (fun j : Fin (4 ^ (m + 1) + 1) => MeasurableSpace.comap
    (tsState (-((j : ℕ) : ℝ) * (dyadicMesh 1 (m + 1) : ℝ))) inferInstance) j

/-- The past window sets. -/
def tsPastWindowSets (d : ℕ) : Set (Set (TwoSidedSpace d)) :=
  ⋃ m : ℕ, {s | MeasurableSet[tsPastWindowSigma (dyadicMesh 1 m) (4 ^ m)] s}

theorem isPiSystem_tsPastWindowSets : IsPiSystem (tsPastWindowSets d) := by
  refine isPiSystem_iUnion_of_directed_le _ (fun m => @MeasurableSpace.isPiSystem_measurableSet _
    (tsPastWindowSigma (dyadicMesh 1 m) (4 ^ m))) ?_
  refine Monotone.directed_le (monotone_nat_of_le_succ fun m => ?_)
  exact fun s hs => tsPastWindowSigma_mono m s hs

private theorem measurable_of_tendsto_of' {α β : Type*} {m : MeasurableSpace α}
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : ℕ → α → β} {g : α → β} (hf : ∀ i, Measurable[m] (f i))
    (lim : ∀ x, Tendsto (fun i => f i x) atTop (𝓝 (g x))) : Measurable[m] g := by
  let _ : MeasurableSpace α := m
  exact measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 lim)

theorem measurable_tsState_pastGenerate {s : ℝ} (hs : s ≤ 0) :
    Measurable[MeasurableSpace.generateFrom (tsPastWindowSets d)] (tsState (d := d) s) := by
  let G := MeasurableSpace.generateFrom (tsPastWindowSets d)
  have hwin : ∀ (m : ℕ) (k : Fin (4 ^ m + 1)),
      Measurable[G] (tsState (d := d) (-((k : ℕ) : ℝ) * (dyadicMesh 1 m : ℝ))) := by
    intro m k
    have hle : tsPastWindowSigma (d := d) (dyadicMesh 1 m) (4 ^ m) ≤ G := fun s hs =>
      MeasurableSpace.measurableSet_generateFrom (Set.mem_iUnion.2 ⟨m, hs⟩)
    refine Measurable.of_comap_le (le_trans ?_ hle)
    rw [tsPastWindowSigma_eq]
    exact le_iSup (fun k : Fin (4 ^ m + 1) => MeasurableSpace.comap
      (tsState (-((k : ℕ) : ℝ) * (dyadicMesh 1 m : ℝ))) inferInstance) k
  obtain ⟨M₀, hM₀⟩ := pow_unbounded_of_one_lt (|s| + 1) (by norm_num : (1 : ℝ) < 2)
  let hm : ℕ → ℝ := fun n => (dyadicMesh 1 (n + M₀) : ℝ)
  have hhm : ∀ n, hm n = 1 / 2 ^ (n + M₀) := fun n => by
    simp only [hm, dyadicMesh, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
  have hmpos : ∀ n, 0 < hm n := fun n => by rw [hhm]; positivity
  let k : ℕ → ℤ := fun n => ⌊s * 2 ^ (n + M₀)⌋
  have hk : ∀ n, -((4 ^ (n + M₀) : ℕ) : ℤ) ≤ k n ∧ k n ≤ 0 := by
    intro n
    have h2 : (2 : ℝ) ^ M₀ ≤ 2 ^ (n + M₀) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hfl : (k n : ℝ) ≤ s * 2 ^ (n + M₀) := Int.floor_le _
    have hlt : s * 2 ^ (n + M₀) < (k n : ℝ) + 1 := Int.lt_floor_add_one _
    have h4 : ((4 ^ (n + M₀) : ℕ) : ℝ) = 2 ^ (n + M₀) * 2 ^ (n + M₀) := by
      push_cast
      rw [← mul_pow]
      norm_num
    have hpos : (0 : ℝ) < 2 ^ (n + M₀) := by positivity
    have hs1 : |s| ≤ 2 ^ (n + M₀) - 1 := by linarith
    have hsl : -((2 ^ (n + M₀) - 1) * 2 ^ (n + M₀)) ≤ s * 2 ^ (n + M₀) := by
      nlinarith [neg_abs_le s]
    constructor
    · have : (-((4 ^ (n + M₀) : ℕ) : ℝ)) < (k n : ℝ) + 1 := by
        rw [h4]
        nlinarith
      have : -((4 ^ (n + M₀) : ℕ) : ℤ) < k n + 1 := by exact_mod_cast this
      omega
    · have : (k n : ℝ) ≤ 0 := by nlinarith
      exact_mod_cast this
  let f : ℕ → TwoSidedSpace d → FieldPair d := fun n => tsState ((k n : ℝ) * hm n)
  have hf : ∀ n, Measurable[G] (f n) := by
    intro n
    let i : Fin (4 ^ (n + M₀) + 1) := ⟨(-k n).toNat, by have := hk n; omega⟩
    have hti : (k n : ℝ) * hm n = -((i : ℕ) : ℝ) * (dyadicMesh 1 (n + M₀) : ℝ) := by
      have hnn : ((i : ℕ) : ℤ) = -k n := by
        simp only [i]
        have := hk n
        rw [Int.toNat_of_nonneg (by omega)]
      have : ((i : ℕ) : ℝ) = -(k n : ℝ) := by exact_mod_cast hnn
      rw [this]
      ring
    show Measurable[G] (tsState ((k n : ℝ) * hm n))
    rw [hti]
    exact hwin _ i
  let : PolishSpace (FieldPair d) := fieldPair_polish d
  refine measurable_of_tendsto_of' hf fun ω => ?_
  have hcont : Continuous fun r : ℝ => tsState r ω :=
    Probability.continuous_translate.comp (ω.2.continuous.prodMk continuous_const)
  refine (hcont.tendsto s).comp ?_
  have hhm0 : Tendsto hm atTop (𝓝 0) := by
    have : hm = fun n => (1 : ℝ) / 2 ^ (n + M₀) := funext hhm
    rw [this]
    have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat M₀)
    exact tendsto_const_nhds.div_atTop h
  have hle : ∀ n, |(k n : ℝ) * hm n - s| ≤ hm n := by
    intro n
    have hfl : (k n : ℝ) ≤ s * 2 ^ (n + M₀) := Int.floor_le _
    have hlt : s * 2 ^ (n + M₀) < (k n : ℝ) + 1 := Int.lt_floor_add_one _
    have hpos : (0 : ℝ) < 2 ^ (n + M₀) := by positivity
    rw [hhm, abs_le]
    constructor
    · rw [show (k n : ℝ) * (1 / 2 ^ (n + M₀)) - s = ((k n : ℝ) - s * 2 ^ (n + M₀)) / 2 ^ (n + M₀)
        by field_simp]
      rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right hpos]
      linarith
    · rw [show (k n : ℝ) * (1 / 2 ^ (n + M₀)) - s = ((k n : ℝ) - s * 2 ^ (n + M₀)) / 2 ^ (n + M₀)
        by field_simp]
      rw [div_le_div_iff_of_pos_right hpos]
      linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]
    exact hle n) hhm0

theorem tsPastSigma_eq_generateFrom :
    tsPastSigma d = MeasurableSpace.generateFrom (tsPastWindowSets d) := by
  apply le_antisymm
  · exact iSup₂_le fun s hs => (measurable_tsState_pastGenerate hs).comap_le
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hs
    exact tsPastWindowSigma_le _ _ s hm


section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

private theorem setIntegral_eq_integral_indicator_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} (hS : MeasurableSet S) (F : α → ℝ) :
    ∫ ω in S, F ω ∂μ = ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω * F ω ∂μ := by
  rw [← integral_indicator hS]
  congr 1
  funext ω
  by_cases h : ω ∈ S <;> simp [h]

open Classical in
include hap hK in
/-- The Markov property on a past box event. -/
theorem setIntegral_past_box (t : ℝ≥0) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (h : ℝ≥0) (N : ℕ) {A : Fin (N + 1) → Set (FieldPair d)}
    (hA : ∀ k, MeasurableSet (A k)) :
    ∫ ω in tsPastWindow h N ⁻¹' Set.pi Set.univ A, kernelPhysMean K f t (tsState 0 ω)
        ∂tsLaw Q K =
      ∫ ω in tsPastWindow h N ⁻¹' Set.pi Set.univ A, f (tsState t ω) ∂tsLaw Q K := by
  set S := tsPastWindow h N ⁻¹' Set.pi Set.univ A with hSdef
  have hS : MeasurableSet S := measurable_tsPastWindow h N (MeasurableSet.univ_pi hA)
  let Lb := gridGaps h (List.ofFn fun k : Fin N => (A k.succ).indicator fun _ => (1 : ℝ))
  have hLb : IsUnitObservables Lb := (isUnitList_ofFn_indicator fun k => hA k.succ).gridGaps
  let g₀ : FieldPair d → ℝ := (A 0).indicator fun _ => 1
  have hg₀ : Measurable g₀ := measurable_const.indicator (hA 0)
  have hg₀b : ∀ ω, |g₀ ω| ≤ 1 := fun ω => by by_cases h : ω ∈ A 0 <;> simp [g₀, h]
  have hTm : Measurable (kernelPhysMean K f t) := measurable_kernelPhysMean K hf t
  have hTb : ∀ ω, |kernelPhysMean K f t ω| ≤ 1 := abs_kernelPhysMean_le K hfb t
  have hiff : ∀ ω, ω ∈ S ↔ (tsState 0 ω ∈ A 0 ∧
      ∀ k : Fin N, tsState (0 - (((k : ℕ) : ℝ) + 1) * h) ω ∈ A k.succ) := by
    intro ω
    have he : ∀ k : Fin N, -((((k.succ : Fin (N + 1)) : ℕ) : ℝ)) * (h : ℝ) =
        0 - (((k : ℕ) : ℝ) + 1) * h := by
      intro k
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
    simp only [hSdef, Set.mem_preimage, Set.mem_univ_pi, tsPastWindow]
    rw [Fin.forall_fin_succ]
    simp only [Fin.val_zero, Nat.cast_zero, neg_zero, zero_mul, he]
  have hind : ∀ ω, S.indicator (fun _ => (1 : ℝ)) ω = g₀ (tsState 0 ω) * tsBwdProd Lb 0 ω := by
    intro ω
    rw [tsBwdProd_ofFn_indicator]
    simp only [Set.indicator_apply, g₀]
    by_cases h0 : tsState 0 ω ∈ A 0 <;> simp [hiff, h0]
  have hLf : IsUnitObservables [(t, f)] := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨hf, hfb⟩
  rw [setIntegral_eq_integral_indicator_mul hS, setIntegral_eq_integral_indicator_mul hS]
  simp_rw [hind]
  have hTg : ∀ x, |g₀ x * kernelPhysMean K f t x| ≤ 1 := fun x => by
    rw [abs_mul]
    exact (mul_le_mul (hg₀b x) (hTb x) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hs1 := integral_tsLaw_split hd D Q hap hK
    (F₀ := fun x => g₀ x * kernelPhysMean K f t x) (hg₀.mul hTm) hTg hLb
    (Lf := []) (fun _ h => (List.not_mem_nil h).elim)
  have hs2 := integral_tsLaw_split hd D Q hap hK hg₀ hg₀b hLb hLf
  beta_reduce at hs1
  calc ∫ ω, g₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * kernelPhysMean K f t (tsState 0 ω) ∂tsLaw Q K
      = ∫ ω, g₀ (tsState 0 ω) * kernelPhysMean K f t (tsState 0 ω) * tsBwdProd Lb 0 ω *
          tsFwdProd [] 0 ω ∂tsLaw Q K := by
        congr 1
        funext ω
        simp only [tsFwdProd]
        ring
    _ = ∫ ω, g₀ ω * kernelPhysMean K f t ω * chainMean K Lb ω * chainMean K [] ω ∂Q.measure :=
        hs1
    _ = ∫ ω, g₀ ω * chainMean K Lb ω * chainMean K [(t, f)] ω ∂Q.measure := by
        congr 1
        funext ω
        have e : kernelPhysMean K (fun ω => f ω * chainMean K [] ω) t = kernelPhysMean K f t := by
          funext x
          simp only [chainMean, mul_one]
        simp only [chainMean] at e ⊢
        rw [e]
        ring
    _ = ∫ ω, g₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * tsFwdProd [(t, f)] 0 ω ∂tsLaw Q K :=
        hs2.symm
    _ = ∫ ω, g₀ (tsState 0 ω) * tsBwdProd Lb 0 ω * f (tsState t ω) ∂tsLaw Q K := by
        congr 1
        funext ω
        simp only [tsFwdProd, zero_add, mul_one]

include hap hK in
/-- The Markov property on a past window event. -/
theorem setIntegral_past_window (t : ℝ≥0) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (h : ℝ≥0) (N : ℕ) {u : Set (TwoSidedSpace d)}
    (hu : MeasurableSet[tsPastWindowSigma h N] u) :
    ∫ ω in u, kernelPhysMean K f t (tsState 0 ω) ∂tsLaw Q K =
      ∫ ω in u, f (tsState t ω) ∂tsLaw Q K := by
  have := tsLaw_isProbability Q hap K
  have hTm : Measurable (kernelPhysMean K f t) := measurable_kernelPhysMean K hf t
  have hTb : ∀ ω, |kernelPhysMean K f t ω| ≤ 1 := abs_kernelPhysMean_le K hfb t
  let C : Set (Set (TwoSidedSpace d)) := {s | ∃ B ∈ Set.pi Set.univ '' Set.pi Set.univ
    (fun _ : Fin (N + 1) => {s : Set (FieldPair d) | MeasurableSet s}), tsPastWindow h N ⁻¹' B = s}
  have hgen : tsPastWindowSigma (d := d) h N = MeasurableSpace.generateFrom C := by
    rw [tsPastWindowSigma, ← generateFrom_pi, MeasurableSpace.comap_generateFrom]
    rfl
  have hle : tsPastWindowSigma (d := d) h N ≤ (inferInstance : MeasurableSpace (TwoSidedSpace d)) :=
    (tsPastWindowSigma_le h N).trans tsPastSigma_le
  refine setIntegral_eq_of_generate hle C (isPiSystem_pi.comap _) hgen
    (hTm.comp (measurable_tsState 0)) (hf.comp (measurable_tsState t)) (fun ω => hTb _)
    (fun ω => hfb _) ?_ ?_ hu
  · rintro _ ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    exact setIntegral_past_box hd D Q hap hK t hf hfb h N fun k => hA k (Set.mem_univ k)
  · have h := setIntegral_past_box hd D Q hap hK t hf hfb h N (A := fun _ => Set.univ)
      fun _ => MeasurableSet.univ
    simp only [Set.pi_univ, Set.preimage_univ, Measure.restrict_univ] at h
    exact h

include hap hK in
/-- The Markov property of the two-sided process at time zero (DFGW (2.1)). -/
theorem tsLaw_condExp_state (t : ℝ≥0) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) :
    (tsLaw Q K)[fun ω => f (tsState t ω) | tsPastSigma d] =ᵐ[tsLaw Q K]
      fun ω => ∫ y, f y ∂envKernel K t (tsState 0 ω) := by
  have := tsLaw_isProbability Q hap K
  have hTm : Measurable (kernelPhysMean K f t) := measurable_kernelPhysMean K hf t
  have hTb : ∀ ω, |kernelPhysMean K f t ω| ≤ 1 := abs_kernelPhysMean_le K hfb t
  have hgfun : (fun ω => ∫ y, f y ∂envKernel K t (tsState 0 ω)) =
      fun ω => kernelPhysMean K f t (tsState 0 ω) := by
    funext ω
    exact integral_envKernel K t hf _
  rw [hgfun]
  have hgm : Measurable[tsPastSigma d] fun ω : TwoSidedSpace d =>
      kernelPhysMean K f t (tsState 0 ω) := hTm.comp (measurable_tsState_past le_rfl)
  have hgint : Integrable (fun ω : TwoSidedSpace d => kernelPhysMean K f t (tsState 0 ω))
      (tsLaw Q K) := Integrable.of_bound (hTm.comp (measurable_tsState 0)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hTb _)
  have hfint : Integrable (fun ω : TwoSidedSpace d => f (tsState t ω)) (tsLaw Q K) :=
    Integrable.of_bound (hf.comp (measurable_tsState t)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hfb _)
  have hset : ∀ s, MeasurableSet[tsPastSigma d] s →
      ∫ ω in s, kernelPhysMean K f t (tsState 0 ω) ∂tsLaw Q K =
        ∫ ω in s, f (tsState t ω) ∂tsLaw Q K := by
    intro s hs
    refine setIntegral_eq_of_generate tsPastSigma_le (tsPastWindowSets d)
      isPiSystem_tsPastWindowSets tsPastSigma_eq_generateFrom
      (hTm.comp (measurable_tsState 0)) (hf.comp (measurable_tsState t)) (fun ω => hTb _)
      (fun ω => hfb _) ?_ ?_ hs
    · intro u hu
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hu
      exact setIntegral_past_window hd D Q hap hK t hf hfb _ _ hm
    · have h := setIntegral_past_window hd D Q hap hK t hf hfb (dyadicMesh 1 0) (4 ^ 0)
        (u := Set.univ) MeasurableSet.univ
      simp only [Measure.restrict_univ] at h
      exact h
  exact (ae_eq_condExp_of_forall_setIntegral_eq tsPastSigma_le hfint
    (fun s _ _ => hgint.integrableOn) (fun s hs _ => hset s hs) hgm.aestronglyMeasurable).symm

end Annealed

end EinsteinFull.Blueprint
