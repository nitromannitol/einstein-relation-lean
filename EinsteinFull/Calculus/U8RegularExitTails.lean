import EinsteinFull.Calculus.U8RegularSignedMoments
import Mathlib.MeasureTheory.Integral.Layercake
import SubdiffusiveProcess.Processes.FellerRealizationRestart
import EinsteinFull.Calculus.S4PathClockSupport

open EinsteinRelation MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- The Euclidean displacement maximum over a compact time interval is continuous in the path. -/
theorem u8_continuous_euclidean_displacement_max {d : ℕ} (x : Vec d) (T : ℝ≥0) :
    Continuous (fun γ : Path d =>
      sSup ((fun t : ℝ≥0 => euclideanNorm (γ t - x)) '' Set.Icc 0 T)) := by
  apply IsCompact.continuous_sSup isCompact_Icc
  exact (Calculus.Feller.continuous_euclideanNorm d).comp
    ((continuous_eval : Continuous (fun p : Path d × ℝ≥0 => p.1 p.2)).sub continuous_const)

/-- The continuous-path Euclidean exit event is measurable, including equality at the boundary. -/
theorem u8_measurableSet_euclidean_path_exit {d : ℕ} (x : Vec d) (T : ℝ≥0) (R : ℝ) :
    MeasurableSet {γ : Path d | ∃ u : ℝ≥0, u ≤ T ∧ R ≤ euclideanNorm (γ u - x)} := by
  let M : Path d → ℝ := fun γ =>
    sSup ((fun t : ℝ≥0 => euclideanNorm (γ t - x)) '' Set.Icc 0 T)
  have heq : {γ : Path d | ∃ u : ℝ≥0, u ≤ T ∧ R ≤ euclideanNorm (γ u - x)} =
      {γ | R ≤ M γ} := by
    ext γ
    have hc : Continuous (fun t : ℝ≥0 => euclideanNorm (γ t - x)) :=
      (Calculus.Feller.continuous_euclideanNorm d).comp (γ.continuous.sub continuous_const)
    have hcompact : IsCompact ((fun t : ℝ≥0 => euclideanNorm (γ t - x))
        '' Set.Icc 0 T) := isCompact_Icc.image hc
    have hn : (Set.Icc (0 : ℝ≥0) T).Nonempty := ⟨0, le_rfl, bot_le⟩
    have hm := hcompact.sSup_mem (hn.image _)
    obtain ⟨u, hu, he⟩ := hm
    constructor
    · rintro ⟨v, hv, hR⟩
      exact hR.trans (le_csSup hcompact.bddAbove ⟨v, ⟨bot_le, hv⟩, rfl⟩)
    · intro h
      exact ⟨u, hu.2, by simpa [M, ← he] using h⟩
  rw [heq]
  exact measurableSet_le measurable_const (u8_continuous_euclidean_displacement_max x T).measurable

/-- A Euclidean exit entails a large displacement in at least one coordinate. -/
theorem u8_euclidean_path_exit_le_coordinate_max {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (Path d)) (x : Vec d) (T : ℝ≥0) (R : ℝ) :
    μ {γ | ∃ u : ℝ≥0, u ≤ T ∧ R ≤ euclideanNorm (γ u - x)} ≤
      ∑ i : Fin d, μ {γ | R / d ≤
        sSup ((fun u : ℝ≥0 => |(γ u) i - x i|) '' Set.Icc 0 T)} := by
  let E : Fin d → Set (Path d) := fun i => {γ | R / d ≤
    sSup ((fun u : ℝ≥0 => |(γ u) i - x i|) '' Set.Icc 0 T)}
  have hsub : {γ : Path d | ∃ u : ℝ≥0, u ≤ T ∧ R ≤ euclideanNorm (γ u - x)} ⊆
      ⋃ i, E i := by
    intro γ hγ
    obtain ⟨u, hu, hR⟩ := hγ
    obtain ⟨i, hi⟩ := c16_max_exists_coord_ge hd hR
    have hc : Continuous (fun v : ℝ≥0 => |(γ v) i - x i|) :=
      (((continuous_apply i).comp γ.continuous).sub continuous_const).abs
    have hb : BddAbove ((fun v : ℝ≥0 => |(γ v) i - x i|) '' Set.Icc 0 T) :=
      (isCompact_Icc.image hc).bddAbove
    apply Set.mem_iUnion.mpr
    refine ⟨i, hi.trans ?_⟩
    exact le_csSup hb ⟨u, ⟨bot_le, hu⟩, by simp⟩
  exact (measure_mono hsub).trans (measure_iUnion_fintype_le μ E)



/-- The signed physical coordinate exponential has a generator bound with one coefficient
uniform over all real tilts and coordinates. -/
theorem u8_regular_signed_coordinate_exp_generator_bound
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℝ) (j : Fin d) (y : Vec d),
      External.Draft.svGenerator (ω.1) (physicalDrift ω i lam)
        (fun z => Real.exp (q * z j)) y ≤
          B * (|q| + q ^ 2) * Real.exp (q * y j) := by
  obtain ⟨Ma, ha⟩ := (physical_svHypotheses hΛ hω i lam).2.2.1
  obtain ⟨Mb, hb⟩ := (physical_svHypotheses hΛ hω i lam).2.2.2.2.2
  let B : ℝ := |Mb| + |Ma| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro q j y
  have h := c16_svGenerator_coordinate_exp_le (ω.1)
    (physicalDrift ω i lam) j q y
    ((ha y j j).trans (le_abs_self Ma)) ((hb y j).trans (le_abs_self Mb))
  have hcoeff : |Mb| * |q| + |Ma| * q ^ 2 / 2 ≤ B * (|q| + q ^ 2) := by
    dsimp [B]
    nlinarith [abs_nonneg Mb, abs_nonneg Ma, abs_nonneg q, sq_nonneg q,
      mul_nonneg (abs_nonneg Mb) (sq_nonneg q),
      mul_nonneg (abs_nonneg Ma) (abs_nonneg q),
      mul_nonneg (abs_nonneg Ma) (sq_nonneg q)]
  have h' : External.Draft.svGenerator (ω.1) (physicalDrift ω i lam)
      (fun z => Real.exp (q * z j)) y ≤
        (|Mb| * |q| + |Ma| * q ^ 2 / 2) * Real.exp (q * y j) := by
    calc
      _ ≤ Real.exp (q * y j) * (|q| * |Mb| + q ^ 2 / 2 * |Ma|) := h
      _ = _ := by ring
  exact h'.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _))


/-- The signed generator integral before a truncated exit is controlled by the
stopped coordinate exponential, with a constant uniform in the tilt. -/
theorem u8_regular_signed_stopped_generator_path_bound
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℝ) (j : Fin d) (U : Set (Vec d)) (t : ℝ≥0) (γ : Path d),
      (∫ u in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTimeTrunc U t γ : ℝ),
        External.Draft.svGenerator (ω.1) (physicalDrift ω i lam)
          (fun y => Real.exp (q * y j)) (γ u.toNNReal)) ≤
        B * (|q| + q ^ 2) * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (q *
          (γ (MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ)) j) := by
  obtain ⟨B, hB, hbound⟩ := u8_regular_signed_coordinate_exp_generator_bound hΛ hω i lam
  refine ⟨B, hB, ?_⟩
  intro q j U t γ
  let r := MarkovProcess.ContinuousPath.exitTimeTrunc U t γ
  let f : ℝ → ℝ := fun u => External.Draft.svGenerator (ω.1)
    (physicalDrift ω i lam) (fun y => Real.exp (q * y j)) (γ u.toNNReal)
  let g : ℝ → ℝ := fun u => Real.exp (q * (γ u.toNNReal) j)
  have hg : Continuous g := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_apply j).comp (γ.continuous.comp continuous_real_toNNReal)))
  have hs := physical_svHypotheses hΛ hω i lam
  obtain ⟨Ma, ha⟩ := hs.2.2.1
  obtain ⟨Mb, hb⟩ := hs.2.2.2.2.2
  have hfi : IntervalIntegrable f volume 0 (r : ℝ) := by
    simpa only [f, External.Bass.generator_eq_svGenerator,
      External.Bass.pathMeasurableEquiv_symm_apply] using
      (External.Bass.intervalIntegrable_generator_path
        (by
          let : MeasurableSpace (Vec d) := MeasurableSpace.pi
          let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
          exact hs.1.measurable) hs.2.2.2.2.1
        ha hb ((contDiff_const.mul (contDiff_apply ℝ ℝ j)).exp)
        ((External.Bass.pathMeasurableEquiv d).symm γ) r)
  have hr : (r : ℝ) ≤ t := NNReal.coe_le_coe.mpr
    (MarkovProcess.ContinuousPath.exitTimeTrunc_le U t γ)
  have hbound' := c16_integral_generator_le_stopped f g hg (fun u => Real.exp_nonneg _)
    (by positivity : 0 ≤ B * (|q| + q ^ 2)) r.coe_nonneg hr hfi
    (fun u _ => hbound q j (γ u.toNNReal))
  refine hbound'.trans_eq ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le t.coe_nonneg] at hu
  have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
  have he := c16_exitTimeTrunc_min U γ u.toNNReal t
  rw [min_eq_left hut] at he
  have he' : ((MarkovProcess.ContinuousPath.exitTimeTrunc U u.toNNReal γ : ℝ≥0) : ℝ) =
      min u (r : ℝ) := by
    rw [he, NNReal.coe_min, Real.coe_toNNReal u hu.1]
  simp only [g, ← he', Real.toNNReal_coe]

#print axioms u8_regular_signed_stopped_generator_path_bound

#print axioms u8_regular_signed_coordinate_exp_generator_bound

/-- The supplied path law has the same uniform Gaussian endpoint bound as its kernel. -/
theorem u8_regular_signed_path_endpoint_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
        K x {γ | R ≤ euclideanNorm (γ t - x)} ≤
          ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_signed_kernel_gaussian_tail hd ω lam Λ hΛ hω
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht x R hR
  have hs : MeasurableSet {y : Vec d | R ≤ euclideanNorm (y - x)} :=
    measurableSet_le measurable_const
      ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)).measurable
  have he := Blueprint.k11_endpoint
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd t x
  have he' := congrArg (fun μ : Measure (Vec d) =>
    μ {y | R ≤ euclideanNorm (y - x)}) he
  rw [Measure.map_apply (measurable_pathPosition t) hs] at he'
  change K x ((pathPosition t) ⁻¹' {y : Vec d | R ≤ euclideanNorm (y - x)}) ≤ _
  exact (le_of_eq he').trans (hbound t ht x R hR)

/-- A past event and a shifted measurable event have the same-law restart formula. -/
theorem u8_regular_path_restart_measure
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ≥0) (E S : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E) (hS : MeasurableSet S) :
    K x (E ∩ (gmpShiftPath s) ⁻¹' S) =
      ∫⁻ γ in E, K (γ s) S ∂K x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let μ := (K x).restrict E
  let Q := Kernel.comap K (pathPosition s) (measurable_pathPosition s)
  have hEc : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] E := by
    rw [← pathFiltration_eq_canonical]
    exact hE
  have hs : MarkovProcess.ContinuousPath.shift s = gmpShiftPath (d := d) s := by
    funext γ
    ext t
    rfl
  have hr : μ.map (gmpShiftPath s) = Q ∘ₘ μ := by
    rw [← hs]
    exact MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.realization_restrict_map_shift
      P (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
      (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
      ⟨fun _ => 0, continuous_const⟩ K hfdd x s E hEc
  have he := congrArg (fun ν : Measure (Path d) => ν S) hr
  rw [Measure.map_apply (measurable_gmpShiftPath s) hS,
    Measure.comp_eq_comp_const_apply, Kernel.comp_apply' _ _ _ hS] at he
  rw [Measure.restrict_apply (hS.preimage (measurable_gmpShiftPath s)), Set.inter_comm] at he
  simpa only [μ, Q, Kernel.comap_apply, Kernel.const_apply, pathPosition] using he

/-- The conditional displacement after a deterministic time has the same Gaussian
bound, uniformly over the past event and its starting point. -/
theorem u8_regular_signed_path_increment_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (s t : ℝ≥0), 0 < t →
      ∀ (x : Vec d) (R : ℝ), 0 ≤ R → ∀ (E : Set (Path d)),
        MeasurableSet[pathFiltration d s] E →
        K x (E ∩ {γ | R ≤ euclideanNorm (γ (s + t) - γ s)}) ≤
          K x E * ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_signed_path_endpoint_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro s t ht x R hR E hE
  let S : Set (Path d) := {γ | R ≤ euclideanNorm (γ t - γ 0)}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_eval_const t).sub (continuous_eval_const 0))).measurable
  have hSbound (y : Vec d) : K y S ≤
      ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
    calc
      K y S ≤ K y {γ | R ≤ euclideanNorm (γ t - y)} := by
        apply measure_mono_ae
        filter_upwards [Blueprint.k11_starts_at
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd y] with γ hγ
        intro h
        change R ≤ euclideanNorm (γ t - γ 0) at h
        change γ 0 = y at hγ
        simpa only [hγ] using h
      _ ≤ _ := hbound t ht y R hR
  have he := u8_regular_path_restart_measure hd ω lam Λ hΛ hω K hfdd x s E S hE hS
  have he' : K x (E ∩ {γ | R ≤ euclideanNorm (γ (s + t) - γ s)}) =
      ∫⁻ γ in E, K (γ s) S ∂K x := by
    have hpre : (gmpShiftPath s) ⁻¹' S =
        {γ | R ≤ euclideanNorm (γ (s + t) - γ s)} := by
      ext γ
      change (R ≤ euclideanNorm (γ (s + t) - γ (s + 0))) ↔ _
      rw [add_zero]
      rfl
    rw [hpre] at he
    exact he
  rw [he']
  calc
    _ ≤ ∫⁻ _ in E, ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) ∂K x :=
      lintegral_mono fun γ => hSbound (γ s)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- The same conditional increment estimate is uniform over every shorter
positive duration in a fixed time horizon. -/
theorem u8_regular_signed_path_increment_gaussian_horizon
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T s t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (x : Vec d) (R : ℝ), 0 ≤ R → ∀ (E : Set (Path d)),
        MeasurableSet[pathFiltration d s] E →
        K x (E ∩ {γ | R ≤ euclideanNorm (γ (s + t) - γ s)}) ≤
          K x E * ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * R ^ 2 / (T : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_signed_path_increment_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T s t ht htT x R hR E hE
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have hfrac : c * R ^ 2 / (T : ℝ) ≤ c * R ^ 2 / (t : ℝ) :=
    div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg R)) ht' htT'
  apply (hbound s t ht x R hR E hE).trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The first threshold crossing of an increasing time grid is a past event. -/
theorem u8_grid_first_exit_past {d : ℕ} (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (x : Vec d) (R : ℝ) (n : ℕ) :
    MeasurableSet[pathFiltration d (τ n)]
      ({γ : Path d | R ≤ euclideanNorm (γ (τ n) - x)} \
        ⋃ k < n, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)}) := by
  have hA (k : ℕ) (hk : k ≤ n) :
      MeasurableSet[pathFiltration d (τ n)]
        {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)} := by
    have hm : Measurable[pathFiltration d (τ n)] (fun γ : Path d => γ (τ k)) := by
      rw [pathFiltration_eq_canonical]
      exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) (τ k)).mono
          ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).mono (hτ hk)) le_rfl
    exact measurableSet_le measurable_const
      ((Calculus.Feller.continuous_euclideanNorm d).measurable.comp (hm.sub measurable_const))
  apply (hA n le_rfl).diff
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => hA k (Nat.le_of_lt hk)

/-- First threshold crossings at distinct grid indices are disjoint. -/
theorem u8_grid_first_exit_disjoint {d : ℕ} (τ : ℕ → ℝ≥0) (x : Vec d) (R : ℝ) :
    Pairwise (fun i j => Disjoint
      ({γ : Path d | R ≤ euclideanNorm (γ (τ i) - x)} \
        ⋃ k < i, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)})
      ({γ : Path d | R ≤ euclideanNorm (γ (τ j) - x)} \
        ⋃ k < j, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)})) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro γ hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact hj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨h, hi.1⟩⟩)
  · exact hi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h, hj.1⟩⟩)

/-- A finite grid exit is the union of the disjoint first-crossing events. -/
theorem u8_grid_exit_eq_first_crossings {d : ℕ} (τ : ℕ → ℝ≥0) (x : Vec d)
    (R : ℝ) (n : ℕ) :
    (⋃ k ≤ n, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)}) =
      ⋃ k ≤ n, ({γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)} \
        ⋃ j < k, {γ : Path d | R ≤ euclideanNorm (γ (τ j) - x)}) := by
  ext γ
  constructor
  · intro h
    obtain ⟨k, hk, hkγ⟩ := Set.mem_iUnion₂.mp h
    have hex : ∃ j : ℕ, R ≤ euclideanNorm (γ (τ j) - x) := ⟨k, hkγ⟩
    let m := Nat.find hex
    have hm : m ≤ k := Nat.find_min' hex hkγ
    apply Set.mem_iUnion₂.mpr
    refine ⟨m, hm.trans hk, Nat.find_spec hex, ?_⟩
    intro hmem
    obtain ⟨j, hj, hjγ⟩ := Set.mem_iUnion₂.mp hmem
    exact Nat.find_min hex hj hjγ
  · intro h
    obtain ⟨k, hk, hkγ⟩ := Set.mem_iUnion₂.mp h
    exact Set.mem_iUnion₂.mpr ⟨k, hk, hkγ.1⟩

#print axioms u8_grid_exit_eq_first_crossings

/-- A first crossing forces either a large terminal displacement or a large
increment from the crossing time to the terminal time. -/
theorem u8_exit_terminal_or_increment {d : ℕ} (x y z : Vec d) (R : ℝ)
    (hR : R ≤ euclideanNorm (y - x)) :
    R / 2 ≤ euclideanNorm (z - x) ∨ R / 2 ≤ euclideanNorm (z - y) := by
  have htri := TimeChange.euclideanNorm_add_le (z - x) (y - z)
  have heq : z - x + (y - z) = y - x := by abel
  rw [heq, ← neg_sub z y, Entropy.euclideanNorm_neg'] at htri
  rcases le_total (R / 2) (euclideanNorm (z - x)) with h | h
  · exact Or.inl h
  · right
    linarith

#print axioms u8_exit_terminal_or_increment

/-- A first-crossing event is controlled by terminal displacement and the
conditional Gaussian estimate for the remaining increment. -/
theorem u8_regular_grid_first_exit_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n < T → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      let F := {γ : Path d | R ≤ euclideanNorm (γ (τ n) - x)} \
        ⋃ k < n, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)}
      K x F ≤ K x (F ∩ {γ | R / 2 ≤ euclideanNorm (γ T - x)}) +
        K x F * ENNReal.ofReal (C * Real.exp
          (C * (T : ℝ) - c * (R / 2) ^ 2 / (T : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_signed_path_increment_gaussian_horizon hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T τ hτ n hn x R hR F
  have hF : MeasurableSet[pathFiltration d (τ n)] F :=
    u8_grid_first_exit_past τ hτ x R n
  have ht : 0 < T - τ n := tsub_pos_of_lt hn
  have hinc := hbound T (τ n) (T - τ n) ht (tsub_le_self) x (R / 2)
    (by positivity) F hF
  have htime : τ n + (T - τ n) = T := add_tsub_cancel_of_le hn.le
  rw [htime] at hinc
  calc
    K x F ≤ K x ((F ∩ {γ | R / 2 ≤ euclideanNorm (γ T - x)}) ∪
        (F ∩ {γ | R / 2 ≤ euclideanNorm (γ T - γ (τ n))})) := by
      apply measure_mono
      intro γ hγ
      rcases u8_exit_terminal_or_increment x (γ (τ n)) (γ T) R hγ.1 with h | h
      · exact Or.inl ⟨hγ, h⟩
      · exact Or.inr ⟨hγ, h⟩
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hinc)

#print axioms u8_regular_grid_first_exit_gaussian_bound

/-- Summing disjoint event estimates preserves the total mass in the
multiplicative remainder. -/
theorem u8_measure_disjoint_union_bound {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (F : ι → Set α) (B : Set α) (q : ℝ≥0∞)
    (hdisj : (↑s : Set ι).PairwiseDisjoint F)
    (hmeas : ∀ i ∈ s, MeasurableSet (F i)) (hB : MeasurableSet B)
    (hbound : ∀ i ∈ s, μ (F i) ≤ μ (F i ∩ B) + μ (F i) * q) :
    μ (⋃ i ∈ s, F i) ≤ μ B + μ (⋃ i ∈ s, F i) * q := by
  have hdisj' : (↑s : Set ι).PairwiseDisjoint (fun i => F i ∩ B) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Set.inter_subset_left Set.inter_subset_left
  have hsum : μ (⋃ i ∈ s, F i) = ∑ i ∈ s, μ (F i) :=
    measure_biUnion_finset hdisj hmeas
  have hsum' : μ (⋃ i ∈ s, F i ∩ B) = ∑ i ∈ s, μ (F i ∩ B) :=
    measure_biUnion_finset hdisj' (fun i hi => (hmeas i hi).inter hB)
  have hle : μ (⋃ i ∈ s, F i ∩ B) ≤ μ B := by
    apply measure_mono
    intro x hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    exact hx.2
  calc
    μ (⋃ i ∈ s, F i) = ∑ i ∈ s, μ (F i) := hsum
    _ ≤ ∑ i ∈ s, (μ (F i ∩ B) + μ (F i) * q) :=
      Finset.sum_le_sum hbound
    _ = (∑ i ∈ s, μ (F i ∩ B)) + (∑ i ∈ s, μ (F i)) * q := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ μ B + μ (⋃ i ∈ s, F i) * q := by
      rw [← hsum', ← hsum]
      exact add_le_add hle le_rfl

#print axioms u8_measure_disjoint_union_bound

/-- The finite-grid exit mass is bounded by the endpoint tail plus the
exit mass times a uniform Gaussian increment factor. -/
theorem u8_regular_grid_exit_gaussian_remainder
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n < T → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤
        K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} +
        K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) *
          ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * (R / 2) ^ 2 / (T : ℝ))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_grid_first_exit_gaussian_bound hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T τ hτ n hn x R hR
  let F : ℕ → Set (Path d) := fun i =>
    {γ | R ≤ euclideanNorm (γ (τ i) - x)} \
      ⋃ k < i, {γ | R ≤ euclideanNorm (γ (τ k) - x)}
  let B : Set (Path d) := {γ | R / 2 ≤ euclideanNorm (γ T - x)}
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    exact u8_grid_first_exit_disjoint τ x R hij
  have hmeas : ∀ i ∈ Finset.range (n + 1), MeasurableSet (F i) := by
    intro i hi
    exact (pathFiltration d).le (τ i) (F i) (u8_grid_first_exit_past τ hτ x R i)
  have hB : MeasurableSet B := by
    exact measurableSet_le measurable_const
      (((Calculus.Feller.continuous_euclideanNorm d).comp
        ((continuous_eval_const T).sub continuous_const)).measurable)
  have hs := u8_measure_disjoint_union_bound (K x) (Finset.range (n + 1)) F B
    (ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * (R / 2) ^ 2 / (T : ℝ))))
    hdisj hmeas hB (by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact hbound T τ hτ i ((hτ hi').trans_lt hn) x R hR)
  have hU : (⋃ i ∈ Finset.range (n + 1), F i) =
      ⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)} := by
    rw [u8_grid_exit_eq_first_crossings]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    rfl
  rw [hU] at hs
  exact hs

#print axioms u8_regular_grid_exit_gaussian_remainder

/-- A finite extended-real mass absorbs a remainder of at most one half. -/
theorem u8_ennreal_absorb_half (a b q : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hq : q ≤ 1 / 2) (h : a ≤ b + a * q) : a ≤ 2 * b := by
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hq
  have hm : a * q ≠ ⊤ := ENNReal.mul_ne_top ha hqtop
  have htop : b + a * q ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hb, hm⟩
  have hr : a.toReal ≤ b.toReal + a.toReal * q.toReal := by
    have hh := ENNReal.toReal_mono htop h
    simpa only [ENNReal.toReal_add hb hm, ENNReal.toReal_mul] using hh
  have hqr : q.toReal ≤ (1 / 2 : ℝ) := by
    have hh := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hq
    simpa using hh
  have hn : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hf : 2 * b ≠ ⊤ := ENNReal.mul_ne_top (by simp) hb
  apply (ENNReal.toReal_le_toReal ha hf).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hqr)]

#print axioms u8_ennreal_absorb_half

/-- An estimate with a probabilistic mass and a multiplicative remainder
is bounded by twice the sum of the endpoint term and remainder. -/
theorem u8_ennreal_probability_remainder (a b q : ℝ≥0∞) (ha : a ≤ 1)
    (hb : b ≠ ⊤) (h : a ≤ b + a * q) : a ≤ 2 * (b + q) := by
  by_cases hq : q ≤ 1 / 2
  · have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
    exact (u8_ennreal_absorb_half a b q ha' hb hq h).trans
      (mul_le_mul' le_rfl (le_add_right le_rfl))
  · calc
      a ≤ 1 := ha
      _ = 2 * (1 / 2 : ℝ≥0∞) := by
        symm
        simpa only [one_div] using
          (ENNReal.mul_inv_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num))
      _ ≤ 2 * q := mul_le_mul' le_rfl (le_of_not_ge hq)
      _ ≤ 2 * (b + q) := mul_le_mul' le_rfl (le_add_left le_rfl)

#print axioms u8_ennreal_probability_remainder

/-- An increasing finite grid has a uniform bound by the endpoint tail and
a Gaussian increment factor. -/
theorem u8_regular_grid_exit_gaussian_two_terms
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n < T → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤
        2 * (K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} +
          ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * (R / 2) ^ 2 / (T : ℝ)))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ :=
    u8_regular_grid_exit_gaussian_remainder hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T τ hτ n hn x R hR
  apply u8_ennreal_probability_remainder
  · calc
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤ K x Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  · exact measure_ne_top _ _
  · exact hbound T τ hτ n hn x R hR

#print axioms u8_regular_grid_exit_gaussian_two_terms

/-- The finite-grid exit probability satisfies a single Gaussian bound,
uniformly in the grid. -/
theorem u8_regular_grid_exit_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n < T → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤
        ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * R ^ 2 / (T : ℝ))) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hgrid⟩ :=
    u8_regular_grid_exit_gaussian_two_terms hd ω lam Λ hΛ hω K hfdd
  obtain ⟨C₂, c₂, hC₂, hc₂, hend⟩ :=
    u8_regular_signed_path_endpoint_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  let C : ℝ := 2 * (C₁ + C₂) + 1
  let c : ℝ := min c₁ c₂ / 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hC₁C : C₁ ≤ C := by dsimp [C]; linarith
  have hC₂C : C₂ ≤ C := by dsimp [C]; linarith
  have hc₁c : c ≤ c₁ / 4 := by dsimp [c]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hc₂c : c ≤ c₂ / 4 := by dsimp [c]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨C, c, hC, hc, ?_⟩
  intro T τ hτ n hn x R hR
  have ht : 0 < T := lt_of_le_of_lt bot_le hn
  have ht' : 0 ≤ (T : ℝ) := by exact_mod_cast (bot_le : (0 : ℝ≥0) ≤ T)
  have hrad : 0 ≤ R / 2 := by positivity
  let z : ℝ := C * (T : ℝ) - c * R ^ 2 / (T : ℝ)
  have hexp₁ : C₁ * (T : ℝ) - c₁ * (R / 2) ^ 2 / (T : ℝ) ≤ z := by
    have htime := mul_le_mul_of_nonneg_right hC₁C ht'
    have hradius := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₁c (sq_nonneg R)) ht'
    have heq : c₁ * (R / 2) ^ 2 / (T : ℝ) = (c₁ / 4) * R ^ 2 / (T : ℝ) := by ring
    dsimp [z]
    rw [heq]
    linarith
  have hexp₂ : C₂ * (T : ℝ) - c₂ * (R / 2) ^ 2 / (T : ℝ) ≤ z := by
    have htime := mul_le_mul_of_nonneg_right hC₂C ht'
    have hradius := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc₂c (sq_nonneg R)) ht'
    have heq : c₂ * (R / 2) ^ 2 / (T : ℝ) = (c₂ / 4) * R ^ 2 / (T : ℝ) := by ring
    dsimp [z]
    rw [heq]
    linarith
  have h₁ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp₁) hC₁.le)
  have h₂ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp₂) hC₂.le)
  calc
    _ ≤ 2 * (K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} +
        ENNReal.ofReal (C₁ * Real.exp (C₁ * (T : ℝ) - c₁ * (R / 2) ^ 2 / (T : ℝ)))) :=
      hgrid T τ hτ n hn x R hR
    _ ≤ 2 * (ENNReal.ofReal (C₂ * Real.exp z) + ENNReal.ofReal (C₁ * Real.exp z)) :=
      mul_le_mul' le_rfl (add_le_add ((hend T ht x (R / 2) hrad).trans h₂) h₁)
    _ = ENNReal.ofReal (2 * (C₂ * Real.exp z + C₁ * Real.exp z)) := by
      symm
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    _ ≤ ENNReal.ofReal (C * Real.exp z) := by
      apply ENNReal.ofReal_le_ofReal
      have hfac : 2 * (C₂ + C₁) ≤ C := by dsimp [C]; linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hfac) (Real.exp_nonneg z)]

#print axioms u8_regular_grid_exit_gaussian_tail

/-- A finite set of observation times can be ordered without changing the
uniform exit bound. -/
theorem u8_regular_finite_exit_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0), 0 < T →
      ∀ (s : Finset ℝ≥0), (∀ t ∈ s, t < T) → ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
      K x (⋃ t ∈ s, {γ | R ≤ euclideanNorm (γ t - x)}) ≤
        ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * R ^ 2 / (T : ℝ))) := by
  obtain ⟨C, c, hC, hc, hgrid⟩ :=
    u8_regular_grid_exit_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT s hs x R hR
  let a : Finset ℝ≥0 := insert 0 s
  have ha : 0 < a.card := Finset.card_pos.mpr ⟨0, by simp [a]⟩
  let τ : ℕ → ℝ≥0 := fun k =>
    a.orderEmbOfFin rfl ⟨min k (a.card - 1), by omega⟩
  have hτ : Monotone τ := by
    intro i j hij
    apply (a.orderEmbOfFin rfl).monotone
    exact min_le_min_right _ hij
  have hmem (k : ℕ) : τ k ∈ a := a.orderEmbOfFin_mem rfl _
  have hlt : τ (a.card - 1) < T := by
    have := hmem (a.card - 1)
    simp only [a, Finset.mem_insert] at this
    rcases this with h | h
    · change τ ((insert 0 s).card - 1) < T
      rw [h]
      exact hT
    · exact hs _ h
  have hsub : (⋃ t ∈ s, {γ : Path d | R ≤ euclideanNorm (γ t - x)}) ⊆
      (⋃ k ≤ a.card - 1, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)}) := by
    intro γ hγ
    rcases Set.mem_iUnion.mp hγ with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨ht, hγ⟩
    have hta : t ∈ a := by simp [a, ht]
    have htr : t ∈ Set.range (a.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hta
    obtain ⟨i, hi⟩ := htr
    apply Set.mem_iUnion.mpr
    refine ⟨i.val, Set.mem_iUnion.mpr ⟨by omega, ?_⟩⟩
    have hti : τ i.val = t := by
      dsimp [τ]
      have hfin : (⟨min i.val (a.card - 1), by omega⟩ : Fin a.card) = i :=
        Fin.ext (min_eq_left (by omega))
      rw [hfin]
      exact hi
    simpa [hti] using hγ
  exact (measure_mono hsub).trans (hgrid T τ hτ (a.card - 1) hlt x R hR)

#print axioms u8_regular_finite_exit_gaussian_tail

/-- The finite-set bound extends to any countable collection of observation times. -/
theorem u8_regular_countable_exit_gaussian_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (T : ℝ≥0), 0 < T →
      ∀ {ι : Type} [Countable ι] (v : ι → ℝ≥0) (x : Vec d) (R : ℝ), 0 ≤ R →
      K x (⋃ i, ⋃ (_ : v i < T), {γ | R ≤ euclideanNorm (γ (v i) - x)}) ≤
        ENNReal.ofReal (C * Real.exp (C * (T : ℝ) - c * R ^ 2 / (T : ℝ))) := by
  classical
  obtain ⟨C, c, hC, hc, hfinite⟩ :=
    u8_regular_finite_exit_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT ι _ v x R hR
  let U : Finset ι → Set (Path d) := fun s =>
    ⋃ i ∈ s, ⋃ (_ : v i < T), {γ | R ≤ euclideanNorm (γ (v i) - x)}
  have hU : Monotone U := by
    intro s t hst γ hγ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hγ ⊢
    obtain ⟨i, hi, hit, hγ⟩ := hγ
    exact ⟨i, hst hi, hit, hγ⟩
  have hcover : (⋃ i, ⋃ (_ : v i < T),
      {γ : Path d | R ≤ euclideanNorm (γ (v i) - x)}) = ⋃ s, U s := by
    ext γ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hγ⟩
      exact ⟨{i}, i, by simp, hi, hγ⟩
    · rintro ⟨s, i, hi, hit, hγ⟩
      exact ⟨i, hit, hγ⟩
  rw [hcover, hU.directed_le.measure_iUnion]
  apply iSup_le
  intro s
  let a : Finset ℝ≥0 := (s.image v).filter (fun t => t < T)
  have ha : ∀ t ∈ a, t < T := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hsub : U s ⊆ ⋃ t ∈ a, {γ : Path d | R ≤ euclideanNorm (γ t - x)} := by
    intro γ hγ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hγ ⊢
    obtain ⟨i, hi, hit, hγ⟩ := hγ
    refine ⟨v i, ?_, hγ⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, hit⟩
  exact (measure_mono hsub).trans (hfinite T hT a ha x R hR)

#print axioms u8_regular_countable_exit_gaussian_tail

/-- Gaussian exit tail for the supplied signed regular physical path law. -/
theorem u8_regular_signed_physical_path_exit_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (x : Vec d) (R : ℝ), 0 ≤ R →
        K x {γ | ∃ u : ℝ≥0, u ≤ t ∧ R ≤ euclideanNorm (γ u - x)} ≤
          ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hcount⟩ :=
    u8_regular_countable_exit_gaussian_tail hd ω lam Λ hΛ hω K hfdd
  let C : ℝ := 2 * C₀ + 1
  let c : ℝ := c₀ / 8
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  have hCC : C₀ ≤ C := by dsimp [C]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro t ht x R hR
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  rcases eq_or_lt_of_le hR with rfl | hR
  · have hexp : 1 ≤ Real.exp (C * (t : ℝ)) := Real.one_le_exp (by positivity)
    have hbound : 1 ≤ C * Real.exp (C * (t : ℝ)) := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ C * Real.exp (C * (t : ℝ)) := mul_le_mul hC1 hexp (by norm_num) hC.le
    calc
      K x {γ | ∃ u : ℝ≥0, u ≤ t ∧ (0 : ℝ) ≤ euclideanNorm (γ u - x)} ≤ K x Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * (0 : ℝ) ^ 2 / (t : ℝ))) := by
        simpa using ENNReal.ofReal_le_ofReal hbound
  · let v : ℚ → ℝ≥0 := fun q => (q : ℝ).toNNReal
    have hv : DenseRange v := by
      have hs : Function.Surjective Real.toNNReal := by
        intro y
        exact ⟨(y : ℝ), by simp⟩
      exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
    have hsub : {γ : Path d | ∃ u : ℝ≥0, u ≤ t ∧ R ≤ euclideanNorm (γ u - x)} ⊆
        ⋃ q, ⋃ (_ : v q < 2 * t),
          {γ : Path d | R / 2 ≤ euclideanNorm (γ (v q) - x)} := by
      intro γ hγ
      obtain ⟨u, hu, huR⟩ := hγ
      have hcont : Continuous (fun z : ℝ≥0 => euclideanNorm (γ z - x)) :=
        (Calculus.Feller.continuous_euclideanNorm d).comp (γ.continuous.sub continuous_const)
      let U : Set ℝ≥0 := Set.Iio (2 * t) ∩
        (fun z : ℝ≥0 => euclideanNorm (γ z - x)) ⁻¹' Set.Ioi (R / 2)
      have hopen : IsOpen U := isOpen_Iio.inter (isOpen_Ioi.preimage hcont)
      have huT : u < 2 * t := by nlinarith
      have huU : u ∈ U := ⟨huT, by
        change R / 2 < euclideanNorm (γ u - x)
        linarith⟩
      obtain ⟨q, hq⟩ := hv.exists_mem_open hopen ⟨u, huU⟩
      change v q < 2 * t ∧ R / 2 < euclideanNorm (γ (v q) - x) at hq
      apply Set.mem_iUnion.mpr
      refine ⟨q, Set.mem_iUnion.mpr ⟨hq.1, ?_⟩⟩
      exact le_of_lt hq.2
    have hdiv : c₀ * (R / 2) ^ 2 / ((2 * t : ℝ≥0) : ℝ) = c * R ^ 2 / (t : ℝ) := by
      dsimp [c]
      field_simp [ne_of_gt ht']
      ring
    have hexp : C₀ * ((2 * t : ℝ≥0) : ℝ) - c₀ * (R / 2) ^ 2 / ((2 * t : ℝ≥0) : ℝ) ≤
        C * (t : ℝ) - c * R ^ 2 / (t : ℝ) := by
      rw [hdiv]
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      nlinarith [mul_nonneg (sub_nonneg.mpr (show 2 * C₀ ≤ C by dsimp [C]; linarith)) ht'.le]
    calc
      K x {γ | ∃ u : ℝ≥0, u ≤ t ∧ R ≤ euclideanNorm (γ u - x)} ≤
          K x (⋃ q, ⋃ (_ : v q < 2 * t), {γ | R / 2 ≤ euclideanNorm (γ (v q) - x)}) :=
        measure_mono hsub
      _ ≤ ENNReal.ofReal (C₀ * Real.exp
          (C₀ * ((2 * t : ℝ≥0) : ℝ) - c₀ * (R / 2) ^ 2 / ((2 * t : ℝ≥0) : ℝ))) :=
        hcount (2 * t) (by positivity) v x (R / 2) (by positivity)
      _ ≤ ENNReal.ofReal (C * Real.exp (C * (t : ℝ) - c * R ^ 2 / (t : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul hCC (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) hC.le

#print axioms u8_regular_signed_physical_path_exit_tail

#print axioms u8_grid_first_exit_past
#print axioms u8_grid_first_exit_disjoint

#print axioms u8_regular_signed_path_increment_gaussian_horizon

#print axioms u8_regular_signed_path_increment_gaussian_tail

#print axioms u8_regular_path_restart_measure

#print axioms u8_regular_signed_path_endpoint_gaussian_tail

#print axioms u8_euclidean_path_exit_le_coordinate_max

#print axioms u8_measurableSet_euclidean_path_exit

/-- The literal indexed Euclidean path maximum is continuous in the path. -/
theorem u8_continuous_euclidean_displacement_iSup {d : ℕ} (x : Vec d) (T : ℝ≥0) :
    Continuous (fun γ : Path d =>
      ⨆ u : Set.Icc (0 : ℝ≥0) T, euclideanNorm (γ (u : ℝ≥0) - x)) := by
  convert u8_continuous_euclidean_displacement_max x T using 1
  funext γ
  change sSup (Set.range (fun u : Set.Icc (0 : ℝ≥0) T =>
    euclideanNorm (γ (u : ℝ≥0) - x))) = _
  congr 1
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, u.property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

/-- The supplied same-FDD path law inherits the polynomial endpoint fourth moment. -/
theorem u8_regular_signed_path_endpoint_fourth_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal (euclideanNorm (γ t - x) ^ 4) ∂K x) ≤
        ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  obtain ⟨C, hC, hbound⟩ := u8_regular_signed_kernel_fourth_increment hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t x
  have he := Blueprint.k11_endpoint
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd t x
  have hm : Measurable (fun y : Vec d => ENNReal.ofReal (euclideanNorm (y - x) ^ 4)) :=
    ENNReal.measurable_ofReal.comp
      (((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)).pow 4).measurable
  have hi := lintegral_map (μ := K x) hm (measurable_pathPosition t)
  rw [he] at hi
  exact hi.symm.le.trans (hbound t x)

#print axioms u8_continuous_euclidean_displacement_iSup
#print axioms u8_regular_signed_path_endpoint_fourth_moment

/-- The supplied path law inherits the tilt-uniform radial exponential bound. -/
theorem u8_regular_signed_path_endpoint_uniform_euclidean_mgf
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ), 0 ≤ q → ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal (Real.exp (q * euclideanNorm (γ t - x))) ∂K x) ≤
        ENNReal.ofReal ((2 * d) * Real.exp (C * (q + q ^ 2) * (t : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := u8_regular_signed_uniform_euclidean_mgf hd ω lam Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro q hq t x
  have he := Blueprint.k11_endpoint
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd t x
  have hm : Measurable (fun y : Vec d =>
      ENNReal.ofReal (Real.exp (q * euclideanNorm (y - x)))) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
      (continuous_const.mul ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)))).measurable)
  have hi := lintegral_map (μ := K x) hm (measurable_pathPosition t)
  rw [he] at hi
  exact hi.symm.le.trans (hbound q hq t x)

#print axioms u8_regular_signed_path_endpoint_uniform_euclidean_mgf

/-- At the diffusive-plus-drift scale, endpoint exponential moments are uniform in time. -/
theorem u8_regular_signed_path_endpoint_scaled_exponential
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal
        (Real.exp (euclideanNorm (γ t - x) / (Real.sqrt (t : ℝ) + (t : ℝ)))) ∂K x) ≤
          ENNReal.ofReal C := by
  obtain ⟨B, hB, hbound⟩ :=
    u8_regular_signed_path_endpoint_uniform_euclidean_mgf hd ω lam Λ hΛ hω K hfdd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨(2 * d) * Real.exp (2 * B), by positivity, ?_⟩
  intro t ht x
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  let S : ℝ := Real.sqrt (t : ℝ) + (t : ℝ)
  have hS : 0 < S := by dsimp [S]; positivity
  have hSt : (t : ℝ) ≤ S := by dsimp [S]; linarith [Real.sqrt_nonneg (t : ℝ)]
  have hsq : (t : ℝ) ≤ S ^ 2 := by
    dsimp [S]
    nlinarith [Real.sq_sqrt ht'.le, Real.sqrt_nonneg (t : ℝ),
      mul_nonneg (Real.sqrt_nonneg (t : ℝ)) ht'.le, sq_nonneg (t : ℝ)]
  have h1 : (t : ℝ) / S ≤ 1 := (div_le_one hS).2 hSt
  have h2 : (t : ℝ) / S ^ 2 ≤ 1 := (div_le_one (pow_pos hS 2)).2 hsq
  have hscale : (S⁻¹ + (S⁻¹) ^ 2) * (t : ℝ) ≤ 2 := by
    have he : (S⁻¹ + (S⁻¹) ^ 2) * (t : ℝ) =
        (t : ℝ) / S + (t : ℝ) / S ^ 2 := by
      field_simp [ne_of_gt hS]
    rw [he]
    linarith
  have hb := hbound S⁻¹ (inv_nonneg.mpr hS.le) t x
  have hexp : B * (S⁻¹ + (S⁻¹) ^ 2) * (t : ℝ) ≤ 2 * B := by
    have h := mul_le_mul_of_nonneg_left hscale hB.le
    nlinarith
  calc
    _ = ∫⁻ γ : Path d, ENNReal.ofReal
        (Real.exp (S⁻¹ * euclideanNorm (γ t - x))) ∂K x := by
          apply lintegral_congr
          intro γ
          congr 2
          rw [div_eq_mul_inv, mul_comm]
    _ ≤ ENNReal.ofReal ((2 * d) * Real.exp
        (B * (S⁻¹ + (S⁻¹) ^ 2) * (t : ℝ))) := hb
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)

#print axioms u8_regular_signed_path_endpoint_scaled_exponential

/-- A nonnegative exponential moment controls every natural-power moment. -/
theorem u8_lintegral_pow_le_factorial_exp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (∫⁻ a, ENNReal.ofReal (f a ^ n) ∂μ) ≤
      ENNReal.ofReal (n.factorial : ℝ) *
        (∫⁻ a, ENNReal.ofReal (Real.exp (f a)) ∂μ) := by
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc
    _ ≤ ∫⁻ a, ENNReal.ofReal ((n.factorial : ℝ) * Real.exp (f a)) ∂μ := by
      apply lintegral_mono
      intro a
      apply ENNReal.ofReal_le_ofReal
      have h := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (f a) (hf a) n)
      nlinarith
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul hfac.le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

#print axioms u8_lintegral_pow_le_factorial_exp

/-- Every normalized endpoint power has a uniform bound over positive times. -/
theorem u8_regular_signed_path_endpoint_scaled_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal
        ((euclideanNorm (γ t - x) / (Real.sqrt (t : ℝ) + (t : ℝ))) ^ n) ∂K x) ≤
          ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ :=
    u8_regular_signed_path_endpoint_scaled_exponential hd ω lam Λ hΛ hω K hfdd
  intro n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  refine ⟨(n.factorial : ℝ) * B, by positivity, ?_⟩
  intro t ht x
  have hS : 0 ≤ Real.sqrt (t : ℝ) + (t : ℝ) := by positivity
  have h := u8_lintegral_pow_le_factorial_exp (K x)
    (fun γ => euclideanNorm (γ t - x) / (Real.sqrt (t : ℝ) + (t : ℝ)))
    (fun γ => div_nonneg (Real.sqrt_nonneg _) hS) n
  calc
    _ ≤ ENNReal.ofReal (n.factorial : ℝ) *
      (∫⁻ γ : Path d, ENNReal.ofReal
        (Real.exp (euclideanNorm (γ t - x) / (Real.sqrt (t : ℝ) + (t : ℝ)))) ∂K x) := h
    _ ≤ ENNReal.ofReal (n.factorial : ℝ) * ENNReal.ofReal B :=
      mul_le_mul' le_rfl (hb t ht x)
    _ = _ := (ENNReal.ofReal_mul hfac.le).symm

#print axioms u8_regular_signed_path_endpoint_scaled_moment

/-- Fourth-moment Markov bound for the actual supplied endpoint law. -/
theorem u8_regular_signed_path_endpoint_fourth_tail
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d) (R : ℝ), 0 < R →
      K x {γ | R ≤ euclideanNorm (γ t - x)} ≤
        ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4) / R ^ 4) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_signed_path_endpoint_fourth_moment hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro t x R hR
  let f : Path d → ℝ≥0∞ := fun γ => ENNReal.ofReal (euclideanNorm (γ t - x) ^ 4)
  have hf : Measurable f :=
    (((Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_eval_const t).sub continuous_const)).pow 4).measurable.ennreal_ofReal
  have hsub : {γ : Path d | R ≤ euclideanNorm (γ t - x)} ⊆
      {γ | ENNReal.ofReal (R ^ 4) ≤ f γ} := by
    intro γ hγ
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ hR.le hγ 4
  calc
    K x {γ | R ≤ euclideanNorm (γ t - x)} ≤
        K x {γ | ENNReal.ofReal (R ^ 4) ≤ f γ} := measure_mono hsub
    _ ≤ (∫⁻ γ, f γ ∂K x) / ENNReal.ofReal (R ^ 4) :=
      meas_ge_le_lintegral_div hf.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) /
        ENNReal.ofReal (R ^ 4) := by
      apply ENNReal.div_le_div_right
      exact hbound t x
    _ = _ := by rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < R ^ 4)]

/-- Polynomial conditional increment tail, uniform over shorter durations. -/
theorem u8_regular_signed_path_increment_fourth_horizon
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T s t : ℝ≥0), t ≤ T →
      ∀ (x : Vec d) (R : ℝ), 0 < R → ∀ (E : Set (Path d)),
        MeasurableSet[pathFiltration d s] E →
        K x (E ∩ {γ | R ≤ euclideanNorm (γ (s + t) - γ s)}) ≤
          K x E * ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / R ^ 4) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_signed_path_endpoint_fourth_tail hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro T s t ht x R hR E hE
  have ht' : (t : ℝ) ≤ T := by exact_mod_cast ht
  have htime : (t : ℝ) ^ 2 + (t : ℝ) ^ 4 ≤ (T : ℝ) ^ 2 + (T : ℝ) ^ 4 := by
    gcongr
  let S : Set (Path d) := {γ | R ≤ euclideanNorm (γ t - γ 0)}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((Calculus.Feller.continuous_euclideanNorm d).comp
      ((continuous_eval_const t).sub (continuous_eval_const 0))).measurable
  have hSbound (y : Vec d) : K y S ≤
      ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / R ^ 4) := by
    calc
      K y S ≤ K y {γ | R ≤ euclideanNorm (γ t - y)} := by
        apply measure_mono_ae
        filter_upwards [Blueprint.k11_starts_at
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd y] with γ hγ
        intro h
        change R ≤ euclideanNorm (γ t - γ 0) at h
        change γ 0 = y at hγ
        simpa only [hγ] using h
      _ ≤ ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4) / R ^ 4) :=
        hbound t y R hR
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htime hC.le) (by positivity)
  have he := u8_regular_path_restart_measure hd ω lam Λ hΛ hω K hfdd x s E S hE hS
  have hpre : (gmpShiftPath s) ⁻¹' S =
      {γ | R ≤ euclideanNorm (γ (s + t) - γ s)} := by
    ext γ
    change (R ≤ euclideanNorm (γ (s + t) - γ (s + 0))) ↔ _
    rw [add_zero]
    rfl
  rw [hpre] at he
  rw [he]
  calc
    _ ≤ ∫⁻ _ in E, ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / R ^ 4) ∂K x :=
      lintegral_mono fun γ => hSbound (γ s)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]

#print axioms u8_regular_signed_path_endpoint_fourth_tail
#print axioms u8_regular_signed_path_increment_fourth_horizon

/-- The fourth-moment remainder controls a finite grid of first exits. -/
theorem u8_regular_grid_exit_fourth_remainder
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n ≤ T → ∀ (x : Vec d) (R : ℝ), 0 < R →
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤
        K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} +
        K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) *
          ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / (R / 2) ^ 4) := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_signed_path_increment_fourth_horizon hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro T τ hτ n hn x R hR
  let F : ℕ → Set (Path d) := fun i =>
    {γ | R ≤ euclideanNorm (γ (τ i) - x)} \
      ⋃ k < i, {γ | R ≤ euclideanNorm (γ (τ k) - x)}
  let B : Set (Path d) := {γ | R / 2 ≤ euclideanNorm (γ T - x)}
  have hdisj : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    exact u8_grid_first_exit_disjoint τ x R hij
  have hmeas : ∀ i ∈ Finset.range (n + 1), MeasurableSet (F i) := by
    intro i hi
    exact (pathFiltration d).le (τ i) (F i) (u8_grid_first_exit_past τ hτ x R i)
  have hB : MeasurableSet B := by
    exact measurableSet_le measurable_const
      (((Calculus.Feller.continuous_euclideanNorm d).comp
        ((continuous_eval_const T).sub continuous_const)).measurable)
  have hs := u8_measure_disjoint_union_bound (K x) (Finset.range (n + 1)) F B
    (ENNReal.ofReal (C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / (R / 2) ^ 4))
    hdisj hmeas hB (by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hit : τ i ≤ T := (hτ hi').trans hn
      have hinc := hbound T (τ i) (T - τ i) tsub_le_self x (R / 2)
        (by positivity) (F i) (u8_grid_first_exit_past τ hτ x R i)
      rw [add_tsub_cancel_of_le hit] at hinc
      calc
        K x (F i) ≤ K x ((F i ∩ B) ∪
            (F i ∩ {γ | R / 2 ≤ euclideanNorm (γ T - γ (τ i))})) := by
          apply measure_mono
          intro γ hγ
          rcases u8_exit_terminal_or_increment x (γ (τ i)) (γ T) R hγ.1 with h | h
          · exact Or.inl ⟨hγ, h⟩
          · exact Or.inr ⟨hγ, h⟩
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hinc))
  have hU : (⋃ i ∈ Finset.range (n + 1), F i) =
      ⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)} := by
    rw [u8_grid_exit_eq_first_crossings]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    rfl
  rw [hU] at hs
  exact hs

#print axioms u8_regular_grid_exit_fourth_remainder

/-- Above the fourth-moment threshold, a finite-grid exit is controlled by the
terminal tail. -/
theorem u8_regular_grid_exit_fourth_absorbed
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ≥0) (τ : ℕ → ℝ≥0),
      Monotone τ → ∀ n, τ n ≤ T → ∀ (x : Vec d) (R : ℝ), 0 < R →
      C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / (R / 2) ^ 4 ≤ 1 / 2 →
      K x (⋃ k ≤ n, {γ | R ≤ euclideanNorm (γ (τ k) - x)}) ≤
        2 * K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} := by
  obtain ⟨C, hC, hbound⟩ :=
    u8_regular_grid_exit_fourth_remainder hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro T τ hτ n hn x R hR hq
  apply u8_ennreal_absorb_half _ _ _ (measure_ne_top _ _) (measure_ne_top _ _)
  · have hh := ENNReal.ofReal_le_ofReal hq
    simpa using hh
  · exact hbound T τ hτ n hn x R hR

#print axioms u8_regular_grid_exit_fourth_absorbed

/-- The absorbed first-exit estimate holds for any finite set of times. -/
theorem u8_regular_finite_exit_fourth_absorbed
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ≥0) (s : Finset ℝ≥0),
      (∀ t ∈ s, t ≤ T) → ∀ (x : Vec d) (R : ℝ), 0 < R →
      C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / (R / 2) ^ 4 ≤ 1 / 2 →
      K x (⋃ t ∈ s, {γ | R ≤ euclideanNorm (γ t - x)}) ≤
        2 * K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} := by
  obtain ⟨C, hC, hgrid⟩ :=
    u8_regular_grid_exit_fourth_absorbed hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro T s hs x R hR hq
  let a : Finset ℝ≥0 := insert 0 s
  have ha : 0 < a.card := Finset.card_pos.mpr ⟨0, by simp [a]⟩
  let τ : ℕ → ℝ≥0 := fun k =>
    a.orderEmbOfFin rfl ⟨min k (a.card - 1), by omega⟩
  have hτ : Monotone τ := by
    intro i j hij
    apply (a.orderEmbOfFin rfl).monotone
    exact min_le_min_right _ hij
  have hmem (k : ℕ) : τ k ∈ a := a.orderEmbOfFin_mem rfl _
  have hle : τ (a.card - 1) ≤ T := by
    have := hmem (a.card - 1)
    simp only [a, Finset.mem_insert] at this
    rcases this with h | h
    · rw [h]; exact bot_le
    · exact hs _ h
  have hsub : (⋃ t ∈ s, {γ : Path d | R ≤ euclideanNorm (γ t - x)}) ⊆
      (⋃ k ≤ a.card - 1, {γ : Path d | R ≤ euclideanNorm (γ (τ k) - x)}) := by
    intro γ hγ
    rcases Set.mem_iUnion.mp hγ with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨ht, hγ⟩
    have hta : t ∈ a := by simp [a, ht]
    have htr : t ∈ Set.range (a.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hta
    obtain ⟨i, hi⟩ := htr
    apply Set.mem_iUnion.mpr
    refine ⟨i.val, Set.mem_iUnion.mpr ⟨by omega, ?_⟩⟩
    have hti : τ i.val = t := by
      dsimp [τ]
      have hfin : (⟨min i.val (a.card - 1), by omega⟩ : Fin a.card) = i :=
        Fin.ext (min_eq_left (by omega))
      rw [hfin]
      exact hi
    simpa [hti] using hγ
  exact (measure_mono hsub).trans (hgrid T τ hτ (a.card - 1) hle x R hR hq)

#print axioms u8_regular_finite_exit_fourth_absorbed

/-- The absorbed estimate extends to countably many observation times. -/
theorem u8_regular_countable_exit_fourth_absorbed
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ≥0) {ι : Type} [Countable ι]
      (v : ι → ℝ≥0) (x : Vec d) (R : ℝ), 0 < R →
      C * ((T : ℝ) ^ 2 + (T : ℝ) ^ 4) / (R / 2) ^ 4 ≤ 1 / 2 →
      K x (⋃ i, ⋃ (_ : v i ≤ T), {γ | R ≤ euclideanNorm (γ (v i) - x)}) ≤
        2 * K x {γ | R / 2 ≤ euclideanNorm (γ T - x)} := by
  classical
  obtain ⟨C, hC, hfinite⟩ :=
    u8_regular_finite_exit_fourth_absorbed hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro T ι _ v x R hR hq
  let U : Finset ι → Set (Path d) := fun s =>
    ⋃ i ∈ s, ⋃ (_ : v i ≤ T), {γ | R ≤ euclideanNorm (γ (v i) - x)}
  have hU : Monotone U := by
    intro s t hst γ hγ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hγ ⊢
    obtain ⟨i, hi, hit, hγ⟩ := hγ
    exact ⟨i, hst hi, hit, hγ⟩
  have hcover : (⋃ i, ⋃ (_ : v i ≤ T),
      {γ : Path d | R ≤ euclideanNorm (γ (v i) - x)}) = ⋃ s, U s := by
    ext γ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hγ⟩
      exact ⟨{i}, i, by simp, hi, hγ⟩
    · rintro ⟨s, i, hi, hit, hγ⟩
      exact ⟨i, hit, hγ⟩
  rw [hcover, hU.directed_le.measure_iUnion]
  apply iSup_le
  intro s
  let a : Finset ℝ≥0 := (s.image v).filter (fun t => t ≤ T)
  have ha : ∀ t ∈ a, t ≤ T := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hsub : U s ⊆ ⋃ t ∈ a, {γ : Path d | R ≤ euclideanNorm (γ t - x)} := by
    intro γ hγ
    simp only [U, Set.mem_iUnion, Set.mem_ofPred_eq] at hγ ⊢
    obtain ⟨i, hi, hit, hγ⟩ := hγ
    refine ⟨v i, ?_, hγ⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, hit⟩
  exact (measure_mono hsub).trans (hfinite T a ha x R hR hq)

#print axioms u8_regular_countable_exit_fourth_absorbed

/-- A strict continuous-path exit inherits the absorbed countable-grid estimate. -/
theorem u8_regular_strict_exit_fourth_absorbed
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d) (R : ℝ), 0 < R →
      C * (((2 * t : ℝ≥0) : ℝ) ^ 2 + ((2 * t : ℝ≥0) : ℝ) ^ 4) / (R / 2) ^ 4 ≤ 1 / 2 →
      K x {γ | ∃ u : ℝ≥0, u ≤ t ∧ R < euclideanNorm (γ u - x)} ≤
        2 * K x {γ | R / 2 ≤ euclideanNorm (γ (2 * t) - x)} := by
  obtain ⟨C, hC, hcount⟩ :=
    u8_regular_countable_exit_fourth_absorbed hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro t ht x R hR hq
  let v : ℚ → ℝ≥0 := fun q => (q : ℝ).toNNReal
  have hv : DenseRange v := by
    have hs : Function.Surjective Real.toNNReal := by
      intro y
      exact ⟨(y : ℝ), by simp⟩
    exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal
  have hsub : {γ : Path d | ∃ u : ℝ≥0, u ≤ t ∧ R < euclideanNorm (γ u - x)} ⊆
      ⋃ q, ⋃ (_ : v q ≤ 2 * t),
        {γ : Path d | R ≤ euclideanNorm (γ (v q) - x)} := by
    intro γ hγ
    obtain ⟨u, hu, huR⟩ := hγ
    have hcont : Continuous (fun z : ℝ≥0 => euclideanNorm (γ z - x)) :=
      (Calculus.Feller.continuous_euclideanNorm d).comp (γ.continuous.sub continuous_const)
    let U : Set ℝ≥0 := Set.Iio (2 * t) ∩
      (fun z : ℝ≥0 => euclideanNorm (γ z - x)) ⁻¹' Set.Ioi R
    have hopen : IsOpen U := isOpen_Iio.inter (isOpen_Ioi.preimage hcont)
    have huT : u < 2 * t := by nlinarith
    have huU : u ∈ U := ⟨huT, huR⟩
    obtain ⟨q, hq⟩ := hv.exists_mem_open hopen ⟨u, huU⟩
    change v q < 2 * t ∧ R < euclideanNorm (γ (v q) - x) at hq
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hq.1.le, hq.2.le⟩⟩
  exact (measure_mono hsub).trans (hcount (2 * t) v x R hR hq)

#print axioms u8_regular_strict_exit_fourth_absorbed

/-- Integrating an absorbed tail bound costs the small-level cutoff and twice
the comparison moment. -/
theorem u8_lintegral_of_absorbed_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ a, 0 ≤ f a)
    (hg0 : ∀ a, 0 ≤ g a) (A : ℝ)
    (htail : ∀ z : ℝ, 0 < z → A < z →
      μ {a | z < f a} ≤ 2 * μ {a | z ≤ g a}) :
    (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≤
      ENNReal.ofReal A + 2 * (∫⁻ a, ENNReal.ofReal (g a) ∂μ) := by
  let b : ℝ → ℝ≥0∞ := (Set.Iic A).indicator (fun _ => 1)
  have hb : Measurable b := measurable_const.indicator measurableSet_Iic
  have hpoint : ∀ z ∈ Set.Ioi (0 : ℝ),
      μ {a | z < f a} ≤ b z + 2 * μ {a | z ≤ g a} := by
    intro z hz
    by_cases h : z ≤ A
    · have hm : μ {a | z < f a} ≤ 1 := by
        calc
          _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have : b z = 1 := by simp [b, h]
      rw [this]
      exact hm.trans (by simpa [add_comm] using
        (le_add_self : (1 : ℝ≥0∞) ≤ 2 * μ {a | z ≤ g a} + 1))
    · have hzA : A < z := lt_of_not_ge h
      have := htail z hz hzA
      simpa [b, h] using this
  rw [lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hf0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le μ (Filter.Eventually.of_forall hg0) hg.aemeasurable]
  calc
    _ ≤ ∫⁻ z in Set.Ioi (0 : ℝ), (b z + 2 * μ {a | z ≤ g a}) :=
      lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi hpoint)
    _ = (∫⁻ z in Set.Ioi (0 : ℝ), b z) +
        2 * (∫⁻ z in Set.Ioi (0 : ℝ), μ {a | z ≤ g a}) := by
      rw [lintegral_add_left hb, lintegral_const_mul' _ _ (by simp)]
    _ = _ := by
      congr 1
      rw [show (∫⁻ z in Set.Ioi (0 : ℝ), b z) =
          (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iic A) by
        simp [b, lintegral_indicator measurableSet_Iic]]
      rw [Measure.restrict_apply measurableSet_Iic]
      have hset : Set.Iic A ∩ Set.Ioi (0 : ℝ) = Set.Ioc 0 A := by
        ext z
        simp [and_comm]
      rw [hset, Real.volume_Ioc]
      simp

#print axioms u8_lintegral_of_absorbed_tail

/-- Fourth-power superlevel comparison for the continuous path maximum. -/
theorem u8_regular_path_fourth_level_absorbed
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d) (z : ℝ), 0 < z →
      32 * C * (((2 * t : ℝ≥0) : ℝ) ^ 2 + ((2 * t : ℝ≥0) : ℝ) ^ 4) < z →
      K x {γ | z < (⨆ u : Set.Icc (0 : ℝ≥0) t,
        euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4} ≤
        2 * K x {γ | z ≤ (2 * euclideanNorm (γ (2 * t) - x)) ^ 4} := by
  obtain ⟨C, hC, hexit⟩ :=
    u8_regular_strict_exit_fourth_absorbed hd ω lam Λ hΛ hω K hfdd
  refine ⟨C, hC, ?_⟩
  intro t ht x z hz hcut
  let R : ℝ := Real.sqrt (Real.sqrt z)
  have hR : 0 < R := Real.sqrt_pos.2 (Real.sqrt_pos.2 hz)
  have hR4 : R ^ 4 = z := by
    calc
      R ^ 4 = (R ^ 2) ^ 2 := by ring
      _ = (Real.sqrt z) ^ 2 := by rw [show R ^ 2 = Real.sqrt z from
        Real.sq_sqrt (Real.sqrt_nonneg z)]
      _ = z := Real.sq_sqrt hz.le
  have hq : C * (((2 * t : ℝ≥0) : ℝ) ^ 2 + ((2 * t : ℝ≥0) : ℝ) ^ 4) /
      (R / 2) ^ 4 ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (R / 2) ^ 4)).2
    have hpow : (R / 2) ^ 4 = z / 16 := by rw [div_pow, hR4]; norm_num
    rw [hpow]
    nlinarith
  have hsub : {γ : Path d | z < (⨆ u : Set.Icc (0 : ℝ≥0) t,
      euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4} ⊆
      {γ | ∃ u : ℝ≥0, u ≤ t ∧ R < euclideanNorm (γ u - x)} := by
    intro γ hγ
    have hcont : Continuous (fun u : ℝ≥0 => euclideanNorm (γ u - x)) :=
      (Calculus.Feller.continuous_euclideanNorm d).comp (γ.continuous.sub continuous_const)
    have hb : BddAbove (Set.range (fun u : Set.Icc (0 : ℝ≥0) t =>
        euclideanNorm (γ (u : ℝ≥0) - x))) := by
      have heq : Set.range (fun u : Set.Icc (0 : ℝ≥0) t =>
          euclideanNorm (γ (u : ℝ≥0) - x)) =
          (fun u : ℝ≥0 => euclideanNorm (γ u - x)) '' Set.Icc 0 t := by
        ext y
        constructor
        · rintro ⟨u, rfl⟩
          exact ⟨u, u.property, rfl⟩
        · rintro ⟨u, hu, rfl⟩
          exact ⟨⟨u, hu⟩, rfl⟩
      rw [heq]
      exact (isCompact_Icc.image hcont).bddAbove
    have hM0 : 0 ≤ ⨆ u : Set.Icc (0 : ℝ≥0) t,
        euclideanNorm (γ (u : ℝ≥0) - x) := by
      exact (show 0 ≤ euclideanNorm (γ 0 - x) from Real.sqrt_nonneg _).trans
        (le_ciSup hb ⟨0, bot_le, bot_le⟩)
    have hRM : R < ⨆ u : Set.Icc (0 : ℝ≥0) t,
        euclideanNorm (γ (u : ℝ≥0) - x) := by
      by_contra hn
      have hh := pow_le_pow_left₀ hM0 (le_of_not_gt hn) 4
      rw [hR4] at hh
      exact (not_lt_of_ge hh) hγ
    letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, bot_le, bot_le⟩⟩
    obtain ⟨u, hu⟩ := exists_lt_of_lt_ciSup hRM
    exact ⟨u, u.property.2, hu⟩
  have hterminal : {γ : Path d | R / 2 ≤ euclideanNorm (γ (2 * t) - x)} ⊆
      {γ | z ≤ (2 * euclideanNorm (γ (2 * t) - x)) ^ 4} := by
    intro γ hγ
    change R / 2 ≤ euclideanNorm (γ (2 * t) - x) at hγ
    rw [← hR4]
    apply pow_le_pow_left₀ hR.le
    linarith
  calc
    _ ≤ K x {γ | ∃ u : ℝ≥0, u ≤ t ∧ R < euclideanNorm (γ u - x)} := measure_mono hsub
    _ ≤ 2 * K x {γ | R / 2 ≤ euclideanNorm (γ (2 * t) - x)} :=
      hexit t ht x R hR hq
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono hterminal)

#print axioms u8_regular_path_fourth_level_absorbed

/-- Uniform fourth moment of the Euclidean physical-path supremum. -/
theorem u8_regular_signed_physical_path_sup_fourth_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal
        ((⨆ u : Set.Icc (0 : ℝ≥0) t, euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4) ∂K x) ≤
          ENNReal.ofReal (C * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := by
  obtain ⟨C₁, hC₁, hlevel⟩ :=
    u8_regular_path_fourth_level_absorbed hd ω lam Λ hΛ hω K hfdd
  obtain ⟨C₂, hC₂, hend⟩ :=
    u8_regular_signed_path_endpoint_fourth_moment hd ω lam Λ hΛ hω K hfdd
  refine ⟨512 * (C₁ + C₂), by positivity, ?_⟩
  intro t x
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · have hz : ∀ᵐ γ ∂K x,
        (⨆ u : Set.Icc (0 : ℝ≥0) 0, euclideanNorm (γ (u : ℝ≥0) - x)) = 0 := by
      filter_upwards [Blueprint.k11_starts_at
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd x] with γ hγ
      change γ 0 = x at hγ
      have hu (u : Set.Icc (0 : ℝ≥0) 0) : (u : ℝ≥0) = 0 :=
        le_antisymm u.property.2 bot_le
      simp only [hu, hγ, sub_self]
      simp [euclideanNorm, euclideanSq, dot]
    have he : (∫⁻ γ : Path d, ENNReal.ofReal
        ((⨆ u : Set.Icc (0 : ℝ≥0) 0, euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4) ∂K x) = 0 := by
      calc
        _ = ∫⁻ _ : Path d, (0 : ℝ≥0∞) ∂K x := by
          apply lintegral_congr_ae
          filter_upwards [hz] with γ hγ
          change ENNReal.ofReal ((⨆ u : Set.Icc (0 : ℝ≥0) 0,
            euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4) = 0
          rw [hγ]
          simp
        _ = 0 := by simp
    simpa using he.le
  · let f : Path d → ℝ := fun γ =>
      (⨆ u : Set.Icc (0 : ℝ≥0) t, euclideanNorm (γ (u : ℝ≥0) - x)) ^ 4
    let g : Path d → ℝ := fun γ => (2 * euclideanNorm (γ (2 * t) - x)) ^ 4
    let P : ℝ := (((2 * t : ℝ≥0) : ℝ) ^ 2 + ((2 * t : ℝ≥0) : ℝ) ^ 4)
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hf : Measurable f := (u8_continuous_euclidean_displacement_iSup x t).pow 4 |>.measurable
    have hg : Measurable g := by
      exact ((continuous_const.mul ((Calculus.Feller.continuous_euclideanNorm d).comp
        ((continuous_eval_const (2 * t)).sub continuous_const))).pow 4).measurable
    have hfg := u8_lintegral_of_absorbed_tail (K x) f g hf hg
      (fun γ => by dsimp [f]; positivity) (fun γ => by dsimp [g]; positivity)
      (32 * C₁ * P) (by
        intro z hz hcut
        exact hlevel t ht x z hz hcut)
    have hgint : (∫⁻ γ : Path d, ENNReal.ofReal (g γ) ∂K x) ≤
        16 * ENNReal.ofReal (C₂ * P) := by
      calc
        _ = 16 * (∫⁻ γ : Path d, ENNReal.ofReal
            (euclideanNorm (γ (2 * t) - x) ^ 4) ∂K x) := by
          dsimp [g]
          simp_rw [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
          norm_num only [ENNReal.ofReal_ofNat]
          rw [lintegral_const_mul' _ _ (by simp)]
        _ ≤ 16 * ENNReal.ofReal (C₂ * P) := by
          exact mul_le_mul' le_rfl (hend (2 * t) x)
    have htime : P ≤ 16 * ((t : ℝ) ^ 2 + (t : ℝ) ^ 4) := by
      dsimp [P]
      nlinarith [sq_nonneg (t : ℝ), pow_nonneg (show 0 ≤ (t : ℝ) by positivity) 4]
    calc
      _ ≤ ENNReal.ofReal (32 * C₁ * P) + 2 *
          (∫⁻ γ : Path d, ENNReal.ofReal (g γ) ∂K x) := hfg
      _ ≤ ENNReal.ofReal (32 * C₁ * P) +
          2 * (16 * ENNReal.ofReal (C₂ * P)) :=
            add_le_add le_rfl (mul_le_mul' le_rfl hgint)
      _ = ENNReal.ofReal ((32 * C₁ + 32 * C₂) * P) := by
        rw [show (2 : ℝ≥0∞) * (16 * ENNReal.ofReal (C₂ * P)) =
          ENNReal.ofReal (32 * C₂ * P) by
            rw [show (2 : ℝ≥0∞) * (16 * ENNReal.ofReal (C₂ * P)) =
              32 * ENNReal.ofReal (C₂ * P) by ring]
            rw [← ENNReal.ofReal_ofNat 32, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
            congr 1
            ring]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_left htime (show 0 ≤ 32 * C₁ + 32 * C₂ by positivity)
        nlinarith

#print axioms u8_regular_signed_physical_path_sup_fourth_moment

/-- A fourth-power superlevel comparison controls every positive natural power. -/
theorem u8_lintegral_pow_of_fourth_absorbed {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ a, 0 ≤ f a)
    (hg0 : ∀ a, 0 ≤ g a) (A : ℝ) (hA : 0 ≤ A)
    (htail : ∀ z : ℝ, 0 < z → A < z →
      μ {a | z < f a ^ 4} ≤ 2 * μ {a | z ≤ g a ^ 4})
    (k : ℕ) (hk : k ≠ 0) :
    (∫⁻ a, ENNReal.ofReal (f a ^ k) ∂μ) ≤
      ENNReal.ofReal ((A + 1) ^ k) +
        2 * (∫⁻ a, ENNReal.ofReal (g a ^ k) ∂μ) := by
  apply u8_lintegral_of_absorbed_tail μ (fun a => f a ^ k) (fun a => g a ^ k)
    (hf.pow_const k) (hg.pow_const k) (fun a => pow_nonneg (hf0 a) k)
    (fun a => pow_nonneg (hg0 a) k) ((A + 1) ^ k)
  intro z hz hcut
  let R : ℝ := z ^ ((k : ℝ)⁻¹)
  have hR : 0 < R := Real.rpow_pos_of_pos hz _
  have hRk : R ^ k = z := Real.rpow_inv_natCast_pow hz.le hk
  have hbig : A + 1 < R := by
    apply lt_of_pow_lt_pow_left₀ k hR.le
    simpa only [hRk] using hcut
  have hcut4 : A < R ^ 4 := by
    have hh : R ≤ R ^ 4 := le_self_pow₀ (by linarith) (by decide)
    linarith
  have hsub : {a | z < f a ^ k} ⊆ {a | R ^ 4 < f a ^ 4} := by
    intro a ha
    change z < f a ^ k at ha
    have hlt : R < f a := by
      apply lt_of_pow_lt_pow_left₀ k (hf0 a)
      simpa only [hRk] using ha
    exact pow_lt_pow_left₀ hlt hR.le (by decide)
  have hsub' : {a | R ^ 4 ≤ g a ^ 4} ⊆ {a | z ≤ g a ^ k} := by
    intro a ha
    have hle : R ≤ g a := le_of_pow_le_pow_left₀ (by decide : 4 ≠ 0) (hg0 a) ha
    rw [← hRk]
    exact pow_le_pow_left₀ hR.le hle k
  calc
    _ ≤ μ {a | R ^ 4 < f a ^ 4} := measure_mono hsub
    _ ≤ 2 * μ {a | R ^ 4 ≤ g a ^ 4} := htail (R ^ 4) (by positivity) hcut4
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono hsub')

#print axioms u8_lintegral_pow_of_fourth_absorbed

/-- The fourth-order exit scale is controlled by the diffusive-plus-drift scale. -/
theorem u8_time_scale_fourth (t : ℝ) (ht : 0 ≤ t) :
    (2 * t) ^ 2 + (2 * t) ^ 4 ≤ 16 * (Real.sqrt t + t) ^ 4 := by
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have hsq : t + t ^ 2 ≤ (Real.sqrt t + t) ^ 2 := by
    nlinarith [Real.sq_sqrt ht, mul_nonneg hs ht]
  have hp := pow_le_pow_left₀ (show 0 ≤ t + t ^ 2 by positivity) hsq 2
  nlinarith [sq_nonneg (t ^ 2)]

#print axioms u8_time_scale_fourth

/-- Scaling preserves an absorbed fourth-power tail comparison. -/
theorem u8_lintegral_scaled_pow_of_fourth_absorbed {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ a, 0 ≤ f a)
    (hg0 : ∀ a, 0 ≤ g a) (A S : ℝ) (hA : 0 ≤ A) (hS : 0 < S)
    (htail : ∀ z : ℝ, 0 < z → A * S ^ 4 < z →
      μ {a | z < f a ^ 4} ≤ 2 * μ {a | z ≤ g a ^ 4})
    (k : ℕ) (hk : k ≠ 0) :
    (∫⁻ a, ENNReal.ofReal ((f a / S) ^ k) ∂μ) ≤
      ENNReal.ofReal ((A + 1) ^ k) +
        2 * (∫⁻ a, ENNReal.ofReal ((g a / S) ^ k) ∂μ) := by
  apply u8_lintegral_pow_of_fourth_absorbed μ (fun a => f a / S) (fun a => g a / S)
    (hf.div_const S) (hg.div_const S) (fun a => div_nonneg (hf0 a) hS.le)
    (fun a => div_nonneg (hg0 a) hS.le) A hA
  · intro z hz hcut
    have h := htail (z * S ^ 4) (mul_pos hz (pow_pos hS 4))
      (mul_lt_mul_of_pos_right hcut (pow_pos hS 4))
    simpa only [div_pow, lt_div_iff₀ (pow_pos hS 4),
      le_div_iff₀ (pow_pos hS 4)] using h
  · exact hk

#print axioms u8_lintegral_scaled_pow_of_fourth_absorbed

/-- The normalized endpoint scale has the required diffusive and drift powers. -/
theorem u8_time_scale_even (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (Real.sqrt (2 * t) + 2 * t) ^ (2 * n) ≤
      (16 : ℝ) ^ n * (t ^ n + t ^ (2 * n)) := by
  have hs : 0 ≤ Real.sqrt (2 * t) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (2 * t) + 2 * t) ^ 2 ≤ 8 * (t + t ^ 2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * t by positivity),
      sq_nonneg (Real.sqrt (2 * t) - 2 * t)]
  have hp := pow_le_pow_left₀ (sq_nonneg (Real.sqrt (2 * t) + 2 * t)) hsq n
  have hadd : (t + t ^ 2) ^ n ≤ (2 : ℝ) ^ n * (t ^ n + (t ^ 2) ^ n) := by
    rcases le_total t (t ^ 2) with h | h
    · have hh : t + t ^ 2 ≤ 2 * t ^ 2 := by linarith
      have hp' := pow_le_pow_left₀ (show 0 ≤ t + t ^ 2 by positivity) hh n
      rw [mul_pow] at hp'
      have hpos : 0 ≤ (2 : ℝ) ^ n := by positivity
      have htpos : 0 ≤ t ^ n := by positivity
      nlinarith
    · have hh : t + t ^ 2 ≤ 2 * t := by linarith
      have hp' := pow_le_pow_left₀ (show 0 ≤ t + t ^ 2 by positivity) hh n
      rw [mul_pow] at hp'
      have hpos : 0 ≤ (2 : ℝ) ^ n := by positivity
      have htpos : 0 ≤ (t ^ 2) ^ n := by positivity
      nlinarith
  rw [mul_pow] at hp
  have h := mul_le_mul_of_nonneg_left hadd (show 0 ≤ (8 : ℝ) ^ n by positivity)
  rw [← mul_assoc, ← mul_pow (8 : ℝ) 2 n] at h
  rw [show (8 : ℝ) * 2 = 16 by norm_num, ← pow_mul] at h
  rw [← pow_mul] at hp
  exact hp.trans h

#print axioms u8_time_scale_even

/-- Normalized maximal moments are controlled by normalized endpoint moments. -/
theorem u8_regular_signed_path_scaled_sup_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t : ℝ≥0), 0 < t → ∀ (x : Vec d) (k : ℕ), k ≠ 0 →
      (∫⁻ γ : Path d, ENNReal.ofReal
        (((⨆ u : Set.Icc (0 : ℝ≥0) t, euclideanNorm (γ (u : ℝ≥0) - x)) /
          (Real.sqrt ((2 * t : ℝ≥0) : ℝ) + ((2 * t : ℝ≥0) : ℝ))) ^ k) ∂K x) ≤
      ENNReal.ofReal ((A + 1) ^ k) + 2 * (∫⁻ γ : Path d, ENNReal.ofReal
        ((2 * euclideanNorm (γ (2 * t) - x) /
          (Real.sqrt ((2 * t : ℝ≥0) : ℝ) + ((2 * t : ℝ≥0) : ℝ))) ^ k) ∂K x) := by
  obtain ⟨C, hC, hlevel⟩ :=
    u8_regular_path_fourth_level_absorbed hd ω lam Λ hΛ hω K hfdd
  refine ⟨32 * C, by positivity, ?_⟩
  intro t ht x k hk
  let T : ℝ := ((2 * t : ℝ≥0) : ℝ)
  let S : ℝ := Real.sqrt T + T
  let f : Path d → ℝ := fun γ => ⨆ u : Set.Icc (0 : ℝ≥0) t,
    euclideanNorm (γ (u : ℝ≥0) - x)
  let g : Path d → ℝ := fun γ => 2 * euclideanNorm (γ (2 * t) - x)
  have hT : 0 < T := by dsimp [T]; exact_mod_cast (mul_pos (by norm_num : (0 : ℝ≥0) < 2) ht)
  have hS : 0 < S := by dsimp [S]; positivity
  have hf : Measurable f := (u8_continuous_euclidean_displacement_iSup x t).measurable
  have hg : Measurable g := (continuous_const.mul ((Calculus.Feller.continuous_euclideanNorm d).comp
    ((continuous_eval_const (2 * t)).sub continuous_const))).measurable
  have hf0 : ∀ γ, 0 ≤ f γ := by
    intro γ
    dsimp [f]
    exact Real.iSup_nonneg (fun u => Real.sqrt_nonneg _)
  have hg0 : ∀ γ, 0 ≤ g γ := by intro γ; dsimp [g, euclideanNorm]; positivity
  have hsq : T + T ^ 2 ≤ S ^ 2 := by
    dsimp [S]
    nlinarith [Real.sq_sqrt hT.le, mul_nonneg (Real.sqrt_nonneg T) hT.le]
  have hp := pow_le_pow_left₀ (show 0 ≤ T + T ^ 2 by positivity) hsq 2
  have hP : T ^ 2 + T ^ 4 ≤ S ^ 4 := by nlinarith [sq_nonneg (T ^ 2)]
  apply u8_lintegral_scaled_pow_of_fourth_absorbed (K x) f g hf hg hf0 hg0
    (32 * C) S (by positivity) hS ?_ k hk
  intro z hz hcut
  apply hlevel t ht x z hz
  have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 32 * C by positivity)
  change 32 * C * (T ^ 2 + T ^ 4) < z
  exact lt_of_le_of_lt hh hcut

#print axioms u8_regular_signed_path_scaled_sup_moment

theorem u8_regular_signed_physical_path_sup_even_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∀ n : ℕ, 1 ≤ n → ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ γ : Path d, ENNReal.ofReal
        ((⨆ u : Set.Icc (0 : ℝ≥0) t, euclideanNorm (γ (u : ℝ≥0) - x)) ^ (2*n)) ∂K x) ≤
          ENNReal.ofReal (C * ((t : ℝ) ^ n + (t : ℝ) ^ (2*n))) := by
  obtain ⟨A, hA, hsup⟩ := u8_regular_signed_path_scaled_sup_moment hd ω lam Λ hΛ hω K hfdd
  intro n hn
  have hk : 2 * n ≠ 0 := by omega
  obtain ⟨D, hD, hend⟩ := u8_regular_signed_path_endpoint_scaled_moment hd ω lam Λ hΛ hω K hfdd (2*n)
  let B : ℝ := (A + 1) ^ (2*n) + 2 * (2 ^ (2*n) * D)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * 16 ^ n, by positivity, ?_⟩
  intro t x
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · have hz : ∀ᵐ γ ∂K x,
        (⨆ u : Set.Icc (0 : ℝ≥0) 0, euclideanNorm (γ (u : ℝ≥0) - x)) = 0 := by
      filter_upwards [Blueprint.k11_starts_at
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) K hfdd x] with γ hγ
      change γ 0 = x at hγ
      have hu (u : Set.Icc (0 : ℝ≥0) 0) : (u : ℝ≥0) = 0 :=
        le_antisymm u.property.2 bot_le
      simp only [hu, hγ, sub_self]
      simp [euclideanNorm, euclideanSq, dot]
    have he : (∫⁻ γ : Path d, ENNReal.ofReal
        ((⨆ u : Set.Icc (0 : ℝ≥0) 0, euclideanNorm (γ (u : ℝ≥0) - x)) ^ (2*n)) ∂K x) = 0 := by
      calc
        _ = ∫⁻ _ : Path d, (0 : ℝ≥0∞) ∂K x := by
          apply lintegral_congr_ae
          filter_upwards [hz] with γ hγ
          rw [hγ]
          simp [hk]
        _ = 0 := by simp
    simpa [Nat.ne_of_gt hn, hk] using he.le
  · let S : ℝ := Real.sqrt ((2 * t : ℝ≥0) : ℝ) + ((2 * t : ℝ≥0) : ℝ)
    let f : Path d → ℝ := fun γ => ⨆ u : Set.Icc (0 : ℝ≥0) t,
      euclideanNorm (γ (u : ℝ≥0) - x)
    have ht2 : (0 : ℝ≥0) < 2 * t := mul_pos (by norm_num) ht
    have hS : 0 < S := by
      dsimp [S]
      exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by exact_mod_cast ht2)
    have hend' : (∫⁻ γ : Path d, ENNReal.ofReal
        ((2 * euclideanNorm (γ (2*t) - x) / S) ^ (2*n)) ∂K x) ≤
        ENNReal.ofReal (2 ^ (2*n) * D) := by
      calc
        _ = ENNReal.ofReal ((2 : ℝ) ^ (2*n)) * (∫⁻ γ : Path d, ENNReal.ofReal
            ((euclideanNorm (γ (2*t) - x) / S) ^ (2*n)) ∂K x) := by
          simp_rw [show ∀ a : ℝ, 2 * a / S = 2 * (a / S) by intro a; ring,
            mul_pow, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (2*n))]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (2*n)) * ENNReal.ofReal D :=
          mul_le_mul' le_rfl (hend (2*t) ht2 x)
        _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
    have hnorm : (∫⁻ γ : Path d, ENNReal.ofReal ((f γ / S) ^ (2*n)) ∂K x) ≤
        ENNReal.ofReal B := by
      calc
        _ ≤ ENNReal.ofReal ((A + 1) ^ (2*n)) + 2 *
          (∫⁻ γ : Path d, ENNReal.ofReal
            ((2 * euclideanNorm (γ (2*t) - x) / S) ^ (2*n)) ∂K x) := hsup t ht x (2*n) hk
        _ ≤ ENNReal.ofReal ((A + 1) ^ (2*n)) + 2 * ENNReal.ofReal (2 ^ (2*n) * D) :=
          add_le_add le_rfl (mul_le_mul' le_rfl hend')
        _ = ENNReal.ofReal B := by
          dsimp [B]
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have htime : S ^ (2*n) ≤ (16 : ℝ) ^ n * ((t : ℝ) ^ n + (t : ℝ) ^ (2*n)) := by
      simpa [S] using u8_time_scale_even (t : ℝ) (by positivity) n
    calc
      _ = ENNReal.ofReal (S ^ (2*n)) * (∫⁻ γ : Path d, ENNReal.ofReal
          ((f γ / S) ^ (2*n)) ∂K x) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro γ
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← mul_pow]
        congr 1
        field_simp
        rfl
      _ ≤ ENNReal.ofReal (S ^ (2*n)) * ENNReal.ofReal B :=
        mul_le_mul' le_rfl hnorm
      _ = ENNReal.ofReal (B * S ^ (2*n)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h := mul_le_mul_of_nonneg_left htime hB.le
        nlinarith

#print axioms u8_regular_signed_physical_path_sup_even_moment

end EinsteinFull
