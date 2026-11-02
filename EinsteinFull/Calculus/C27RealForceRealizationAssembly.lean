import EinsteinFull.Calculus.C27RealForceRealization
import EinsteinFull.Calculus.C16SourceExponentialMaxAssembly
import EinsteinFull.Calculus.C2SourceWeightedDynkinFinal

open MeasureTheory Filter Topology
open scoped NNReal BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The generator of a dilated cutoff times a coordinate exponential, minus the potential term,
vanishes inside the cutoff region and is uniformly controlled by the exponential. -/
theorem c27_cutoff_exp_generator {d : ℕ} {a : Vec d → Mat d} {b : Vec d → Vec d} {A B : ℝ}
    (hA : ∀ y i j, |a y i j| ≤ A) (hB : ∀ y i, |b y i| ≤ B) (i0 : Fin d) (lam : ℝ)
    (x0 : Vec d) {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (h1 : ∀ y : Vec d, ‖y‖ ≤ 1 → χ y = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (y : Vec d),
      (‖y‖ < (k : ℝ) + 1 →
        External.Draft.svGenerator a b (fun z => χ (((k : ℝ) + 1)⁻¹ • z) *
            Real.exp (lam * (z i0 - x0 i0))) y -
          (lam * b y i0 + lam ^ 2 / 2 * a y i0 i0) *
            (χ (((k : ℝ) + 1)⁻¹ • y) * Real.exp (lam * (y i0 - x0 i0))) = 0) ∧
      |External.Draft.svGenerator a b (fun z => χ (((k : ℝ) + 1)⁻¹ • z) *
            Real.exp (lam * (z i0 - x0 i0))) y -
          (lam * b y i0 + lam ^ 2 / 2 * a y i0 i0) *
            (χ (((k : ℝ) + 1)⁻¹ • y) * Real.exp (lam * (y i0 - x0 i0)))| ≤
        C * Real.exp (lam * (y i0 - x0 i0)) := by
  obtain ⟨M, hM0, hM⟩ := c27_cutoff_derivative_bounds hχ hc
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 i0 i0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 i0)
  refine ⟨(1 / 2 : ℝ) * ((d : ℝ) * ((d : ℝ) * (A * (M + 2 * |lam| * M)))) +
    (d : ℝ) * (B * M), by positivity, fun k y => ?_⟩
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set c : ℝ := ((k : ℝ) + 1)⁻¹ with hcdef
  have hc0 : 0 < c := inv_pos.mpr hk0
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hu : ContDiff ℝ 2 (fun z : Vec d => χ (c • z)) :=
    (hχ.comp (contDiff_const_smul c)).of_le (WithTop.coe_le_coe.2 le_top)
  have hgen := c27_svGenerator_mul_exp a b i0 lam x0 hu y
  constructor
  · intro hy
    have hcy : ‖c • y‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0, hcdef, inv_mul_lt_iff₀ hk0]
      linarith
    rw [hgen]
    have hz1 : ∀ j : Fin d, fderiv ℝ (fun z => χ (c • z)) y (unitVector j) = 0 := fun j =>
      (c27_cutoff_derivatives_zero h1 c y hcy j j).1
    have hz2 : ∀ i j : Fin d, fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z
        (unitVector j)) y (unitVector i) = 0 := fun i j =>
      (c27_cutoff_derivatives_zero h1 c y hcy i j).2
    simp [hz1, hz2]
  · rw [hgen, add_sub_cancel_right, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hd1 : ∀ j, |fderiv ℝ (fun z => χ (c • z)) y (unitVector j)| ≤ M := fun j => (hM c hc0 hc1 y j j).1
    have hd2 : ∀ i j, |fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) y
        (unitVector i)| ≤ M := fun i j => (hM c hc0 hc1 y i j).2
    have hδ : ∀ i : Fin d, |(if i = i0 then (1 : ℝ) else 0)| ≤ 1 := fun i => by
      split_ifs <;> simp
    have hterm : ∀ i j, |a y i j * (fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z
          (unitVector j)) y (unitVector i) +
        lam * (if i = i0 then 1 else 0) * fderiv ℝ (fun z => χ (c • z)) y (unitVector j) +
        lam * (if j = i0 then 1 else 0) * fderiv ℝ (fun z => χ (c • z)) y (unitVector i))| ≤
        A * (M + 2 * |lam| * M) := fun i j => by
      rw [abs_mul]
      have e1 : |lam * (if i = i0 then (1 : ℝ) else 0) * fderiv ℝ (fun z => χ (c • z)) y
          (unitVector j)| ≤ |lam| * M := by
        rw [abs_mul, abs_mul]
        calc |lam| * |(if i = i0 then (1 : ℝ) else 0)| * _ ≤ |lam| * 1 * M :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hδ i) (abs_nonneg _)) (hd1 j)
                (abs_nonneg _) (by positivity)
          _ = _ := by ring
      have e2 : |lam * (if j = i0 then (1 : ℝ) else 0) * fderiv ℝ (fun z => χ (c • z)) y
          (unitVector i)| ≤ |lam| * M := by
        rw [abs_mul, abs_mul]
        calc |lam| * |(if j = i0 then (1 : ℝ) else 0)| * _ ≤ |lam| * 1 * M :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hδ j) (abs_nonneg _)) (hd1 i)
                (abs_nonneg _) (by positivity)
          _ = _ := by ring
      have := abs_add_three (fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z (unitVector j)) y
        (unitVector i)) (lam * (if i = i0 then (1 : ℝ) else 0) * fderiv ℝ (fun z => χ (c • z)) y
          (unitVector j)) (lam * (if j = i0 then (1 : ℝ) else 0) * fderiv ℝ (fun z => χ (c • z)) y
          (unitVector i))
      exact mul_le_mul (hA y i j) (by linarith [hd2 i j]) (abs_nonneg _) hA0
    have hsum : |∑ i, ∑ j, a y i j * (fderiv ℝ (fun z => fderiv ℝ (fun z => χ (c • z)) z
          (unitVector j)) y (unitVector i) +
        lam * (if i = i0 then 1 else 0) * fderiv ℝ (fun z => χ (c • z)) y (unitVector j) +
        lam * (if j = i0 then 1 else 0) * fderiv ℝ (fun z => χ (c • z)) y (unitVector i))| ≤
        (d : ℝ) * ((d : ℝ) * (A * (M + 2 * |lam| * M))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => hterm i j))|>.trans ?_
      simp
    have hb : |∑ i, b y i * fderiv ℝ (fun z => χ (c • z)) y (unitVector i)| ≤
        (d : ℝ) * (B * M) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => B * M) fun i _ => ?_).trans ?_
      · rw [abs_mul]; exact mul_le_mul (hB y i) (hd1 i) (abs_nonneg _) hB0
      · simp
    refine (abs_add_le _ _).trans (add_le_add ?_ hb)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- A bounded coordinate exponential along a path on `[0,T]` is dominated by the exponential of
the running maximum. -/
theorem c27_exp_coord_le_max {d : ℕ} (i : Fin d) (lam : ℝ) (x : Vec d) (γ : Path d)
    (T s : ℝ≥0) (hs : s ≤ T) :
    Real.exp (lam * ((γ s) i - x i)) ≤ Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) := by
  have hc : Continuous (fun t : ℝ≥0 => |(γ t) i - x i|) :=
    (((continuous_apply i).comp γ.continuous).sub continuous_const).abs
  have h : |(γ s) i - x i| ≤ sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) :=
    le_csSup (isCompact_Icc.bddAbove_image hc.continuousOn) ⟨s, ⟨zero_le, hs⟩, rfl⟩
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _))

/-- A path is bounded in norm on `[0,T]`. -/
theorem c27_path_norm_bounded {d : ℕ} (γ : Path d) (T : ℝ≥0) :
    ∃ R : ℝ, ∀ s : ℝ≥0, s ≤ T → ‖γ s‖ < R := by
  obtain ⟨R, hR⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).image γ.continuous).isBounded.exists_norm_le
  exact ⟨R + 1, fun s hs => by
    have := hR (γ s) ⟨s, ⟨zero_le, hs⟩, rfl⟩
    linarith⟩

/-- Dominated convergence for a double integral over a finite time interval. -/
theorem c27_double_integral_tendsto_zero {α : Type*} [MeasurableSpace α] {P : Measure α}
    {T : ℝ≥0} {H : ℕ → ℝ → α → ℝ} {G : α → ℝ}
    (hHm : ∀ k, Measurable (fun p : ℝ × α => H k p.1 p.2))
    (hbound : ∀ k γ, ∀ u ∈ Set.Ioc (0 : ℝ) (T : ℝ), ‖H k u γ‖ ≤ G γ)
    (hG : Integrable G P)
    (hzero : ∀ γ, ∀ u ∈ Set.Ioc (0 : ℝ) (T : ℝ), ∀ᶠ k in atTop, H k u γ = 0) :
    Tendsto (fun k : ℕ => ∫ γ, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ), H k u γ) ∂P) atTop (𝓝 0) := by
  have hfinite : volume (Set.Ioc (0 : ℝ) (T : ℝ)) < ⊤ := by simp
  have hinner : ∀ γ, Tendsto (fun k : ℕ => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), H k u γ) atTop
      (𝓝 0) := by
    intro γ
    have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict
      (Set.Ioc (0 : ℝ) (T : ℝ))) (fun _ => G γ) (F := fun k u => H k u γ) (f := fun _ => 0)
      (fun k => ((hHm k).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (by simp)
      (fun k => (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun u hu => hbound k γ u hu))
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu =>
        tendsto_const_nhds.congr' ((hzero γ u hu).mono fun k hk => hk.symm)))
    simpa using hlim
  have hlim := tendsto_integral_of_dominated_convergence (μ := P) (fun γ => (T : ℝ) * G γ)
    (F := fun k γ => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ), H k u γ) (f := fun _ => 0)
    (fun k => (StronglyMeasurable.integral_prod_left
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) (f := fun u γ => H k u γ)
      (hHm k).stronglyMeasurable).aestronglyMeasurable)
    (hG.const_mul (T : ℝ))
    (fun k => Filter.Eventually.of_forall fun γ => by
      have h := norm_setIntegral_le_of_norm_le_const (C := G γ) hfinite
        (fun u hu => hbound k γ u hu)
      rw [Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero] at h
      rwa [mul_comm] at h)
    (Filter.Eventually.of_forall hinner)
  simpa using hlim

/-- The cutoff error terms in the weighted Dynkin identity vanish in the limit. -/
theorem c27_cutoff_remainder_tendsto {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : ℝ≥0)
    {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (h1 : ∀ y : Vec d, ‖y‖ ≤ 1 → χ y = 1) :
    let V : Vec d → ℝ := fun y => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
    let f : ℕ → Vec d → ℝ := fun k z => χ (((k : ℝ) + 1)⁻¹ • z) *
      Real.exp (lam * (z i - x i))
    Tendsto (fun k : ℕ => ∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), V (γ v.toNNReal))) *
        (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) (f k) (γ u.toNNReal) -
            V (γ u.toNNReal) * f k (γ u.toNNReal))) ∂P) atTop (𝓝 0) := by
  intro V f
  obtain ⟨hcont, _, ⟨A, hA⟩, _, hm, ⟨B, hB⟩⟩ := reduced_svHypotheses hΛ hω i 0
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨Bw, hBw0, hBw⟩ := c2_path_weight_horizon_bound hK T
  obtain ⟨C, hC0, hC⟩ := c27_cutoff_exp_generator hA hB i lam x hχ hcs h1
  have hmax := c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP |lam| T
  have hfk : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (f k) ∧ HasCompactSupport (f k) := fun k => by
    refine ⟨(hχ.comp (contDiff_const_smul _)).mul ?_, ?_⟩
    · exact Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
    · exact (hcs.comp_homeomorph (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹)
        (inv_ne_zero (by positivity)))).mul_right
  have hGm : ∀ k : ℕ, Measurable (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) i 0) (f k)) := fun k =>
    (c2_reduced_generator_measurable_bounded hΛ hω i (hfk k).1 (hfk k).2).1
  have heval : Measurable (fun p : ℝ × Path d => p.2 p.1.toNNReal) :=
    (continuous_snd.eval (continuous_real_toNNReal.comp continuous_fst)).measurable
  have hWj := c2_path_weight_joint_measurable hVm hK
  refine c27_double_integral_tendsto_zero (P := P) (T := T) (G := fun γ : Path d =>
    Bw * (C * Real.exp (|lam| * sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))))
    (H := fun k u γ => Real.exp (-(∫ v in Set.Ioc (0 : ℝ) (u.toNNReal : ℝ), V (γ v.toNNReal))) *
        (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i 0) (f k) (γ u.toNNReal) -
            V (γ u.toNNReal) * f k (γ u.toNNReal))) ?_ ?_ ((hmax.const_mul C).const_mul Bw) ?_
  · exact fun k => hWj.mul (((hGm k).comp heval).sub ((hVm.comp heval).mul
      ((hfk k).1.continuous.measurable.comp heval)))
  · intro k γ u hu
    have huT : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hu.2
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hBw u.toNNReal huT γ) ?_ (abs_nonneg _) hBw0
    refine ((hC k (γ u.toNNReal)).2).trans ?_
    exact mul_le_mul_of_nonneg_left (c27_exp_coord_le_max i lam x γ T _ huT) hC0
  · intro γ u hu
    obtain ⟨R, hR⟩ := c27_path_norm_bounded γ T
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
    have := (hC k (γ u.toNNReal)).1 (by
      have := hR u.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hu.2)
      linarith)
    simp only [V, f] at this ⊢
    rw [this, mul_zero]

/-- The actual signed exponential path weight is integrable and normalized. -/
theorem c27_reduced_force_exponential_weight_integral {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i 0)) x P) (T : ℝ≥0) :
    let Z : Path d → ℝ := fun γ => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Integrable Z P ∧ (∫ γ, Z γ ∂P) = 1 := by
  intro Z
  letI : IsProbabilityMeasure P := hP.1
  have hmax := c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP |lam| T
  have hZ : Integrable Z P :=
    c27_reduced_force_weight_integrable_of_max hΛ hω i lam x T P hmax
  refine ⟨hZ, ?_⟩
  obtain ⟨χ, hχ, hcs, h1, h01⟩ := c27_exists_cutoff d
  have hrem := c27_cutoff_remainder_tendsto hd hΛ hω i lam hP T hχ hcs h1
  obtain ⟨hVm, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  have hfk : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => χ (((k : ℝ) + 1)⁻¹ • z) *
      Real.exp (lam * (z i - x i))) ∧
      HasCompactSupport (fun z : Vec d => χ (((k : ℝ) + 1)⁻¹ • z) *
        Real.exp (lam * (z i - x i))) := fun k => by
    refine ⟨(hχ.comp (contDiff_const_smul _)).mul ?_, ?_⟩
    · exact Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
    · exact (hcs.comp_homeomorph (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹)
        (inv_ne_zero (by positivity)))).mul_right
  have hdyn := fun k : ℕ => c2_reduced_force_weighted_dynkin hΛ hω i lam hP _ (hfk k).1
    (hfk k).2 T
  have hZeq : ∀ γ : Path d, Z γ = Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) *
      Real.exp (lam * ((γ T) i - x i)) := fun γ => by
    simp only [Z]; rw [← Real.exp_add]; congr 1; ring
  have hWm := (c25_reduced_force_path_weight_measurable hΛ hω i lam T).1
  have hT1 : Tendsto (fun k : ℕ => ∫ γ, Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) *
      (χ (((k : ℝ) + 1)⁻¹ • γ T) * Real.exp (lam * ((γ T) i - x i))) ∂P) atTop
      (𝓝 (∫ γ, Z γ ∂P)) := by
    refine tendsto_integral_of_dominated_convergence Z (fun k => ?_) hZ (fun k => ?_) ?_
    · exact (hWm.mul (((hfk k).1.continuous.measurable).comp
        (continuous_eval_const T).measurable)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun γ => ?_
      have hχk := h01 (((k : ℝ) + 1)⁻¹ • γ T)
      have key : ∀ w g c : ℝ, 0 < w → 0 < g → 0 ≤ c → c ≤ 1 → ‖w * (c * g)‖ ≤ w * g :=
        fun w g c hw hg hc0 hc1 => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [mul_pos hw hg]
      rw [hZeq γ]
      exact key _ _ _ (Real.exp_pos _) (Real.exp_pos _) hχk.1 hχk.2
    · refine Filter.Eventually.of_forall fun γ => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖γ T‖
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop N] with k hk
      have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
      have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hnorm : ‖((k : ℝ) + 1)⁻¹ • γ T‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), inv_mul_le_iff₀ hk0]
        linarith
      rw [h1 _ hnorm, one_mul, hZeq γ]
  have hT2 : Tendsto (fun k : ℕ => χ (((k : ℝ) + 1)⁻¹ • x) * Real.exp (lam * (x i - x i)))
      atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr hk
    have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hnorm : ‖((k : ℝ) + 1)⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), inv_mul_le_iff₀ hk0]
      linarith
    rw [h1 _ hnorm]; simp
  have hT3 := hT1.sub hT2
  have hT4 : Tendsto (fun k : ℕ => (∫ γ, Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) *
      (χ (((k : ℝ) + 1)⁻¹ • γ T) * Real.exp (lam * ((γ T) i - x i))) ∂P) -
      χ (((k : ℝ) + 1)⁻¹ • x) * Real.exp (lam * (x i - x i))) atTop (𝓝 0) := by
    refine hrem.congr fun k => ?_
    exact (hdyn k).symm
  have := tendsto_nhds_unique hT3 hT4
  linarith

end EinsteinFull
