import EinsteinFull.Regeneration.ExitPayoffGreen
import EinsteinFull.Blueprint.G1.Proofs.SbxS8StoppedLocality

/-!
# Exit payoffs as weak solutions

The zero-boundary variational resolvents of a bounded observable are Cauchy in the
weighted Sobolev graph norm as the rate vanishes, because their values converge to the
expected undiscounted occupation before the exit. The limit is an element of the
zero-boundary domain solving the undiscounted weak equation. Combined with Dynkin's
formula at the exit time, the exit payoff of a smooth compactly supported payoff is the
payoff plus this limit, and it solves the homogeneous weak equation inside the set.
-/

open MeasureTheory ProbabilityTheory Filter Set EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The zero-boundary resolvent equation in inner-product form. -/
theorem zeroBoundaryResolvent_inner (U : Set (Vec d)) (hd : 2 ≤ d) (ω : FieldPair d)
    (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (v : physicalH1ZeroBoundary U hd lam) :
    α * ⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f (Lp.memLp f)).1,
      EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v.1⟫_ℝ +
      EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f (Lp.memLp f)).1 v.1 =
      ⟪f, EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v.1⟫_ℝ := by
  set u := physicalZeroBoundaryResolvent U hd ω lam L α hL hω hα f (Lp.memLp f)
  have hs := (physicalZeroBoundaryResolvent_spec U hd ω lam L α hL hω hα f (Lp.memLp f)).2 v
  have hmass : (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
      ∂physicalReversibleMeasure ω hd lam) =
      ⟪physicalZeroBoundaryValue U hd ω lam L hω u,
        physicalZeroBoundaryValue U hd ω lam L hω v⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u,
      physicalZeroBoundaryValue_ae_eq U hd ω lam L hω v] with x hu hv
    rw [hu, hv]
    simp only [RCLike.inner_apply', conj_trivial]
  have hforce : (∫ x, f x * densityWeightedH1SpaceValue v.1 x
      ∂physicalReversibleMeasure ω hd lam) =
      ⟪f, physicalZeroBoundaryValue U hd ω lam L hω v⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalZeroBoundaryValue_ae_eq U hd ω lam L hω v] with x hv
    rw [hv]
    simp only [RCLike.inner_apply', conj_trivial]
  rw [hmass, hforce, ← EinsteinFull.Blueprint.sbxS8_physicalH1Energy_eq_integral hd ω lam L hω,
    EinsteinFull.Blueprint.sbxS8_physicalZeroBoundaryValue_eq U hd ω lam L hω u,
    EinsteinFull.Blueprint.sbxS8_physicalZeroBoundaryValue_eq U hd ω lam L hω v] at hs
  exact hs

/-- The physical energy is bounded as a bilinear form. -/
theorem abs_gmpPhysicalH1Energy_le (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L)
    (hω : IsRegular L ω) (u v : EinsteinFull.Blueprint.GMPForceH1 hd lam) :
    |EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u v| ≤
      (Real.exp (2 * L) * (1 + L / 2) + Real.exp L * Real.exp L) * ‖u‖ * ‖v‖ := by
  have hb := sourcePhysicalResolventForm_bounded hd ω lam L 1 hL hω zero_lt_one u v
  rw [← EinsteinFull.Blueprint.gmpPhysicalH1Energy_eq_source hd ω lam L hω u v, one_mul] at hb
  have hi : |⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u,
      EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v⟫_ℝ| ≤
      Real.exp L * Real.exp L * ‖u‖ * ‖v‖ := by
    calc _ ≤ ‖EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u‖ *
          ‖EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v‖ := abs_real_inner_le_norm _ _
      _ ≤ (Real.exp L * ‖u‖) * (Real.exp L * ‖v‖) :=
          mul_le_mul (EinsteinFull.Blueprint.gmpPhysicalH1Value_norm_le hd ω lam L hω u)
            (EinsteinFull.Blueprint.gmpPhysicalH1Value_norm_le hd ω lam L hω v) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hb' : |⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u,
      EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v⟫_ℝ +
      EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u v| ≤
      Real.exp (2 * L) * (1 + L / 2) * ‖u‖ * ‖v‖ := hb
  calc |EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u v|
      = |(⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u,
          EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v⟫_ℝ +
          EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u v) -
          ⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u,
            EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v⟫_ℝ| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ Real.exp (2 * L) * (1 + L / 2) * ‖u‖ * ‖v‖ + Real.exp L * Real.exp L * ‖u‖ * ‖v‖ :=
        add_le_add hb' hi
    _ = _ := by ring

/-- The physical energy is subtractive in its first argument. -/
theorem gmpPhysicalH1Energy_sub_left (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hL : 1 ≤ L)
    (hω : IsRegular L ω) (u v w : EinsteinFull.Blueprint.GMPForceH1 hd lam) :
    EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω (u - v) w =
      EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u w -
        EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω v w := by
  rw [sub_eq_add_neg, EinsteinFull.Blueprint.gmpPhysicalH1Energy_add_left hd ω lam L hL hω,
    ← neg_one_smul ℝ v, EinsteinFull.Blueprint.gmpPhysicalH1Energy_smul_left]
  ring

/-- A path that exits immediately has no occupation. -/
theorem discountedOccupation_eq_zero_of_exitTime_eq_zero (U : Set (Vec d)) (g : Vec d → ℝ)
    (α : ℝ) (γ : Path d) (h : MarkovProcess.ContinuousPath.exitTime U γ = 0) :
    discountedOccupation U g α γ = 0 := by
  unfold discountedOccupation
  have hempty : {s : ℝ | (s.toNNReal : ℝ≥0∞) < MarkovProcess.ContinuousPath.exitTime U γ} = ∅ := by
    ext s
    simp [h]
  rw [hempty]
  simp

variable {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
  {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}

/-- The expected discounted occupation before the exit, as a function of the start. -/
noncomputable def occupationExpectation
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (g : Vec d → ℝ) (α : ℝ) (x : Vec d) : ℝ :=
  ∫ γ, discountedOccupation U g α γ ∂G.pathLaw x

theorem measurable_occupationExpectation
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g) (α : ℝ) :
    Measurable (occupationExpectation G U g α) :=
  ((measurable_discountedOccupation U hU g hg α).stronglyMeasurable.integral_kernel
    (κ := G.pathLaw)).measurable

theorem occupationExpectation_eq_zero_of_notMem
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (g : Vec d → ℝ) (α : ℝ) (x : Vec d) (hx : x ∉ U) :
    occupationExpectation G U g α x = 0 := by
  unfold occupationExpectation
  apply integral_eq_zero_of_ae
  filter_upwards [G.pathLaw_starts_at x] with γ hγ
  change γ 0 = x at hγ
  apply discountedOccupation_eq_zero_of_exitTime_eq_zero
  have hle := MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ 0 (by rw [hγ]; exact hx)
  simpa using hle

theorem abs_occupationExpectation_le
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (g : Vec d → ℝ) (B : ℝ) (hB : ∀ y, |g y| ≤ B) (α : ℝ) (hα : 0 ≤ α)
    (x : Vec d)
    (hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) (M : ℝ)
    (hM : ∫ γ, (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x ≤ M) :
    |occupationExpectation G U g α x| ≤ B * M := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  unfold occupationExpectation
  calc |∫ γ, discountedOccupation U g α γ ∂G.pathLaw x|
      ≤ ∫ γ, |discountedOccupation U g α γ| ∂G.pathLaw x := abs_integral_le_integral_abs
    _ ≤ ∫ γ, B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun γ => abs_nonneg _)
          (hτ.const_mul B)
        filter_upwards [hfin] with γ hγ
        exact abs_discountedOccupation_le U g B hB α hα γ hγ
    _ = B * ∫ γ, (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x :=
        integral_const_mul _ _
    _ ≤ B * M := mul_le_mul_of_nonneg_left hM hB0

theorem tendsto_occupationExpectation
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ)
    (hB : ∀ y, |g y| ≤ B) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n) (hα0 : Tendsto α atTop (𝓝 0))
    (x : Vec d)
    (hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) :
    Tendsto (fun n => occupationExpectation G U g (α n) x) atTop
      (𝓝 (occupationExpectation G U g 0 x)) := by
  unfold occupationExpectation
  apply tendsto_integral_of_dominated_convergence
    (fun γ => B * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
  · exact fun n => (measurable_discountedOccupation U hU g hg (α n)).aestronglyMeasurable
  · exact hτ.const_mul B
  · intro n
    filter_upwards [hfin] with γ hγ
    rw [Real.norm_eq_abs]
    exact abs_discountedOccupation_le U g B hB (α n) (hα n) γ hγ
  · filter_upwards [hfin] with γ hγ
    exact tendsto_discountedOccupation U g hg B hB α hα hα0 γ hγ

/-- As the rate vanishes, the values of the zero-boundary resolvents of a bounded
observable converge in the physical L² space to the expected occupation before the exit. -/
theorem tendsto_zeroBoundaryResolvent_value
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (hUm : physicalReversibleMeasure ω hd lam U ≠ ⊤)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, |g y| ≤ B)
    (hgL : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) (M : ℝ)
    (hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x ≤ M)
    (α : ℕ → ℝ) (hαpos : ∀ n, 0 < α n) (hα0 : Tendsto α atTop (𝓝 0)) :
    ∃ W0L : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (W0L : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] occupationExpectation G U g 0 ∧
      Tendsto (fun n => EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n)
          (hgL.toLp g : Vec d → ℝ) (Lp.memLp (hgL.toLp g))).1) atTop (𝓝 W0L) := by
  let m := physicalReversibleMeasure ω hd lam
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := by
    have : IsProbabilityMeasure (G.pathLaw 0) := G.pathLaw_isMarkovKernel.isProbabilityMeasure 0
    exact (integral_nonneg fun γ => ENNReal.toReal_nonneg).trans (hM 0)
  let gL := hgL.toLp g
  let W : ℝ → Vec d → ℝ := fun a => occupationExpectation G U g a
  have hWm : ∀ a, Measurable (W a) := fun a => measurable_occupationExpectation G U hU g hg a
  have hWb : ∀ a, 0 ≤ a → ∀ x, |W a x| ≤ B * M := fun a ha x =>
    abs_occupationExpectation_le G U g B hB a ha x (hfin x) (hτ x) M (hM x)
  have hWz : ∀ a x, x ∉ U → W a x = 0 := fun a x hx =>
    occupationExpectation_eq_zero_of_notMem G U g a x hx
  have hind : MemLp (U.indicator (fun _ => B * M)) 2 m :=
    memLp_indicator_const 2 hU.measurableSet (B * M) (Or.inr hUm)
  have hW0mem : MemLp (W 0) 2 m := by
    refine hind.of_le (hWm 0).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hB0 hM0)]
      exact hWb 0 le_rfl x
    · rw [Set.indicator_of_notMem hx, hWz 0 x hx]
  refine ⟨hW0mem.toLp (W 0), hW0mem.coeFn_toLp, ?_⟩
  have hval : ∀ n, (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n)
        (gL : Vec d → ℝ) (Lp.memLp gL)).1 : Vec d → ℝ) =ᵐ[m] W (α n) := by
    intro n
    rw [← EinsteinFull.Blueprint.sbxS8_physicalZeroBoundaryValue_eq,
      ← EinsteinFull.s1_supplied_killed_Laplace_eq_zeroBoundaryResolvent hd L hL ω hω lam h₀ h₁
        G U hU (α n) (hαpos n) gL]
    exact killedLaplace_ae_eq_discountedOccupation G U hU g hg B hB hgL (α n) (hαpos n)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun n => ‖EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
      (physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n)
        (gL : Vec d → ℝ) (Lp.memLp gL)).1 - hW0mem.toLp (W 0)‖ ^ 2) atTop (𝓝 0) := by
    have hnorm : ∀ n, ‖EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n)
          (gL : Vec d → ℝ) (Lp.memLp gL)).1 - hW0mem.toLp (W 0)‖ ^ 2 =
        ∫ x, (W (α n) x - W 0 x) ^ 2 ∂m := by
      intro n
      rw [l2_norm_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω
        (physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n)
          (gL : Vec d → ℝ) (Lp.memLp gL)).1) (hW0mem.toLp (W 0)), hval n,
        hW0mem.coeFn_toLp] with x hx h1 h2
      rw [hx, Pi.sub_apply, h1, h2, Real.norm_eq_abs, sq_abs]
    simp only [hnorm]
    have hbound : Integrable (U.indicator (fun _ => (2 * B * M) ^ 2)) m :=
      (integrable_indicator_iff hU.measurableSet).mpr
        (integrableOn_const (μ := m) (s := U) (C := (2 * B * M) ^ 2) (hs := hUm.lt_top.ne))
    have hlim0 := tendsto_integral_of_dominated_convergence
      (U.indicator (fun _ => (2 * B * M) ^ 2))
      (F := fun n x => (W (α n) x - W 0 x) ^ 2) (f := fun _ => (0 : ℝ))
      (fun n => (((hWm (α n)).sub (hWm 0)).pow_const 2).aestronglyMeasurable) hbound
      (fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ U
        · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have h1 := hWb (α n) (hαpos n).le x
          have h2 := hWb 0 le_rfl x
          have h3 : |W (α n) x - W 0 x| ≤ 2 * B * M := by
            calc |W (α n) x - W 0 x| ≤ |W (α n) x| + |W 0 x| := abs_sub _ _
              _ ≤ B * M + B * M := add_le_add h1 h2
              _ = 2 * B * M := by ring
          calc (W (α n) x - W 0 x) ^ 2 = |W (α n) x - W 0 x| ^ 2 := (sq_abs _).symm
            _ ≤ (2 * B * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
        · rw [Set.indicator_of_notMem hx, hWz _ x hx, hWz 0 x hx]
          simp)
      (Eventually.of_forall fun x => by
        have h := tendsto_occupationExpectation G U hU g hg B hB α (fun n => (hαpos n).le) hα0 x
          (hfin x) (hτ x)
        have h2 := (h.sub (tendsto_const_nhds (x := W 0 x))).pow 2
        have h0 : (occupationExpectation G U g 0 x - W 0 x) ^ 2 = 0 := by
          simp [W]
        rw [h0] at h2
        exact h2)
    simpa using hlim0
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- A sequence controlled by a multiple of a null sequence converges. -/
theorem tendsto_of_abs_sub_le_mul (f r : ℕ → ℝ) (a C K : ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ n, |f n - a| ≤ C * r n * K) : Tendsto f atTop (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 := (hr.const_mul C).mul_const K
  rw [mul_zero, zero_mul] at h2
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact h n) h2

/-- A vanishing multiple of a convergent sequence does not change a constant limit. -/
theorem tendsto_const_sub_mul (b l : ℝ) (α ip : ℕ → ℝ) (hα0 : Tendsto α atTop (𝓝 0))
    (hip : Tendsto ip atTop (𝓝 l)) : Tendsto (fun n => b - α n * ip n) atTop (𝓝 b) := by
  have h3 := (tendsto_const_nhds (x := b)).sub (hα0.mul hip)
  rw [zero_mul, sub_zero] at h3
  exact h3

/-- A sequence whose squared increments are controlled by null sequences is Cauchy. -/
theorem cauchySeq_of_sq_dist_le {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (a α : ℕ → ℝ)
    (c K : ℝ) (hc : 0 < c) (hK : 0 < K) (ha0 : Tendsto a atTop (𝓝 0))
    (hα0 : Tendsto α atTop (𝓝 0)) (hα : ∀ n, 0 ≤ α n) (ha : ∀ n, 0 ≤ a n)
    (hkey : ∀ n k, a n ≤ 1 → a k ≤ 1 →
      c * dist (u n) (u k) ^ 2 ≤ K * (a n + α n + a k + α k) ^ 2) :
    CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ : ℝ := Real.sqrt (c / K) * ε / 2
  have hδ : 0 < δ := by
    have : 0 < Real.sqrt (c / K) := Real.sqrt_pos.mpr (div_pos hc hK)
    positivity
  have hb : Tendsto (fun j => a j + α j) atTop (𝓝 0) := by simpa using ha0.add hα0
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds hδ))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (ha0.eventually (ge_mem_nhds zero_lt_one))
  refine ⟨max N₁ N₂, fun n hn k hk => ?_⟩
  have hn₁ := hN₁ n ((le_max_left _ _).trans hn)
  have hk₁ := hN₁ k ((le_max_left _ _).trans hk)
  have hbound := hkey n k (hN₂ n ((le_max_right _ _).trans hn))
    (hN₂ k ((le_max_right _ _).trans hk))
  have hsum : a n + α n + a k + α k < 2 * δ := by linarith
  have hsum0 : 0 ≤ a n + α n + a k + α k := by
    linarith [ha n, ha k, hα n, hα k]
  have hδsq : K * (2 * δ) ^ 2 = c * ε ^ 2 := by
    simp only [δ]
    rw [show (2 * (Real.sqrt (c / K) * ε / 2)) ^ 2 = Real.sqrt (c / K) ^ 2 * ε ^ 2 by ring,
      Real.sq_sqrt (div_pos hc hK).le]
    field_simp
  have hlt : c * dist (u n) (u k) ^ 2 < c * ε ^ 2 := by
    calc c * dist (u n) (u k) ^ 2 ≤ K * (a n + α n + a k + α k) ^ 2 := hbound
      _ < K * (2 * δ) ^ 2 := by
          apply mul_lt_mul_of_pos_left _ hK
          exact pow_lt_pow_left₀ hsum hsum0 (by norm_num)
      _ = c * ε ^ 2 := hδsq
  have hlt' : dist (u n) (u k) ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left hlt hc.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt'

set_option maxHeartbeats 400000 in
/-- The zero-boundary resolvents of a bounded observable converge, as the rate vanishes,
to an element of the zero-boundary domain whose value is the expected occupation before
the exit and which solves the undiscounted weak equation with the observable as source. -/
theorem exists_zeroBoundary_occupation_solution
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (hUm : physicalReversibleMeasure ω hd lam U ≠ ⊤)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, |g y| ≤ B)
    (hgL : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) (M : ℝ)
    (hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x ≤ M) :
    ∃ v : physicalH1ZeroBoundary U hd lam,
      (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v.1 : Vec d → ℝ)
        =ᵐ[physicalReversibleMeasure ω hd lam] occupationExpectation G U g 0 ∧
      ∀ w : physicalH1ZeroBoundary U hd lam,
        EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω v.1 w.1 =
          ⟪hgL.toLp g, EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω w.1⟫_ℝ := by
  let gL := hgL.toLp g
  let α : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hαpos : ∀ n, 0 < α n := fun n => by positivity
  have hα0 : Tendsto α atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hα1 : ∀ n, α n ≤ 1 := fun n => by
    simp only [α]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨W0L, hW0L, hconv⟩ := tendsto_zeroBoundaryResolvent_value G U hU hUm g hg B hB hgL
    hfin hτ M hM α hαpos hα0
  let u : ℕ → physicalH1ZeroBoundary U hd lam := fun n =>
    physicalZeroBoundaryResolvent U hd ω lam L (α n) hL hω (hαpos n) (gL : Vec d → ℝ)
      (Lp.memLp gL)
  let V := EinsteinFull.Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω lam L hω
  have hV : ∀ z, V z = EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω z := fun z => rfl
  let E := EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω
  have heq : ∀ n (v : physicalH1ZeroBoundary U hd lam),
      α n * ⟪V (u n).1, V v.1⟫_ℝ + E (u n).1 v.1 = ⟪gL, V v.1⟫_ℝ := fun n v =>
    zeroBoundaryResolvent_inner U hd ω lam L (α n) hL hω (hαpos n) gL v
  have hconv' : Tendsto (fun n => V (u n).1) atTop (𝓝 W0L) := hconv
  have hEbound : ∀ x y : physicalH1ZeroBoundary U hd lam, |E x.1 y.1| ≤
      (Real.exp (2 * L) * (1 + L / 2) + Real.exp L * Real.exp L) *
        ‖(x.1 : PhysicalH1Space hd lam)‖ * ‖(y.1 : PhysicalH1Space hd lam)‖ := fun x y =>
    abs_gmpPhysicalH1Energy_le hd ω lam L hL hω x.1 y.1
  have hEsub : ∀ x y z : physicalH1ZeroBoundary U hd lam,
      E (x - y).1 z.1 = E x.1 z.1 - E y.1 z.1 := fun x y z => by
    have h : (x - y).1 = x.1 - y.1 := rfl
    rw [h]
    exact gmpPhysicalH1Energy_sub_left hd ω lam L hL hω _ _ _
  clear_value u
  let c := Real.exp (-2 * L) * min 1 ((1 / 2 : ℝ) * L⁻¹)
  have hc : 0 < c := sourcePhysicalResolvent_coercivity_constant_pos L 1 hL zero_lt_one
  let a : ℕ → ℝ := fun n => ‖V (u n).1 - W0L‖
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.mp hconv'
  let K : ℝ := 2 + ‖W0L‖
  have hK : 0 < K := by positivity
  have hkey : ∀ n k, a n ≤ 1 → a k ≤ 1 →
      c * ‖u n - u k‖ ^ 2 ≤ K * (a n + α n + a k + α k) ^ 2 := by
    intro n k han hak
    set w := u n - u k with hw
    have hw1 : w.1 = (u n).1 - (u k).1 := rfl
    have hEw : E w.1 w.1 = α k * ⟪V (u k).1, V w.1⟫_ℝ - α n * ⟪V (u n).1, V w.1⟫_ℝ := by
      have h1 := heq n w
      have h2 := heq k w
      have hsub : E w.1 w.1 = E (u n).1 w.1 - E (u k).1 w.1 := hEsub (u n) (u k) w
      linarith
    have hVw : V w.1 = V (u n).1 - V (u k).1 := by
      rw [hw1]
      exact V.map_sub _ _
    have hnVw : ‖V w.1‖ ≤ a n + a k := by
      rw [hVw]
      calc ‖V (u n).1 - V (u k).1‖ = ‖(V (u n).1 - W0L) - (V (u k).1 - W0L)‖ := by
            congr 1; abel
        _ ≤ ‖V (u n).1 - W0L‖ + ‖V (u k).1 - W0L‖ := norm_sub_le _ _
    have hnV : ∀ j, ‖V (u j).1‖ ≤ ‖W0L‖ + a j := fun j => by
      calc ‖V (u j).1‖ = ‖W0L + (V (u j).1 - W0L)‖ := by congr 1; abel
        _ ≤ ‖W0L‖ + ‖V (u j).1 - W0L‖ := norm_add_le _ _
    have hcoer := EinsteinFull.Blueprint.gmpPhysicalH1Energy_coercive hd ω lam L hL hω w.1
    have hnorm : ‖w‖ = ‖(w.1 : PhysicalH1Space hd lam)‖ := rfl
    have hi1 : α k * ⟪V (u k).1, V w.1⟫_ℝ ≤ α k * ((‖W0L‖ + 1) * (a n + a k)) := by
      apply mul_le_mul_of_nonneg_left _ (hαpos k).le
      calc ⟪V (u k).1, V w.1⟫_ℝ ≤ ‖V (u k).1‖ * ‖V w.1‖ := real_inner_le_norm _ _
        _ ≤ (‖W0L‖ + 1) * (a n + a k) := mul_le_mul (by linarith [hnV k]) hnVw
            (norm_nonneg _) (by positivity)
    have hi2 : -(α n * ⟪V (u n).1, V w.1⟫_ℝ) ≤ α n * ((‖W0L‖ + 1) * (a n + a k)) := by
      rw [← mul_neg]
      apply mul_le_mul_of_nonneg_left _ (hαpos n).le
      calc -⟪V (u n).1, V w.1⟫_ℝ ≤ |⟪V (u n).1, V w.1⟫_ℝ| := neg_le_abs _
        _ ≤ ‖V (u n).1‖ * ‖V w.1‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖W0L‖ + 1) * (a n + a k) := mul_le_mul (by linarith [hnV n]) hnVw
            (norm_nonneg _) (by positivity)
    have ha_n : 0 ≤ a n := norm_nonneg _
    have ha_k : 0 ≤ a k := norm_nonneg _
    have hsq : ‖V w.1‖ ^ 2 ≤ (a n + a k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnVw 2
    rw [hnorm]
    calc c * ‖(w.1 : PhysicalH1Space hd lam)‖ ^ 2
        ≤ ‖V w.1‖ ^ 2 + E w.1 w.1 := hcoer
      _ ≤ (a n + a k) ^ 2 + (α k + α n) * ((‖W0L‖ + 1) * (a n + a k)) := by
          rw [hEw]; nlinarith
      _ ≤ K * (a n + α n + a k + α k) ^ 2 := by
          have hαn := (hαpos n).le
          have hαk := (hαpos k).le
          nlinarith [sq_nonneg (a n + a k), sq_nonneg (α n + α k), norm_nonneg W0L,
            mul_nonneg (add_nonneg hαn hαk) (add_nonneg ha_n ha_k)]
  have hcauchy : CauchySeq u :=
    cauchySeq_of_sq_dist_le u a α c K hc hK ha0 hα0 (fun n => (hαpos n).le)
      (fun n => norm_nonneg _) (fun n k han hak => by
        rw [dist_eq_norm]
        exact hkey n k han hak)
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hv1 : Tendsto (fun n => (u n).1) atTop (𝓝 v.1) :=
    (continuous_subtype_val.tendsto v).comp hv
  have hVv : Tendsto (fun n => V (u n).1) atTop (𝓝 (V v.1)) :=
    (V.continuous.tendsto v.1).comp hv1
  have hVeq : V v.1 = W0L := tendsto_nhds_unique hVv hconv'
  refine ⟨v, ?_, ?_⟩
  · have hVeq' : EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v.1 = W0L := hVeq
    exact (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => (f : Vec d → ℝ)) hVeq')).trans hW0L
  · intro w
    have hsub : ∀ n, E (u n - v).1 w.1 = E (u n).1 w.1 - E v.1 w.1 := fun n => hEsub (u n) v w
    have hr : Tendsto (fun n => ‖((u n - v).1 : PhysicalH1Space hd lam)‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.mp hv).congr fun n => rfl
    have hbound : ∀ n, |E (u n).1 w.1 - E v.1 w.1| ≤
        (Real.exp (2 * L) * (1 + L / 2) + Real.exp L * Real.exp L) *
          ‖((u n - v).1 : PhysicalH1Space hd lam)‖ * ‖(w.1 : PhysicalH1Space hd lam)‖ := by
      intro n
      have h := hEbound (u n - v) w
      rw [hsub n] at h
      exact h
    have hlim1 : Tendsto (fun n => E (u n).1 w.1) atTop (𝓝 (E v.1 w.1)) :=
      tendsto_of_abs_sub_le_mul (fun n => E (u n).1 w.1)
        (fun n => ‖((u n - v).1 : PhysicalH1Space hd lam)‖) (E v.1 w.1)
        (Real.exp (2 * L) * (1 + L / 2) + Real.exp L * Real.exp L)
        ‖(w.1 : PhysicalH1Space hd lam)‖ hr hbound
    have hform : ∀ n, E (u n).1 w.1 = ⟪gL, V w.1⟫_ℝ - α n * ⟪V (u n).1, V w.1⟫_ℝ := fun n =>
      eq_sub_of_add_eq' (heq n w)
    have hlim2 : Tendsto (fun n => E (u n).1 w.1) atTop (𝓝 ⟪gL, V w.1⟫_ℝ) :=
      (tendsto_const_sub_mul ⟪gL, V w.1⟫_ℝ ⟪V v.1, V w.1⟫_ℝ α (fun n => ⟪V (u n).1, V w.1⟫_ℝ)
        hα0 (hVv.inner tendsto_const_nhds)).congr fun n => (hform n).symm
    exact tendsto_nhds_unique hlim1 hlim2

/-- The exit payoff of a smooth compactly supported payoff from an open set of finite
physical measure with uniformly integrable exit time is the payoff plus a zero-boundary
element, and it solves the homogeneous weak equation against every zero-boundary test. -/
theorem exists_exitPayoff_weak_solution
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (U : Set (Vec d)) (hU : IsOpen U) (hUm : physicalReversibleMeasure ω hd lam U ≠ ⊤)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hfin : ∀ x, ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤)
    (hτ : ∀ x, Integrable (fun γ => (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
      (G.pathLaw x)) (M : ℝ)
    (hM : ∀ x, ∫ γ, (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x ≤ M) :
    ∃ u : EinsteinFull.Blueprint.GMPForceH1 hd lam,
      u - EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hφc ∈
        physicalH1ZeroBoundary U hd lam ∧
      (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω u : Vec d → ℝ)
        =ᵐ[physicalReversibleMeasure ω hd lam] exitPayoff G U φ ∧
      ∀ w : physicalH1ZeroBoundary U hd lam,
        EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω u w.1 = 0 := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam φ
  have hgm : Measurable g := measurable_physicalGenerator _ ω lam φ
  obtain ⟨B, -, hB⟩ := EinsteinFull.sbxS4_physicalGenerator_bounded hd
    (firstCoordinateIndex hd) hL0 hω lam hφ hφc
  have hgL : MemLp g 2 (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd) hL0 hω lam hφ hφc
  obtain ⟨v, hv, hveq⟩ :=
    exists_zeroBoundary_occupation_solution G U hU hUm g hgm B hB hgL hfin hτ M hM
  let φ' := EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hφc
  let v' : EinsteinFull.Blueprint.GMPForceH1 hd lam := v.1
  refine ⟨φ' + v', ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact v.2
  · have hsum : EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω (φ' + v') =
        EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω φ' +
          EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v' :=
      map_add (EinsteinFull.Blueprint.gmpPhysicalH1ValueContinuousLinear hd ω lam L hω) φ' v'
    have hadd : (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω (φ' + v') :
        Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω φ' : Vec d → ℝ) +
          (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v' : Vec d → ℝ) := by
      rw [hsum]
      exact Lp.coeFn_add _ _
    have hφv := EinsteinFull.Blueprint.gmpPhysicalCompactTest_value_ae hd ω lam L hω φ hφ hφc
    filter_upwards [hadd, hφv, hv] with x h1 h2 h3
    have h3' : (EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω v' : Vec d → ℝ) x =
        occupationExpectation G U g 0 x := h3
    rw [h1, Pi.add_apply, h2, h3']
    have hD := exitPayoff_sub_eq_integral_generator G U hU φ hφ hφc x (hfin x) (hτ x)
    have hO : occupationExpectation G U g 0 x =
        ∫ γ, (∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal,
          g (γ s.toNNReal)) ∂G.pathLaw x := by
      unfold occupationExpectation
      apply integral_congr_ae
      filter_upwards [hfin x] with γ hγ
      exact discountedOccupation_zero U g γ hγ
    rw [hO]
    change φ x + ∫ γ, (∫ s in (0 : ℝ)..(MarkovProcess.ContinuousPath.exitTime U γ).toReal,
      physicalGenerator (firstCoordinateIndex hd) ω lam φ (γ s.toNNReal)) ∂G.pathLaw x = _
    rw [← hD]
    ring
  · intro w
    have hadd := EinsteinFull.Blueprint.gmpPhysicalH1Energy_add_left hd ω lam L hL hω φ' v' w.1
    have h2 : EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω v' w.1 =
        ⟪hgL.toLp g, EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω w.1⟫_ℝ := hveq w
    have h1 : EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω φ' w.1 =
        -⟪hgL.toLp g, EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω w.1⟫_ℝ := by
      have hs := EinsteinFull.Blueprint.gmpPhysicalH1Energy_symm hd ω lam L hω φ' w.1
      have he := EinsteinFull.Blueprint.gmpPhysicalH1Energy_eq_source hd ω lam L hω w.1 φ'
      have hg := EinsteinFull.sbxS4_compactTest_fullDomain_generatorInner hd L ω hω lam hL0 w.1
        φ hφ hφc
      have hi : ⟪EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω w.1, hgL.toLp g⟫_ℝ =
          ⟪hgL.toLp g, EinsteinFull.Blueprint.gmpPhysicalH1Value hd ω lam L hω w.1⟫_ℝ :=
        real_inner_comm _ _
      exact hs.trans (he.trans (hg.trans (congrArg Neg.neg hi)))
    calc EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω (φ' + v') w.1
        = EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω φ' w.1 +
          EinsteinFull.Blueprint.gmpPhysicalH1Energy hd ω lam L hω v' w.1 := hadd
      _ = 0 := by rw [h1, h2]; ring

end EinsteinFull.Regeneration
