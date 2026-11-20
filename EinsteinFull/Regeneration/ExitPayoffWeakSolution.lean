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

end EinsteinFull.Regeneration
