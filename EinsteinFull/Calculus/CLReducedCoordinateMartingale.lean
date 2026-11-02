import EinsteinFull.Calculus.S4MartingaleSllnSupport
import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import EinsteinFull.Calculus.C6ResponseVelocityCesaro

/-!
# The coordinate martingale of the reduced diffusion

On a smooth regular environment every solution of the reduced martingale problem from the origin
makes each compensated coordinate `γ_t^j - ∫₀ᵗ b^j(γ_u) du` a martingale, although a coordinate
is not a compactly supported test. The compensated cutoff tests converge to it in L¹: they agree
with it on every path that stays in the cutoff ball, and their second moments are uniformly
bounded.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- For every `c > 0`, `|z| ≤ z² / (2c) + (c / 2) 1_{z ≠ 0}`. -/
theorem abs_le_sq_div_add_indicator (z : ℝ) {c : ℝ} (hc : 0 < c) :
    |z| ≤ z ^ 2 / (2 * c) + c / 2 * (if z = 0 then 0 else 1) := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, mul_one]
    have h : 0 ≤ (|z| - c) ^ 2 / (2 * c) := div_nonneg (sq_nonneg _) (by positivity)
    have e : (|z| - c) ^ 2 / (2 * c) = z ^ 2 / (2 * c) + c / 2 - |z| := by
      field_simp
      rw [sub_sq, sq_abs]
      ring
    linarith

/-- On a smooth regular environment each compensated coordinate is a martingale under every
solution of the reduced martingale problem from the origin. -/
theorem reduced_coordinate_martingale {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    (j : Fin d) :
    Martingale (compensatedTest (reducedGenerator i ω lam) (fun y => y j))
      (pathFiltration d) P := by
  have : IsProbabilityMeasure P := hP.1
  let f : Vec d → ℝ := fun y => y j
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_apply ℝ ℝ j
  have hG0 : ∀ y k, |fderiv ℝ f y (unitVector k)| ≤ 1 := by
    intro y k
    rw [(hasFDerivAt_apply j y).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    by_cases h : j = k <;> simp [unitVector, h]
  have hgrow : ∀ y, |f y| ≤ 0 + 1 * ‖y‖ := fun y => by
    simpa only [zero_add, one_mul, Real.norm_eq_abs] using norm_le_pi_norm y j
  obtain ⟨χ, B, hχ, hχ1, hχ0, hB⟩ :=
    reduced_cutoff_bound hΛ hω hs i lam hf hG0 hgrow le_rfl zero_le_one
  obtain ⟨B', _, hB'⟩ := response_coordinate_second_moment hΛ hω hs i lam hP j
  let F : ℕ → Vec d → ℝ := fun k => cutoffFn χ ((k : ℝ) + 1) f
  have hk0 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hFd : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (F k) := fun k => contDiff_cutoffFn hχ hf _
  have hFc : ∀ k, HasCompactSupport (F k) := fun k => hasCompactSupport_cutoffFn f (hk0 k) hχ0
  have hLc : Continuous (reducedGenerator i ω lam f) :=
    continuous_reducedGenerator_apply hs i lam hf
  have hMc (t : ℝ≥0) : Continuous (compensatedTest (reducedGenerator i ω lam) f t) :=
    continuous_compensatedTest_path hf.continuous hLc t
  have hMkc (k : ℕ) (t : ℝ≥0) :
      Continuous (compensatedTest (reducedGenerator i ω lam) (F k) t) :=
    continuous_compensatedTest_path (hFd k).continuous
      (continuous_reducedGenerator_apply hs i lam (hFd k)) t
  -- uniform second moments of the cutoff tests
  have hsqk (k : ℕ) (t : ℝ≥0) :
      Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2) P ∧
      ∫ γ, compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 ∂P ≤ B * t := by
    obtain ⟨K, hK⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam (hFd k) (hFc k)
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun z => F k z ^ 2) := (hFd k).pow 2
    have hsqc : HasCompactSupport (fun z => F k z ^ 2) :=
      (hFc k).comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    obtain ⟨K2, hK2⟩ := bounded_reducedGenerator_apply hΛ hω hs i lam hsq hsqc
    obtain ⟨C, hC⟩ := (hFd k).continuous.bounded_above_of_compact_support (hFc k)
    exact ⟨integrable_sq_compensatedTest (hFd k).continuous
        (fun y => by have := hC y; rwa [Real.norm_eq_abs] at this)
        (continuous_reducedGenerator_apply hs i lam (hFd k)) hK t,
      integral_sq_compensatedTest_le hP (hFd k) (hFc k) hK
        (continuous_reducedGenerator_apply hs i lam (hFd k)) hK2
        (continuous_reducedGenerator_apply hs i lam hsq)
        (fun y => hB _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) y) t⟩
  -- every path stays in the cutoff ball eventually
  have hev (t : ℝ≥0) (γ : Path d) : ∀ᶠ k : ℕ in atTop,
      compensatedTest (reducedGenerator i ω lam) (F k) t γ =
        compensatedTest (reducedGenerator i ω lam) f t γ := by
    obtain ⟨R0, hR0⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).image
      γ.continuous).isBounded.exists_norm_le
    obtain ⟨N, hN⟩ := exists_nat_gt R0
    filter_upwards [eventually_ge_atTop N] with k hk
    have hR : R0 < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := Nat.cast_le.2 hk
      linarith
    have hball : ∀ u : ℝ≥0, u ≤ t → ‖γ u‖ < (k : ℝ) + 1 := fun u hu =>
      lt_of_le_of_lt (hR0 _ ⟨u, ⟨bot_le, hu⟩, rfl⟩) hR
    have e1 : F k (γ t) = f (γ t) := cutoffFn_eq f (hk0 k) hχ1 (hball t le_rfl).le
    have e0 : F k (γ 0) = f (γ 0) := cutoffFn_eq f (hk0 k) hχ1 (hball 0 bot_le).le
    unfold compensatedTest
    rw [e1, e0]
    congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le t.coe_nonneg] at hu
    have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact reducedGenerator_congr_nhds hs i lam (hFd k) hf
      (cutoffFn_eventuallyEq f (hk0 k) hχ1 (hball _ hut))
  -- L¹ convergence of the cutoff tests
  have hL1 (t : ℝ≥0) : Tendsto (fun k : ℕ => ∫ γ,
      |compensatedTest (reducedGenerator i ω lam) (F k) t γ -
        compensatedTest (reducedGenerator i ω lam) f t γ| ∂P) atTop (𝓝 0) := by
    let Z : ℕ → Path d → ℝ := fun k γ =>
      compensatedTest (reducedGenerator i ω lam) (F k) t γ -
        compensatedTest (reducedGenerator i ω lam) f t γ
    have hZc (k : ℕ) : Continuous (Z k) := (hMkc k t).sub (hMc t)
    have hXsq : Integrable (fun γ => compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) P :=
      ((memLp_two_iff_integrable_sq (hMc t).aestronglyMeasurable).1 (hB' t).1)
    let V : ℝ := 2 * (B * t) + 2 * (B' * t)
    have hZsq (k : ℕ) : Integrable (fun γ => Z k γ ^ 2) P ∧ ∫ γ, Z k γ ^ 2 ∂P ≤ V := by
      have hi : Integrable (fun γ => 2 * compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 +
          2 * compensatedTest (reducedGenerator i ω lam) f t γ ^ 2) P :=
        ((hsqk k t).1.const_mul 2).add (hXsq.const_mul 2)
      have hle : ∀ γ, Z k γ ^ 2 ≤ 2 * compensatedTest (reducedGenerator i ω lam) (F k) t γ ^ 2 +
          2 * compensatedTest (reducedGenerator i ω lam) f t γ ^ 2 := fun γ => by
        nlinarith [sq_nonneg (compensatedTest (reducedGenerator i ω lam) (F k) t γ +
          compensatedTest (reducedGenerator i ω lam) f t γ)]
      have hZi : Integrable (fun γ => Z k γ ^ 2) P :=
        hi.mono' ((hZc k).pow 2).aestronglyMeasurable
          (ae_of_all _ fun γ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hle γ)
      refine ⟨hZi, (integral_mono hZi hi hle).trans ?_⟩
      rw [integral_add ((hsqk k t).1.const_mul 2) (hXsq.const_mul 2), integral_const_mul,
        integral_const_mul]
      linarith [(hsqk k t).2, (hB' t).2]
    let ind : ℕ → Path d → ℝ := fun k γ => if Z k γ = 0 then 0 else 1
    have hind_meas (k : ℕ) : Measurable (ind k) :=
      Measurable.ite (measurableSet_eq_fun (hZc k).measurable measurable_const)
        measurable_const measurable_const
    have hind : Tendsto (fun k => ∫ γ, ind k γ ∂P) atTop (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence (μ := P) (f := fun _ : Path d => (0 : ℝ))
        (fun _ : Path d => (1 : ℝ))
        (fun k => (hind_meas k).aestronglyMeasurable) (integrable_const 1)
        (fun k => ae_of_all _ fun γ => by
          by_cases hz : Z k γ = 0 <;> simp [ind, hz])
        (ae_of_all _ fun γ => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev t γ] with k hk
          have : Z k γ = 0 := by simp only [Z, hk, sub_self]
          simp [ind, this])
      simpa only [integral_zero] using h
    have hint_ind (k : ℕ) : Integrable (ind k) P :=
      (integrable_const (1 : ℝ)).mono' (hind_meas k).aestronglyMeasurable
        (ae_of_all _ fun γ => by by_cases hz : Z k γ = 0 <;> simp [ind, hz])
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hV : 0 ≤ V := by
      have := (hZsq 0).2
      exact le_trans (integral_nonneg fun γ => sq_nonneg _) this
    set c : ℝ := 2 * (V + 1) / ε with hc
    have hcpos : 0 < c := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hind (ε / 2 / (c / 2)) (by positivity)
    refine ⟨N, fun k hk => ?_⟩
    have hb := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun γ => by
      by_cases hz : Z k γ = 0 <;> simp [ind, hz])] at hb
    have hpt : ∀ γ, |Z k γ| ≤ Z k γ ^ 2 / (2 * c) + c / 2 * ind k γ :=
      fun γ => abs_le_sq_div_add_indicator (Z k γ) hcpos
    have hint_rhs : Integrable (fun γ => Z k γ ^ 2 / (2 * c) + c / 2 * ind k γ) P :=
      ((hZsq k).1.div_const _).add ((hint_ind k).const_mul _)
    have habs : Integrable (fun γ => |Z k γ|) P :=
      hint_rhs.mono' (hZc k).abs.aestronglyMeasurable
        (ae_of_all _ fun γ => by rw [Real.norm_eq_abs, abs_abs]; exact hpt γ)
    have hmono := integral_mono habs hint_rhs hpt
    rw [integral_add ((hZsq k).1.div_const _) ((hint_ind k).const_mul _), integral_div,
      integral_const_mul] at hmono
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun γ => abs_nonneg _)]
    have h1 : (∫ γ, Z k γ ^ 2 ∂P) / (2 * c) ≤ V / (2 * c) :=
      div_le_div_of_nonneg_right (hZsq k).2 (by positivity)
    have h2 : V / (2 * c) < ε / 2 := by
      rw [hc, div_lt_iff₀ (by positivity)]
      field_simp
      nlinarith
    have h3 : c / 2 * ∫ γ, ind k γ ∂P < ε / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < c / 2)] at hb
      linarith [mul_comm (c / 2) (∫ γ, ind k γ ∂P)]
    change (∫ γ, |Z k γ| ∂P) < ε
    linarith
  -- set integrals converge
  have hset (t : ℝ≥0) {A : Set (Path d)} (hA : MeasurableSet A) :
      Tendsto (fun k : ℕ => ∫ γ in A, compensatedTest (reducedGenerator i ω lam) (F k) t γ ∂P)
        atTop (𝓝 (∫ γ in A, compensatedTest (reducedGenerator i ω lam) f t γ ∂P)) := by
    have hXi : Integrable (compensatedTest (reducedGenerator i ω lam) f t) P :=
      (hB' t).1.integrable one_le_two
    have hXki (k : ℕ) : Integrable (compensatedTest (reducedGenerator i ω lam) (F k) t) P :=
      (hP.2.2 (F k) (hFd k) (hFc k)).2.1 t
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => ?_) (hL1 t))
    rw [← integral_sub (hXki k).integrableOn hXi.integrableOn]
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [Real.norm_eq_abs]
    exact setIntegral_le_integral ((hXki k).sub hXi).abs
      (ae_of_all _ fun γ => abs_nonneg _)
  have hadapt := stronglyAdapted_compensatedTest_of_measurable (reducedGenerator i ω lam) f
    hf.continuous hLc.measurable
  refine ⟨hadapt, fun s t hst => ?_⟩
  have hXti : Integrable (compensatedTest (reducedGenerator i ω lam) f t) P :=
    (hB' t).1.integrable one_le_two
  have hXsi : Integrable (compensatedTest (reducedGenerator i ω lam) f s) P :=
    (hB' s).1.integrable one_le_two
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((pathFiltration d).le s) hXti
    (fun _ _ _ => hXsi.integrableOn) (fun A hA _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := (pathFiltration d).le s _ hA
  have hk (k : ℕ) := (hP.2.2 (F k) (hFd k) (hFc k)).2.2.setIntegral_eq hst hA
  exact tendsto_nhds_unique ((hset s hA').congr hk) (hset t hA')

/-- Mean forward velocity: the mean displacement over a short time, divided by the time,
converges to the drift at the starting point. -/
theorem tendsto_mean_displacement_div {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (hs : IsSmoothFieldPair ω) (i : Fin d) (lam : ℝ)
    {P : Measure (Path d)} (hP : SolvesMartingaleProblem (reducedGenerator i ω lam) 0 P)
    (j : Fin d) :
    Tendsto (fun δ : ℝ => δ⁻¹ * ∫ γ, γ δ.toNNReal j ∂P) (𝓝[>] 0)
      (𝓝 (forcedDrift (reducedCoefficient ω) i lam 0 j)) := by
  have : IsProbabilityMeasure P := hP.1
  let f : Vec d → ℝ := fun y => y j
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_apply ℝ ℝ j
  let b : Vec d → ℝ := fun y => forcedDrift (reducedCoefficient ω) i lam y j
  have hLb : reducedGenerator i ω lam f = b :=
    funext fun y => response_reducedGenerator_coordinate hs i j lam y
  have hbc : Continuous b := hLb ▸ continuous_reducedGenerator_apply hs i lam hf
  obtain ⟨_, _, _, _, _, ⟨Mb, hMb⟩⟩ := reduced_svHypotheses hΛ hω i lam
  have hbb (y : Vec d) : |b y| ≤ Mb := hMb y j
  have hmart := reduced_coordinate_martingale hΛ hω hs i lam hP j
  -- the mean of the compensated coordinate vanishes
  have hmean (t : ℝ≥0) :
      ∫ γ, compensatedTest (reducedGenerator i ω lam) f t γ ∂P = 0 := by
    have h := hmart.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp [compensatedTest]
  -- the time-averaged drift along a path
  let A : ℝ → Path d → ℝ := fun δ γ => δ⁻¹ * ∫ u in (0 : ℝ)..δ, b (γ u.toNNReal)
  have hAint (δ : ℝ) (hδ : 0 < δ) : Integrable (A δ) P := by
    have hmeas : Measurable (A δ) := by
      have hc : Continuous fun γ : Path d => ∫ u in (0 : ℝ)..δ, b (γ u.toNNReal) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (f := fun (γ : Path d) (u : ℝ) => b (γ u.toNNReal))
          (hbc.comp (continuous_eval.comp (continuous_fst.prodMk
            (continuous_real_toNNReal.comp continuous_snd)))) 0 δ
      exact (continuous_const.mul hc).measurable
    refine Integrable.of_bound hmeas.aestronglyMeasurable Mb (ae_of_all _ fun γ => ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := Mb)
      (f := fun u => b (γ u.toNNReal)) (fun u _ => by rw [Real.norm_eq_abs]; exact hbb _)
    rw [sub_zero, abs_of_pos hδ] at h
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * |∫ u in (0 : ℝ)..δ, b (γ u.toNNReal)| ≤ δ⁻¹ * (Mb * δ) :=
          mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact h) (by positivity)
      _ = Mb := by field_simp
  -- the displacement mean is the averaged drift mean
  obtain ⟨B', _, hB'⟩ := response_coordinate_second_moment hΛ hω hs i lam hP j
  have hdisp : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      δ⁻¹ * ∫ γ, γ δ.toNNReal j ∂P = ∫ γ, A δ γ ∂P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have hMi : Integrable (compensatedTest (reducedGenerator i ω lam) f δ.toNNReal) P :=
      (hB' _).1.integrable one_le_two
    have hIi : Integrable (fun γ : Path d => ∫ u in (0 : ℝ)..δ, b (γ u.toNNReal)) P := by
      have h := (hAint δ hδ').const_mul δ
      refine h.congr (ae_of_all _ fun γ => ?_)
      change δ * (δ⁻¹ * _) = _
      field_simp
    have hpt : ∀ᵐ γ ∂P, γ δ.toNNReal j =
        compensatedTest (reducedGenerator i ω lam) f δ.toNNReal γ +
          ∫ u in (0 : ℝ)..δ, b (γ u.toNNReal) := by
      filter_upwards [hP.2.1] with γ hγ
      simp only [compensatedTest, hLb, hγ, Real.coe_toNNReal _ hδ'.le]
      change γ δ.toNNReal j = γ δ.toNNReal j - (0 : Vec d) j - _ + _
      simp
    rw [integral_congr_ae hpt, integral_add hMi hIi, hmean, zero_add,
      ← integral_const_mul]
  have hlim : ∀ᵐ γ ∂P, Tendsto (fun δ => A δ γ) (𝓝[>] (0 : ℝ)) (𝓝 (b 0)) := by
    filter_upwards [hP.2.1] with γ hγ
    have hg : Continuous fun u : ℝ => b (γ u.toNNReal) :=
      hbc.comp (γ.continuous.comp continuous_real_toNNReal)
    have hd := (hg.integral_hasStrictDerivAt 0 0).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hd
    have h0 : b (γ (0 : ℝ).toNNReal) = b 0 := by
      rw [Real.toNNReal_zero, hγ]
    rw [h0] at hd
    refine (hd.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ _
    simp only [slope, intervalIntegral.integral_same, sub_zero, vsub_eq_sub, smul_eq_mul, A]
  have hA_meas : ∀ᶠ δ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (A δ) P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hAint δ hδ).aestronglyMeasurable
  have hA_bound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ γ ∂P, ‖A δ γ‖ ≤ Mb := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    refine ae_of_all _ fun γ => ?_
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ) (C := Mb)
      (f := fun u => b (γ u.toNNReal)) (fun u _ => by rw [Real.norm_eq_abs]; exact hbb _)
    rw [sub_zero, abs_of_pos hδ'] at h
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ']
    calc δ⁻¹ * |∫ u in (0 : ℝ)..δ, b (γ u.toNNReal)| ≤ δ⁻¹ * (Mb * δ) :=
          mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact h) (by positivity)
      _ = Mb := by field_simp
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun _ : Path d => Mb)
    hA_meas hA_bound (integrable_const Mb) hlim
  rw [integral_const, probReal_univ, one_smul] at hconv
  exact hconv.congr' (hdisp.mono fun δ h => h.symm)

end EinsteinFull.Blueprint
