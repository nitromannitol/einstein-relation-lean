import EinsteinFull.Calculus.S4SharpHarmonicSupport
import EinsteinFull.Calculus.S4MartingaleSllnSupport

/-!
# `app:sharp-harmonic`, conjunct 7: the first coordinate of an existing quenched velocity

If `Y` solves the reduced martingale problem at force `lam` for almost every environment of the
sharp law, and `ell` is a quenched velocity of `Y`, then `ell · e₁ = lam`.  No ergodic input is
used: the harmonic coordinate `x₁ + ψ` has constant generator `lam`, the martingale strong law
along the squares kills the martingale part, and `ψ` is bounded.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

theorem abs_coord_le_euclideanNorm {d : ℕ} (g : Vec d) (j : Fin d) :
    |g j| ≤ euclideanNorm g := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun i => g i * g i) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ j)

theorem tendsto_natCast_sq_nnreal_atTop :
    Tendsto (fun n : ℕ => (n : ℝ≥0) ^ 2) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast Nat.le_self_pow two_ne_zero n

theorem tendsto_natCast_sq_real_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop

/-- Path-level identification of the first coordinate of the velocity. -/
theorem velocity_first_of_slln {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ) {s : ℝ}
    (hψ : ∀ y, |ψ y| ≤ s) (lam : ℝ) (γ : Path d) (ell : Vec d) (hv : HasPathVelocity γ ell)
    (hM : Tendsto (fun n : ℕ =>
      (γ ((n : ℝ≥0) ^ 2) i + ψ (γ ((n : ℝ≥0) ^ 2)) - (γ 0 i + ψ (γ 0)) - (n : ℝ) ^ 2 * lam) /
        (n : ℝ) ^ 2) atTop (𝓝 0)) : ell i = lam := by
  have h1 : Tendsto (fun n : ℕ => γ ((n : ℝ≥0) ^ 2) i / (n : ℝ) ^ 2) atTop (𝓝 (ell i)) := by
    have h := ((continuous_apply i).continuousAt.tendsto.comp
      (hv.comp tendsto_natCast_sq_nnreal_atTop))
    refine h.congr fun n => ?_
    simp [div_eq_inv_mul]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_sq_real_atTop.inv_tendsto_atTop
  have h2 : Tendsto (fun n : ℕ => ψ (γ ((n : ℝ≥0) ^ 2)) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hinv.const_mul s)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hψ _) (by positivity)
  have h3 : Tendsto (fun n : ℕ => (γ 0 i + ψ (γ 0)) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul (γ 0 i + ψ (γ 0))
  have hsum := (h1.add h2).sub h3
  have hsum' : Tendsto (fun n : ℕ => γ ((n : ℝ≥0) ^ 2) i / (n : ℝ) ^ 2 +
      ψ (γ ((n : ℝ≥0) ^ 2)) / (n : ℝ) ^ 2 - (γ 0 i + ψ (γ 0)) / (n : ℝ) ^ 2 - lam) atTop
      (𝓝 (ell i + 0 - 0 - lam)) := hsum.sub_const lam
  have heq : (fun n : ℕ => γ ((n : ℝ≥0) ^ 2) i / (n : ℝ) ^ 2 +
      ψ (γ ((n : ℝ≥0) ^ 2)) / (n : ℝ) ^ 2 - (γ 0 i + ψ (γ 0)) / (n : ℝ) ^ 2 - lam) =ᶠ[atTop]
      (fun n : ℕ => (γ ((n : ℝ≥0) ^ 2) i + ψ (γ ((n : ℝ≥0) ^ 2)) - (γ 0 i + ψ (γ 0)) -
        (n : ℝ) ^ 2 * lam) / (n : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ^ 2 ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have := tendsto_nhds_unique (hsum'.congr' heq) hM
  linarith

/-- **Conjunct 7, identification step.** A quenched velocity of a reduced solution at force `lam`
has first coordinate `lam`, for the sharp law. -/
theorem sharp_velocity_first {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)}
    (hP : External.IsWhiteNoiseLaw P) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (ell : Vec d) (hv : HasQuenchedVelocity Q.measure (originLaw Y) ell) :
    ell (⟨0, by omega⟩ : Fin d) = lam := by
  letI : IsProbabilityMeasure P := hP.1
  set first : Fin d := ⟨0, by omega⟩ with hfirst
  have hpair := EinsteinFull.Work.W8.measurable_physicalPair first
  have hv0 : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(Y (0, ω)), HasPathVelocity γ ell := hv
  rw [hQ] at hY hv0
  have hY' := ae_of_ae_map hpair.aemeasurable hY
  have hv' := ae_of_ae_map hpair.aemeasurable hv0
  obtain ⟨W, hYW, hvW⟩ := (hY'.and hv').exists
  obtain ⟨Λ, hΛ4, hreg⟩ := EinsteinFull.Work.W8.exists_physicalPair_regularity first
  have hΛ : 0 < Λ := by linarith
  have hsmooth := EinsteinFull.Work.W8.physicalPair_isSmooth first W
  have hψc : ContDiff ℝ (⊤ : ℕ∞) (EinsteinFull.Work.W8.corrector W) :=
    EinsteinFull.Work.W8.corrector_contDiff W
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => y first + EinsteinFull.Work.W8.corrector W y) :=
    (contDiff_apply ℝ ℝ first).add hψc
  have hG0 : ∀ (y : Vec d) (j : Fin d), |fderiv ℝ (fun z : Vec d =>
      z first + EinsteinFull.Work.W8.corrector W z) y (unitVector j)| ≤ 5 / 4 := by
    intro y j
    have hψd : DifferentiableAt ℝ (EinsteinFull.Work.W8.corrector W) y :=
      (hψc.differentiable (by simp)) y
    have hc : DifferentiableAt ℝ (fun z : Vec d => z first) y := differentiableAt_apply first y
    have e : fderiv ℝ (fun z : Vec d => z first + EinsteinFull.Work.W8.corrector W z) y
        (unitVector j) =
        unitVector j first + gradient (EinsteinFull.Work.W8.corrector W) y j := by
      rw [fderiv_fun_add hc hψd, ContinuousLinearMap.add_apply,
        (hasFDerivAt_apply first y).fderiv]
      simp only [ContinuousLinearMap.proj_apply]
      try rfl
    rw [e]
    have h1 : |unitVector j first| ≤ 1 := by
      unfold unitVector
      rw [Pi.single_apply]
      split_ifs <;> simp
    have h2 : |gradient (EinsteinFull.Work.W8.corrector W) y j| ≤ 1 / 4 :=
      (abs_coord_le_euclideanNorm _ j).trans (EinsteinFull.Work.W8.corrector_gradient_bound W y)
    calc |unitVector j first + gradient (EinsteinFull.Work.W8.corrector W) y j|
        ≤ |unitVector j first| + |gradient (EinsteinFull.Work.W8.corrector W) y j| :=
          abs_add_le _ _
      _ ≤ 5 / 4 := by linarith
  have hgrow : ∀ y : Vec d, |y first + EinsteinFull.Work.W8.corrector W y| ≤
      EinsteinFull.Work.W8.seedScale d + 1 * ‖y‖ := by
    intro y
    have h1 : |y first| ≤ ‖y‖ := by
      have := norm_le_pi_norm y first
      rwa [Real.norm_eq_abs] at this
    have h2 := EinsteinFull.Work.W8.corrector_abs_le W y
    calc |y first + EinsteinFull.Work.W8.corrector W y|
        ≤ |y first| + |EinsteinFull.Work.W8.corrector W y| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hslln := reduced_slln_squares hΛ (hreg W) hsmooth first lam hYW hf hG0 hgrow
    (EinsteinFull.Work.W8.seedScale_pos d).le zero_le_one
  haveI : IsProbabilityMeasure (Y (0, EinsteinFull.Work.W8.physicalPair first W)) := hYW.1
  obtain ⟨γ, hγ1, hγ2⟩ := (hvW.and hslln).exists
  refine velocity_first_of_slln first (EinsteinFull.Work.W8.corrector W)
    (s := EinsteinFull.Work.W8.seedScale d)
    (fun y => EinsteinFull.Work.W8.corrector_abs_le W y) lam γ ell hγ1 ?_
  refine hγ2.congr fun n => ?_
  have hLf : ∀ y : Vec d, reducedGenerator first (EinsteinFull.Work.W8.physicalPair first W) lam
      (fun z => z first + EinsteinFull.Work.W8.corrector W z) y = lam := fun y =>
    EinsteinFull.Work.W8.physicalPair_harmonicCoordinate_generator first W lam y
  have hint : ∫ u in (0 : ℝ)..(((n : ℝ≥0) ^ 2 : ℝ≥0) : ℝ),
      reducedGenerator first (EinsteinFull.Work.W8.physicalPair first W) lam
        (fun z => z first + EinsteinFull.Work.W8.corrector W z) (γ u.toNNReal) =
      (n : ℝ) ^ 2 * lam := by
    simp only [hLf, intervalIntegral.integral_const, smul_eq_mul, NNReal.coe_pow,
      NNReal.coe_natCast, sub_zero]
  show ((γ ((n : ℝ≥0) ^ 2) first + EinsteinFull.Work.W8.corrector W (γ ((n : ℝ≥0) ^ 2))) -
    (γ 0 first + EinsteinFull.Work.W8.corrector W (γ 0)) -
    ∫ u in (0 : ℝ)..(((n : ℝ≥0) ^ 2 : ℝ≥0) : ℝ),
      reducedGenerator first (EinsteinFull.Work.W8.physicalPair first W) lam
        (fun z => z first + EinsteinFull.Work.W8.corrector W z) (γ u.toNNReal)) / (n : ℝ) ^ 2 = _
  rw [hint]

end EinsteinFull.Blueprint
