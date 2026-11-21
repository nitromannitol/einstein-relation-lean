import EinsteinFull.Homogenization.HeatFormulaSmallTime

/-!
# Large times in the heat formula and the joint Cauchy property

If the Hessian convolutions `∂ⱼ∂ᵢΦ_t * f` decay like `t^(-1-κ)` at large times on the parabolic
region `|x|² ≤ t`, the time integrals of the heat formula (6.7) in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, converge uniformly on balls at
large times. Together with the small-time Cauchy property this shows that the truncations
`∫_{1/(m+1)}^{n+1} ∂ⱼ∂ᵢΦ_t * f dt` are Cauchy in `L²(B_ρ)` as `m` and `n` tend to infinity
independently.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

/-- Large-time decay of the Hessian convolutions on the parabolic region. -/
def HasHeatHessianDecay (f : Vec d → ℝ) (i j : Fin d) : Prop :=
  ∃ A κ T₀ : ℝ, 0 ≤ A ∧ 0 < κ ∧ 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ x : Vec d,
    euclideanNorm x ^ 2 ≤ t → |heatHessianConv t i j f x| ≤ A * t ^ (-(1 + κ))

theorem setIntegral_rpow_neg_le {a b κ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hκ : 0 < κ) :
    ∫ t in Icc a b, t ^ (-(1 + κ)) ≤ a ^ (-κ) / κ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inr ⟨by linarith, fun h => by
      rw [uIcc_of_le hab] at h
      linarith [h.1]⟩)]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [show -(1 + κ) + 1 = -κ by ring]
  have h1 : 0 ≤ b ^ (-κ) := Real.rpow_nonneg hb.le _
  rw [div_neg, ← neg_div, neg_sub]
  exact div_le_div_of_nonneg_right (by linarith) hκ.le

/-- Uniform smallness of large-time windows on balls. -/
theorem abs_heatHessianWindow_le_of_decay {f : Vec d → ℝ} {i j : Fin d}
    {A κ T₀ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ)
    (hT₀ : 0 < T₀) (hdec : ∀ t : ℝ, T₀ ≤ t → ∀ x : Vec d,
      euclideanNorm x ^ 2 ≤ t → |heatHessianConv t i j f x| ≤ A * t ^ (-(1 + κ)))
    {a b : ℝ} (hTa : T₀ ≤ a) (hab : a ≤ b) {x : Vec d} (hx : euclideanNorm x ^ 2 ≤ a) :
    |heatHessianWindow a b i j f x| ≤ A / κ * a ^ (-κ) := by
  have ha : 0 < a := lt_of_lt_of_le hT₀ hTa
  have hint : IntegrableOn (fun t : ℝ => A * t ^ (-(1 + κ))) (Icc a b) volume := by
    have hc : ContinuousOn (fun t : ℝ => A * t ^ (-(1 + κ))) (Icc a b) := fun t ht =>
      (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl
        (lt_of_lt_of_le ha ht.1).ne'))).continuousWithinAt
    exact hc.integrableOn_Icc
  unfold heatHessianWindow
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact hdec t (hTa.trans ht.1) x (hx.trans ht.1)
  · rw [integral_const_mul]
    calc A * ∫ t in Icc a b, t ^ (-(1 + κ)) ≤ A * (a ^ (-κ) / κ) :=
          mul_le_mul_of_nonneg_left (setIntegral_rpow_neg_le ha hab hκ) hA
      _ = A / κ * a ^ (-κ) := by ring

/-- **Large-time Cauchy property on balls.** -/
theorem HasHeatHessianDecay.exists_eLpNorm_heatHessianWindow_le {f : Vec d → ℝ} {i j : Fin d}
    (hdec : HasHeatHessianDecay f i j) (hfm : Measurable f)
    (ρ : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ ∀ a b : ℝ, T ≤ a → a ≤ b →
      eLpNorm (heatHessianWindow a b i j f) 2 (volume.restrict (ball 0 ρ)) ≤ δ := by
  obtain ⟨A, κ, T₀, hA, hκ, hT₀, hdec⟩ := hdec
  set V : ℝ≥0∞ := volume (ball (0 : Vec d) ρ) ^ (ENNReal.toReal 2)⁻¹ with hV
  have hVfin : V ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (volume_ball_zero_lt_top ρ).ne
  have hlim : Tendsto (fun a : ℝ => V * ENNReal.ofReal (A / κ * a ^ (-κ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => A / κ * a ^ (-κ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop hκ).const_mul (A / κ)
    have h2 := ENNReal.tendsto_ofReal h1
    rw [ENNReal.ofReal_zero] at h2
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr hVfin)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp hlim) δ hδ)
  refine ⟨max (max T₀ (ρ ^ 2)) (max T₁ 1), by positivity, fun a b ha hab => ?_⟩
  have hTa : T₀ ≤ a := ((le_max_left _ _).trans (le_max_left _ _)).trans ha
  have hρa : ρ ^ 2 ≤ a := ((le_max_right _ _).trans (le_max_left _ _)).trans ha
  have hT₁a : T₁ ≤ a := ((le_max_left _ _).trans (le_max_right _ _)).trans ha
  have ha0 : 0 < a := lt_of_lt_of_le hT₀ hTa
  have hbd : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)),
      ‖heatHessianWindow a b i j f x‖ ≤ A / κ * a ^ (-κ) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball_zero ρ)] with x hx
    have hx' : euclideanNorm (x - 0) < ρ := hx
    rw [sub_zero] at hx'
    have hx2 : euclideanNorm x ^ 2 ≤ a := by
      have h0 : 0 ≤ euclideanNorm x := by unfold euclideanNorm; positivity
      nlinarith
    rw [Real.norm_eq_abs]
    exact abs_heatHessianWindow_le_of_decay hA hκ hT₀ hdec hTa hab hx2
  refine (eLpNorm_le_of_ae_bound
    (stronglyMeasurable_heatHessianWindow ha0 i j hfm).aestronglyMeasurable hbd).trans ?_
  rw [Measure.restrict_apply_univ]
  exact hT₁ a hT₁a

/-- The time truncation `∫_{1/(m+1)}^{n+1}` of the heat Hessian. -/
noncomputable def heatHessianTruncation (m n : ℕ) (i j : Fin d) (f : Vec d → ℝ) (x : Vec d) :
    ℝ :=
  heatHessianWindow ((m + 1 : ℕ) : ℝ)⁻¹ ((n + 1 : ℕ) : ℝ) i j f x

theorem natCast_succ_inv_le_one (m : ℕ) : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_pos m)

theorem one_le_natCast_succ (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_pos n

theorem natCast_succ_inv_pos (m : ℕ) : 0 < ((m + 1 : ℕ) : ℝ)⁻¹ := by positivity

/-- A truncation splits into its small-time and large-time parts. -/
theorem HasGaussianMoments.heatHessianTruncation_eq {f : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hfm : Measurable f) (m n : ℕ) (i j : Fin d) (x : Vec d) :
    heatHessianTruncation m n i j f x =
      heatHessianWindow ((m + 1 : ℕ) : ℝ)⁻¹ 1 i j f x +
        heatHessianWindow 1 ((n + 1 : ℕ) : ℝ) i j f x :=
  (hf.heatHessianWindow_add (natCast_succ_inv_pos m) (natCast_succ_inv_le_one m)
    (one_le_natCast_succ n) i j hfm x).symm

/-- The difference of two windows with a common right endpoint. -/
theorem HasGaussianMoments.eLpNorm_window_sub_le {f : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hfm : Measurable f) {a a' c : ℝ} (ha : 0 < a) (ha' : 0 < a') (hac : a ≤ c) (ha'c : a' ≤ c)
    (i j : Fin d) (μ : Measure (Vec d)) :
    eLpNorm (fun x => heatHessianWindow a c i j f x - heatHessianWindow a' c i j f x) 2 μ ≤
      eLpNorm (heatHessianWindow (min a a') (max a a') i j f) 2 μ := by
  rcases le_total a a' with h | h
  · rw [min_eq_left h, max_eq_right h]
    refine le_of_eq (congrArg (fun F => eLpNorm F 2 μ) (funext fun x => ?_))
    rw [← hf.heatHessianWindow_add ha h ha'c i j hfm x]
    ring
  · rw [min_eq_right h, max_eq_left h]
    refine le_of_eq ?_
    rw [← eLpNorm_neg]
    refine congrArg (fun F => eLpNorm F 2 μ) (funext fun x => ?_)
    rw [Pi.neg_apply, ← hf.heatHessianWindow_add ha' h hac i j hfm x]
    ring

/-- The difference of two windows with a common left endpoint. -/
theorem HasGaussianMoments.eLpNorm_window_sub_le' {f : Vec d → ℝ} (hf : HasGaussianMoments f)
    (hfm : Measurable f) {a b b' : ℝ} (ha : 0 < a) (hab : a ≤ b) (hab' : a ≤ b')
    (i j : Fin d) (μ : Measure (Vec d)) :
    eLpNorm (fun x => heatHessianWindow a b i j f x - heatHessianWindow a b' i j f x) 2 μ ≤
      eLpNorm (heatHessianWindow (min b b') (max b b') i j f) 2 μ := by
  rcases le_total b b' with h | h
  · rw [min_eq_left h, max_eq_right h]
    refine le_of_eq ?_
    rw [← eLpNorm_neg]
    refine congrArg (fun F => eLpNorm F 2 μ) (funext fun x => ?_)
    rw [Pi.neg_apply, ← hf.heatHessianWindow_add ha hab h i j hfm x]
    ring
  · rw [min_eq_right h, max_eq_left h]
    refine le_of_eq (congrArg (fun F => eLpNorm F 2 μ) (funext fun x => ?_))
    rw [← hf.heatHessianWindow_add ha hab' h i j hfm x]
    ring

/-- **Joint Cauchy property on balls** of the time truncations. -/
theorem exists_eLpNorm_heatHessianTruncation_sub_le {f : Vec d → ℝ} (hfm : Measurable f)
    (hloc : ∀ R : ℝ, MemLp f 2 (volume.restrict (ball 0 R))) (hf : HasGaussianMoments f)
    {i j : Fin d} (hdec : HasHeatHessianDecay f i j) (ρ : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ m n m' n' : ℕ, N ≤ m → N ≤ n → N ≤ m' → N ≤ n' →
      eLpNorm (fun x => heatHessianTruncation m n i j f x -
        heatHessianTruncation m' n' i j f x) 2 (volume.restrict (ball 0 ρ)) ≤ δ := by
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨η, hη, hsmall⟩ := exists_eLpNorm_heatHessianWindow_ball_le hfm hloc hf i j ρ hδ2
  obtain ⟨T, hT, hlarge⟩ := hdec.exists_eLpNorm_heatHessianWindow_le hfm ρ hδ2
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (η⁻¹)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt T
  refine ⟨max N₁ N₂, fun m n m' n' hm hn hm' hn' => ?_⟩
  set μ := volume.restrict (ball (0 : Vec d) ρ)
  have hsmall' : ∀ k : ℕ, max N₁ N₂ ≤ k → ((k + 1 : ℕ) : ℝ)⁻¹ ≤ η := by
    intro k hk
    have hk1 : (N₁ : ℝ) ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
    rw [inv_le_comm₀ (by positivity) hη]
    push_cast
    linarith
  have hlarge' : ∀ k : ℕ, max N₁ N₂ ≤ k → T ≤ ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk2 : (N₂ : ℝ) ≤ k := by exact_mod_cast (le_max_right _ _).trans hk
    push_cast
    linarith
  have hsplit : (fun x => heatHessianTruncation m n i j f x -
      heatHessianTruncation m' n' i j f x) =
      (fun x => heatHessianWindow ((m + 1 : ℕ) : ℝ)⁻¹ 1 i j f x -
        heatHessianWindow ((m' + 1 : ℕ) : ℝ)⁻¹ 1 i j f x) +
      (fun x => heatHessianWindow 1 ((n + 1 : ℕ) : ℝ) i j f x -
        heatHessianWindow 1 ((n' + 1 : ℕ) : ℝ) i j f x) := by
    funext x
    simp only [Pi.add_apply, hf.heatHessianTruncation_eq hfm]
    ring
  rw [hsplit]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  calc _ ≤ δ / 2 + δ / 2 := by
        refine add_le_add ?_ ?_
        · refine (hf.eLpNorm_window_sub_le hfm (natCast_succ_inv_pos m) (natCast_succ_inv_pos m')
            (natCast_succ_inv_le_one m) (natCast_succ_inv_le_one m') i j μ).trans ?_
          refine hsmall _ _ (lt_min (natCast_succ_inv_pos m) (natCast_succ_inv_pos m'))
            (min_le_max) (max_le (hsmall' m hm) (hsmall' m' hm'))
        · refine (hf.eLpNorm_window_sub_le' hfm one_pos (one_le_natCast_succ n)
            (one_le_natCast_succ n') i j μ).trans ?_
          exact hlarge _ _ (le_min (hlarge' n hn) (hlarge' n' hn')) min_le_max
    _ = δ := ENNReal.add_halves δ

end EinsteinFull.Homogenization
