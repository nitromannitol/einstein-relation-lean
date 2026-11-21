import EinsteinFull.Homogenization.HeatFormulaLocal

/-!
# Small times in the heat formula on balls

Let `f` be locally square integrable with Gaussian moments. On a ball `B_ρ`, the time-truncated
heat Hessian `∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * f dt` of the heat formula (6.7) in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, tends to zero in
`L²(B_ρ)` as both endpoints tend to zero. The near part `f 1_{B_{ρ+1}}` is square integrable and
is handled by the Calderón–Zygmund estimate; for the far part the kernel stays at distance one
from the singularity, where `|∂ᵢ∂ⱼΦ_t| ≤ A Φ₄` for `t ≤ 1`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology Nat

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

theorem one_le_euclideanNorm_sub {ρ : ℝ} {x y : Vec d} (hx : euclideanNorm x ≤ ρ)
    (hy : y ∉ ball (0 : Vec d) (ρ + 1)) : 1 ≤ euclideanNorm (x - y) := by
  have hy' : ρ + 1 ≤ euclideanNorm y := by
    have : ¬ euclideanNorm (y - 0) < ρ + 1 := hy
    rw [sub_zero] at this
    exact not_lt.mp this
  have htri := TimeChange.euclideanNorm_add_le (y - x) x
  rw [sub_add_cancel] at htri
  have hsym : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    rw [show y - x = -(x - y) by abel]
    unfold euclideanNorm euclideanSq dot
    congr 1
    exact Finset.sum_congr rfl fun l _ => by simp only [Pi.neg_apply, Pi.sub_apply]; ring
  linarith

/-- Away from the singularity the heat-kernel Hessian at times `t ≤ 1` is dominated by `Φ₄`. -/
theorem exists_heatHessian_far_le (d : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ i j : Fin d, ∀ z : Vec d,
      1 ≤ euclideanNorm z →
        |coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) z| ≤
          A * euclideanHeatKernel 4 z := by
  set k : ℕ := d + 1 with hk
  set A : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * ((32 : ℝ) ^ k * (Nat.factorial k : ℝ)) with hA
  refine ⟨A, by positivity, fun t ht ht1 i j z hz => ?_⟩
  have hz2 : 1 ≤ euclideanSq z := by
    rw [euclideanSq_eq_euclideanNorm_sq]
    nlinarith
  suffices key : 2 / t * euclideanHeatKernel (2 * t) z ≤
      (32 : ℝ) ^ k * (Nat.factorial k : ℝ) * euclideanHeatKernel 4 z by
    calc |coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) z|
        ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) z :=
          abs_heatHessian_le ht i j z
      _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t * euclideanHeatKernel (2 * t) z) := by ring
      _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) *
            ((32 : ℝ) ^ k * (Nat.factorial k : ℝ) * euclideanHeatKernel 4 z) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = A * euclideanHeatKernel 4 z := by rw [hA]; ring
  set u : ℝ := 1 / (16 * t) with hu
  have hu0 : 0 < u := by positivity
  have h32 : 2 / t = 32 * u := by rw [hu]; field_simp; ring
  have hratio : euclideanHeatKernel (2 * t) z =
      (2 / t) ^ ((d : ℝ) / 2) * Real.exp (-(euclideanSq z) * (2 - t) / (16 * t)) *
        euclideanHeatKernel 4 z := by
    unfold euclideanHeatKernel
    have e1 : (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) =
        (2 / t) ^ ((d : ℝ) / 2) * (4 * Real.pi * 4) ^ (-(d : ℝ) / 2) := by
      have : 4 * Real.pi * (2 * t) = (t / 2) * (4 * Real.pi * 4) := by ring
      rw [this, Real.mul_rpow (by positivity) (by positivity),
        show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg (by positivity),
        ← Real.inv_rpow (by positivity), inv_div]
    rw [e1, show -(euclideanSq z) / (4 * (2 * t)) =
      -(euclideanSq z) * (2 - t) / (16 * t) + -(euclideanSq z) / (4 * 4) by
        field_simp
        ring, Real.exp_add]
    ring
  have hexp : Real.exp (-(euclideanSq z) * (2 - t) / (16 * t)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    rw [hu, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have hpow : (2 / t) ^ ((d : ℝ) / 2) * (2 / t) ≤ (32 * u) ^ k := by
    rw [h32]
    have h1 : 1 ≤ 32 * u := by
      rw [hu, show (32 : ℝ) * (1 / (16 * t)) = 2 / t by field_simp; ring, le_div_iff₀ ht]
      linarith
    calc (32 * u) ^ ((d : ℝ) / 2) * (32 * u) = (32 * u) ^ ((d : ℝ) / 2 + 1) := by
          rw [Real.rpow_add (by positivity), Real.rpow_one]
      _ ≤ (32 * u) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by
          rw [hk]; push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      _ = (32 * u) ^ k := Real.rpow_natCast _ _
  have hfac : u ^ k * Real.exp (-u) ≤ (Nat.factorial k : ℝ) := by
    have h := Real.pow_div_factorial_le_exp u hu0.le k
    rw [div_le_iff₀ (by positivity)] at h
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos u)]
    linarith [mul_comm (Real.exp u) (Nat.factorial k : ℝ)]
  have hK4 := euclideanHeatKernel_nonneg (d := d) (t := 4) (by norm_num) z
  rw [hratio]
  calc 2 / t * ((2 / t) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq z * (2 - t) / (16 * t)) *
        euclideanHeatKernel 4 z)
      = ((2 / t) ^ ((d : ℝ) / 2) * (2 / t)) * Real.exp (-euclideanSq z * (2 - t) / (16 * t)) *
          euclideanHeatKernel 4 z := by ring
    _ ≤ (32 * u) ^ k * Real.exp (-u) * euclideanHeatKernel 4 z := by
        gcongr
    _ = (32 : ℝ) ^ k * (u ^ k * Real.exp (-u)) * euclideanHeatKernel 4 z := by
        rw [mul_pow]
        ring
    _ ≤ (32 : ℝ) ^ k * (Nat.factorial k : ℝ) * euclideanHeatKernel 4 z := by
        gcongr

theorem HasGaussianMoments.mono {f g : Vec d → ℝ} (hf : HasGaussianMoments f) (hgm : Measurable g)
    (hgf : ∀ y, |g y| ≤ |f y|) : HasGaussianMoments g := by
  intro s hs ρ
  obtain ⟨B, hB⟩ := hf s hs ρ
  refine ⟨B, fun x hx => ?_⟩
  have hint := (hB x hx).1
  have hmeas : AEStronglyMeasurable (fun y => euclideanHeatKernel s (x - y) * |g y|) volume :=
    (((measurable_euclideanHeatKernel s).comp (measurable_const.sub measurable_id)).mul
      (continuous_abs.measurable.comp hgm)).aestronglyMeasurable
  have hle : ∀ y, euclideanHeatKernel s (x - y) * |g y| ≤ euclideanHeatKernel s (x - y) * |f y| :=
    fun y => mul_le_mul_of_nonneg_left (hgf y) (euclideanHeatKernel_nonneg hs.le _)
  have hint' : Integrable (fun y => euclideanHeatKernel s (x - y) * |g y|) volume :=
    hint.mono' hmeas (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (euclideanHeatKernel_nonneg hs.le _)
        (abs_nonneg _))]
      exact hle y)
  exact ⟨hint', (integral_mono hint' hint hle).trans (hB x hx).2⟩

/-- The far part has bounded Hessian convolutions at small times on the ball. -/
theorem HasGaussianMoments.abs_heatHessianConv_far_le {f : Vec d → ℝ}
    (hf : HasGaussianMoments f) (i j : Fin d) (ρ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x : Vec d, euclideanNorm x ≤ ρ →
      |heatHessianConv t i j ((ball (0 : Vec d) (ρ + 1))ᶜ.indicator f) x| ≤ C := by
  obtain ⟨A, hA0, hA⟩ := exists_heatHessian_far_le d
  obtain ⟨B, hB⟩ := hf 4 (by norm_num) ρ
  refine ⟨A * max B 0, mul_nonneg hA0 (le_max_right _ _), fun t ht ht1 x hx => ?_⟩
  have hint := (hB x hx).1
  calc |heatHessianConv t i j ((ball (0 : Vec d) (ρ + 1))ᶜ.indicator f) x|
      ≤ ∫ y, A * (euclideanHeatKernel 4 (x - y) * |f y|) := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul A)
          (Filter.Eventually.of_forall fun y => ?_))
        simp only
        by_cases hy : y ∈ ball (0 : Vec d) (ρ + 1)
        · rw [indicator_of_notMem (show y ∉ (ball (0 : Vec d) (ρ + 1))ᶜ from fun h => h hy),
            mul_zero, abs_zero]
          exact mul_nonneg hA0 (mul_nonneg (euclideanHeatKernel_nonneg (by norm_num) _)
            (abs_nonneg _))
        · rw [indicator_of_mem hy, abs_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (hA t ht ht1 i j _ (one_le_euclideanNorm_sub hx hy)) (abs_nonneg _)
    _ = A * ∫ y, euclideanHeatKernel 4 (x - y) * |f y| := integral_const_mul _ _
    _ ≤ A * max B 0 := mul_le_mul_of_nonneg_left ((hB x hx).2.trans (le_max_left _ _)) hA0

/-- **Small-time Cauchy property on balls** of the time-truncated heat Hessian of a locally
square-integrable function with Gaussian moments. -/
theorem exists_eLpNorm_heatHessianWindow_ball_le {f : Vec d → ℝ} (hfm : Measurable f)
    (hloc : ∀ R : ℝ, MemLp f 2 (volume.restrict (ball 0 R))) (hf : HasGaussianMoments f)
    (i j : Fin d) (ρ : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ ε₂ → ε₂ ≤ η →
      eLpNorm (heatHessianWindow ε₁ ε₂ i j f) 2 (volume.restrict (ball 0 ρ)) ≤ δ := by
  set U := ball (0 : Vec d) (ρ + 1) with hU
  have hUm : MeasurableSet U := measurableSet_ball_zero _
  set f₁ := U.indicator f with hf₁
  set f₂ := Uᶜ.indicator f with hf₂
  have hsum : f = f₁ + f₂ := (indicator_self_add_compl U f).symm
  have hf₁m : Measurable f₁ := hfm.indicator hUm
  have hf₂m : Measurable f₂ := hfm.indicator hUm.compl
  have hf₁2 : MemLp f₁ 2 volume := (memLp_indicator_iff_restrict hUm).2 (hloc (ρ + 1))
  have hf₁mom := hasGaussianMoments_of_memLp hf₁m hf₁2
  have hf₂mom : HasGaussianMoments f₂ := hf.mono hf₂m fun y => by
    simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := Uᶜ) (f := f) (a := y)
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨η₁, hη₁, hnear⟩ := exists_eLpNorm_heatHessianWindow_le hf₁m hf₁2 i j hδ2
  obtain ⟨C, hC0, hC⟩ := hf.abs_heatHessianConv_far_le i j ρ
  set V : ℝ≥0∞ := volume (ball (0 : Vec d) ρ) ^ (ENNReal.toReal 2)⁻¹ with hV
  have hVfin : V ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (volume_ball_zero_lt_top ρ).ne
  have hlim : Tendsto (fun η : ℝ => V * ENNReal.ofReal (η * C)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun η : ℝ => ENNReal.ofReal (η * C)) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => η * C) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun η : ℝ => η * C := by fun_prop
        simpa using hc.tendsto (0 : ℝ)
      simpa using ENNReal.tendsto_ofReal this
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hVfin)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((ENNReal.tendsto_nhds_zero.mp hlim) (δ / 2) hδ2)
  refine ⟨min (min η₁ (r / 2)) 1, lt_min (lt_min hη₁ (by positivity)) one_pos,
    fun ε₁ ε₂ hε₁ hε hε₂ => ?_⟩
  have hε₂η₁ : ε₂ ≤ η₁ := hε₂.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₂r : ε₂ ≤ r / 2 := hε₂.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε₂1 : ε₂ ≤ 1 := hε₂.trans (min_le_right _ _)
  have hsplit : heatHessianWindow ε₁ ε₂ i j f =
      heatHessianWindow ε₁ ε₂ i j f₁ + heatHessianWindow ε₁ ε₂ i j f₂ := by
    funext x
    rw [Pi.add_apply, ← heatHessianWindow_add_of_moments hf₁mom hf₂mom hf₁m hf₂m hε₁ i j x,
      ← hsum]
  have hfar : eLpNorm (heatHessianWindow ε₁ ε₂ i j f₂) 2 (volume.restrict (ball 0 ρ)) ≤
      δ / 2 := by
    have hbd : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)),
        ‖heatHessianWindow ε₁ ε₂ i j f₂ x‖ ≤ ε₂ * C := by
      filter_upwards [ae_restrict_mem (measurableSet_ball_zero ρ)] with x hx
      have hx' : euclideanNorm (x - 0) < ρ := hx
      rw [sub_zero] at hx'
      have hb := norm_setIntegral_le_of_norm_le_const (s := Icc ε₁ ε₂)
        (f := fun t => heatHessianConv t i j f₂ x) (C := C)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
        (fun t ht => by
          rw [Real.norm_eq_abs]
          exact hC t (lt_of_lt_of_le hε₁ ht.1) (ht.2.trans hε₂1) x hx'.le)
      simp only [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ ε₂ - ε₁)] at hb
      calc ‖heatHessianWindow ε₁ ε₂ i j f₂ x‖ ≤ C * (ε₂ - ε₁) := hb
        _ ≤ ε₂ * C := by nlinarith
    refine (eLpNorm_le_of_ae_bound
      (stronglyMeasurable_heatHessianWindow hε₁ i j hf₂m).aestronglyMeasurable hbd).trans ?_
    rw [Measure.restrict_apply_univ]
    refine le_trans ?_ (hball (y := ε₂) ?_)
    · exact le_rfl
    · rw [Real.dist_eq, sub_zero, abs_of_pos (lt_of_lt_of_le hε₁ hε)]
      linarith
  rw [hsplit]
  calc eLpNorm (heatHessianWindow ε₁ ε₂ i j f₁ + heatHessianWindow ε₁ ε₂ i j f₂) 2
        (volume.restrict (ball 0 ρ))
      ≤ eLpNorm (heatHessianWindow ε₁ ε₂ i j f₁) 2 (volume.restrict (ball 0 ρ)) +
          eLpNorm (heatHessianWindow ε₁ ε₂ i j f₂) 2 (volume.restrict (ball 0 ρ)) :=
        eLpNorm_add_le (by norm_num)
    _ ≤ δ / 2 + δ / 2 := add_le_add ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (hnear ε₁ ε₂ hε₁ hε hε₂η₁)) hfar
    _ = δ := ENNReal.add_halves δ

end EinsteinFull.Homogenization
