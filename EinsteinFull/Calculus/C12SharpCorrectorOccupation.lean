import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_clock
import EinsteinFull.Calculus.S2SharpClockSupport
import EinsteinFull.Calculus.S4MartingaleSllnSupport

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

/-- A bounded rate permits interpolation between consecutive square times. -/
private theorem average_zero_of_squares (F : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hinc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → |F t - F s| ≤ K * (t - s))
    (hsq : Tendsto (fun n : ℕ => F ((n : ℝ) ^ 2) / (n : ℝ) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => F t / t) atTop (𝓝 0) := by
  let n : ℝ → ℕ := fun t => ⌊Real.sqrt t⌋₊
  have hnlim : Tendsto n atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_sqrt_atTop
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hbound : Tendsto (fun k : ℕ => |F ((k : ℝ) ^ 2) / (k : ℝ) ^ 2| +
      K * (2 * (k : ℝ)⁻¹ + ((k : ℝ)⁻¹) ^ 2)) atTop (𝓝 0) := by
    simpa using hsq.abs.add (((hinv.const_mul 2).add (hinv.pow 2)).const_mul K)
  refine squeeze_zero_norm' ?_ (hbound.comp hnlim)
  filter_upwards [hnlim.eventually (eventually_ge_atTop 1), eventually_ge_atTop (0 : ℝ)]
    with t hn ht0
  have hn1 : (1 : ℝ) ≤ (n t : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n t : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hfloor : (n t : ℝ) ≤ Real.sqrt t := Nat.floor_le (Real.sqrt_nonneg t)
  have hceil : Real.sqrt t < (n t : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqrt : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0
  have hsmall : (n t : ℝ) ^ 2 ≤ t := by
    nlinarith [Real.sqrt_nonneg t]
  have hlarge : t < ((n t : ℝ) + 1) ^ 2 := by
    nlinarith [Real.sqrt_nonneg t]
  have ht : 0 < t := lt_of_lt_of_le (sq_pos_of_pos hn0) hsmall
  have hgap : t - (n t : ℝ) ^ 2 ≤ 2 * (n t : ℝ) + 1 := by nlinarith
  have hF : |F t| ≤ |F ((n t : ℝ) ^ 2)| + K * (2 * (n t : ℝ) + 1) := by
    calc
      |F t| = |(F t - F ((n t : ℝ) ^ 2)) + F ((n t : ℝ) ^ 2)| := by rw [sub_add_cancel]
      _ ≤ |F t - F ((n t : ℝ) ^ 2)| + |F ((n t : ℝ) ^ 2)| := abs_add_le _ _
      _ ≤ K * (t - (n t : ℝ) ^ 2) + |F ((n t : ℝ) ^ 2)| :=
        by linarith only [hinc _ _ (sq_nonneg _) hsmall]
      _ ≤ |F ((n t : ℝ) ^ 2)| + K * (2 * (n t : ℝ) + 1) := by
        linarith only [mul_le_mul_of_nonneg_left hgap hK]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht]
  calc
    |F t| / t ≤ (|F ((n t : ℝ) ^ 2)| + K * (2 * (n t : ℝ) + 1)) / t :=
      div_le_div_of_nonneg_right hF ht.le
    _ ≤ (|F ((n t : ℝ) ^ 2)| + K * (2 * (n t : ℝ) + 1)) / (n t : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0) hsmall
    _ = |F ((n t : ℝ) ^ 2) / (n t : ℝ) ^ 2| +
        K * (2 * (n t : ℝ)⁻¹ + ((n t : ℝ)⁻¹) ^ 2) := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hn0)]
      field_simp

private theorem sharp_generator_bounded {d : ℕ} (i : Fin d) (W : NoiseSample d) (lam : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Vec d,
      |reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
        (EinsteinFull.Work.W8.corrector W) x| ≤ K := by
  have hp := EinsteinFull.Work.W8.clockParameter_pos i
  refine ⟨(1 / 4 : ℝ) / EinsteinFull.Work.W8.clockParameter i + 4 * |lam|,
    by positivity, fun x => ?_⟩
  have hclock := EinsteinFull.Work.W8.density_bounds i W x
  rw [← EinsteinFull.Work.W8.physicalPair_clockDensity i W x] at hclock
  have hclockabs : |1 - clockDensity (EinsteinFull.Work.W8.physicalPair i W) x| ≤ 1 / 4 :=
    abs_le.2 ⟨by linarith [hclock.2], by linarith [hclock.1]⟩
  have hcoeff := abs_apply_le_of_isElliptic (by norm_num : (0 : ℝ) < 3)
    (EinsteinFull.Work.W8.reducedCoefficient_isElliptic i W) x i i
  have hcoeffabs : |1 - reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i| ≤ 4 :=
    (abs_sub _ _).trans (by rw [abs_one]; linarith only [hcoeff])
  rw [(sharpClock_identities i W x lam).2]
  calc
    _ ≤ |(1 - clockDensity (EinsteinFull.Work.W8.physicalPair i W) x) /
        EinsteinFull.Work.W8.clockParameter i| +
        |lam * (1 - reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i)| :=
      abs_add_le _ _
    _ ≤ (1 / 4 : ℝ) / EinsteinFull.Work.W8.clockParameter i + 4 * |lam| := by
      rw [abs_div, abs_of_pos hp, abs_mul, mul_comm 4]
      exact add_le_add (div_le_div_of_nonneg_right hclockabs hp.le)
        (mul_le_mul_of_nonneg_left hcoeffabs (abs_nonneg lam))

/-- The actual bounded sharp corrector has vanishing generator occupation average
under every supplied solution of its reduced martingale problem. -/
theorem sharp_corrector_generator_time_average_zero
    {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (W : NoiseSample d) (lam : ℝ)
    (Y : Measure (Path d))
    (hY : SolvesMartingaleProblem
      (reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam) 0 Y) :
    ∀ᵐ γ ∂Y,
      Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
        reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
          (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos d with hdim | hdim
  · have hbad : 2 ≤ 0 := hdim ▸ hd
    omega
  · clear hd hdim
    obtain ⟨Λ, hΛ4, hreg⟩ := EinsteinFull.Work.W8.exists_physicalPair_regularity i
    have hΛ : 0 < Λ := by linarith only [hΛ4]
    have hsmooth := EinsteinFull.Work.W8.physicalPair_isSmooth i W
    have hf := EinsteinFull.Work.W8.corrector_contDiff W
    have hG : ∀ (x : Vec d) (j : Fin d),
        |fderiv ℝ (EinsteinFull.Work.W8.corrector W) x (unitVector j)| ≤ 1 / 4 := by
      intro x j
      change |gradient (EinsteinFull.Work.W8.corrector W) x j| ≤ 1 / 4
      exact (EinsteinFull.abs_apply_le_euclideanNorm _ j).trans
        (EinsteinFull.Work.W8.corrector_gradient_bound W x)
    have hM := reduced_slln_squares hΛ (hreg W) hsmooth i lam hY hf hG
      (a := EinsteinFull.Work.W8.seedScale d) (b := 0)
      (fun x => by simpa only [zero_mul, add_zero] using EinsteinFull.Work.W8.corrector_abs_le W x)
      (EinsteinFull.Work.W8.seedScale_pos d).le (le_refl 0)
    obtain ⟨K, hK, hgen⟩ := sharp_generator_bounded i W lam
    filter_upwards [hM] with γ hγ
    let F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t,
      reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
        (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)
    have hcont : Continuous (fun u : ℝ =>
        reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
          (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) :=
      (continuous_reducedGenerator_apply hsmooth i lam hf).comp
        (γ.continuous.comp continuous_real_toNNReal)
    have hinc : ∀ s t : ℝ, 0 ≤ s → s ≤ t → |F t - F s| ≤ K * (t - s) := by
      intro s t _ hst
      dsimp only [F]
      rw [intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 t)
        (hcont.intervalIntegrable 0 s)]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := s) (b := t) (fun u _ => show ‖reducedGenerator i
          (EinsteinFull.Work.W8.physicalPair i W) lam (EinsteinFull.Work.W8.corrector W)
            (γ u.toNNReal)‖ ≤ K by rw [Real.norm_eq_abs]; exact hgen _)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] using hb
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have hψ : Tendsto (fun n : ℕ => EinsteinFull.Work.W8.corrector W
        (γ ((n : ℝ≥0) ^ 2)) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have hscale := hinv.const_mul (EinsteinFull.Work.W8.seedScale d)
      refine squeeze_zero_norm (fun n => ?_) (by simpa only [mul_zero] using hscale)
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ)), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (EinsteinFull.Work.W8.corrector_abs_le W _)
        (inv_nonneg.2 (sq_nonneg _))
    have hψ0 : Tendsto (fun n : ℕ => EinsteinFull.Work.W8.corrector W (γ 0) /
        (n : ℝ) ^ 2) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        hinv.const_mul (EinsteinFull.Work.W8.corrector W (γ 0))
    have hsquare : Tendsto (fun n : ℕ => F ((n : ℝ) ^ 2) / (n : ℝ) ^ 2)
        atTop (𝓝 0) := by
      have h := (hψ.sub hψ0).sub hγ
      simp only [sub_zero] at h
      refine h.congr fun n => ?_
      simp only [compensatedTest, NNReal.coe_pow, NNReal.coe_natCast, F]
      ring
    simpa only [div_eq_inv_mul] using average_zero_of_squares F hK hinc hsquare
end EinsteinFull.Blueprint
