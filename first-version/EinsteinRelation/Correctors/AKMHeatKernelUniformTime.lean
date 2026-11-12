import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A point outside the sup-norm ball of radius `R` around `y` has squared
Euclidean distance at least `R ^ 2` from `y`. -/
lemma akm_heatKernel_sq_le_euclideanSq_of_not_mem_closedBall {d : ℕ} (x y : Vec d)
    {R : ℝ} (hR : 0 ≤ R) (hx : x ∉ Metric.closedBall y R) :
    R ^ 2 ≤ euclideanSq (x - y) := by
  have hlt : R < ‖x - y‖ := by
    rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hx
    exact hx
  obtain ⟨i, hi⟩ : ∃ i, R < ‖(x - y) i‖ := by
    by_contra hcon
    push_neg at hcon
    exact (not_le.mpr hlt) ((pi_norm_le_iff_of_nonneg hR).mpr hcon)
  have hsum : (x - y) i * (x - y) i ≤ euclideanSq (x - y) := by
    unfold euclideanSq dot
    exact Finset.single_le_sum (f := fun j => (x - y) j * (x - y) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [Real.norm_eq_abs] at hi
  have hmul : R * R ≤ |(x - y) i| * |(x - y) i| :=
    mul_le_mul hi.le hi.le hR (abs_nonneg _)
  rw [abs_mul_abs_self] at hmul
  rw [sq]
  linarith

/-- Positive-time continuity is uniform in the free spatial variable, by
the Gaussian tail bound. Source: `paper/main.tex:787–792,850`; AKM (E.7). -/
theorem akm_heatKernel_uniform_time_continuity {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C)
    (T : ℝ) (hT : 0 < T) (y : Vec d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 T, ∀ x : Vec d,
      |P t x y - P T x y| < ε := by
  intro ε hε
  obtain ⟨α, hα, hαK⟩ : ∃ α : ℝ, 0 < α ∧ α < K⁻¹ :=
    ⟨K⁻¹ / 2, half_pos (inv_pos.mpr hK), half_lt_self (inv_pos.mpr hK)⟩
  have hb := h.2.2.2.2.2.2.2.1 α hα hαK
  have hC0 : 0 ≤ C α := by
    have hh := (hb 1 zero_lt_one 0 0).1
    simp only [Real.one_rpow, mul_one, sub_self, euclideanSq, dot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_div, Real.exp_zero] at hh
    exact (abs_nonneg _).trans hh
  have hF : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y) (Set.Ioi 0 ×ˢ Set.univ) :=
    h.1.comp ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨hz.1, Set.mem_univ _⟩)
  -- Tail: outside a fixed sup-ball the kernel is uniformly small near `T`.
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = α / (8 * T) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact div_pos hα (by linarith)
  have hT8 : (8 * T) ≠ 0 := (by linarith : (0 : ℝ) < 8 * T).ne'
  have hc8 : c * (8 * T) = α := by rw [hcdef]; field_simp
  have hct : ∀ t : ℝ, t < 2 * T → c * (4 * t) ≤ α := by
    intro t ht
    rw [← hc8]
    exact mul_le_mul_of_nonneg_left (by linarith) hc.le
  have htail : ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, T / 2 < t → t < 2 * T →
      ∀ x : Vec d, x ∉ Metric.closedBall y R → |P t x y| < ε / 2 := by
    have hlim : Tendsto (fun R : ℝ => C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)))
        atTop (𝓝 0) := by
      have hsq : Tendsto (fun R : ℝ => c * R ^ 2) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc (tendsto_pow_atTop two_ne_zero)
      have h0 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq).const_mul
        (C α * (T / 2) ^ (-(d : ℝ) / 2))
      rw [mul_zero] at h0
      exact h0
    obtain ⟨R, hR0, hRlt⟩ : ∃ R : ℝ, 0 ≤ R ∧
        C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)) < ε / 2 := by
      obtain ⟨R, hR⟩ := ((hlim.eventually (gt_mem_nhds (half_pos hε))).and
        (eventually_ge_atTop (0 : ℝ))).exists
      exact ⟨R, hR.2, hR.1⟩
    refine ⟨R, hR0, fun t ht1 ht2 x hx => ?_⟩
    have ht0 : 0 < t := by linarith
    have hq := akm_heatKernel_sq_le_euclideanSq_of_not_mem_closedBall x y hR0 hx
    have hpow : t ^ (-(d : ℝ) / 2) ≤ (T / 2) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (half_pos hT) ht1.le
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num))
    have hexp : Real.exp (-α * euclideanSq (x - y) / (4 * t)) ≤ Real.exp (-(c * R ^ 2)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * t)]
      nlinarith [mul_le_mul_of_nonneg_left (hct t ht2) (sq_nonneg R),
        mul_le_mul_of_nonneg_left hq hα.le]
    have hbound : |P t x y| ≤ C α * (T / 2) ^ (-(d : ℝ) / 2) * Real.exp (-(c * R ^ 2)) :=
      ((hb t ht0 x y).1).trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0) hexp
        (Real.exp_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (half_pos hT).le _)))
    exact lt_of_le_of_lt hbound hRlt
  -- Inside the sup-ball the slice is uniformly continuous on a compact set.
  obtain ⟨R, hR0, htail'⟩ := htail
  have hKc : IsCompact (Set.Icc (T / 2) (2 * T) ×ˢ Metric.closedBall y R) :=
    isCompact_Icc.prod (isCompact_closedBall y R)
  have hFc : ContinuousOn (fun z : ℝ × Vec d => P z.1 z.2 y)
      (Set.Icc (T / 2) (2 * T) ×ˢ Metric.closedBall y R) :=
    hF.mono fun z hz => ⟨lt_of_lt_of_le (half_pos hT) hz.1.1, Set.mem_univ _⟩
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hFc) ε hε
  filter_upwards [Ioo_mem_nhds (by linarith : T / 2 < T) (by linarith : T < 2 * T),
    Metric.ball_mem_nhds T hδ] with t ht1 ht2 x
  by_cases hx : x ∈ Metric.closedBall y R
  · have hdist : dist (t, x) (T, x) < δ := by
      rw [Prod.dist_eq]
      exact max_lt (Metric.mem_ball.mp ht2) (by simpa using hδ)
    have htI : t ∈ Set.Icc (T / 2) (2 * T) := ⟨ht1.1.le, ht1.2.le⟩
    have hTI : T ∈ Set.Icc (T / 2) (2 * T) := ⟨by linarith, by linarith⟩
    have hU := hδP (t, x) ⟨htI, hx⟩ (T, x) ⟨hTI, hx⟩ hdist
    rw [Real.dist_eq] at hU
    exact hU
  · have h1 := htail' t ht1.1 ht1.2 x hx
    have h2 := htail' T (by linarith) (by linarith) x hx
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
    rw [abs_lt]
    constructor <;> linarith

end EinsteinRelation.Correctors
